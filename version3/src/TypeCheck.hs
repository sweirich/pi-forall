{- PiForall language -}

-- | The main routines for type-checking
module TypeCheck (tcModules, inferType, checkType) where

import Control.Monad.Except

import Data.Maybe ( catMaybes )


import Environment (D (..), TcMonad)
import Environment qualified as Env
import Equal qualified
import PrettyPrint (Disp (disp))
import Syntax
import Text.PrettyPrint.HughesPJ (($$),render)
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import Debug.Trace

-- | Infer the type of a term, producing an annotated version of the
-- term (whose type can *always* be inferred)
inferType :: Term -> TcMonad (Term, Type)
inferType t = tcTerm t Nothing

-- | Check that the given term has the expected type.
-- The provided type does not necessarily need to be in whnf, but it should be
-- elaborated (i.e. already checked to be a good type)
checkType :: Term -> Type -> TcMonad (Term, Type)
checkType tm expectedTy = do
  nf <- Equal.whnf expectedTy
  tcTerm tm (Just nf)

-- | check a term, producing an elaborated term
-- where all type annotations have been filled in.
-- The second argument is 'Nothing' in inference mode and
-- an expected type (in weak-head-normal form) in checking mode
tcTerm :: Term -> Maybe Type -> TcMonad (Term, Type)
tcTerm t@(Var x) Nothing = do
  sig <- Env.lookupTy x   -- make sure the variable is accessible
  Env.checkStage (sigEp sig) 
  return (t, sigType sig)
tcTerm t@(Type) Nothing = return (t, Type)
tcTerm (Pi bnd) Nothing = do
  ((x, {- SOLN EP -}ep,{- STUBWITH -} Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
  atyA <- tcType tyA
  atyB <- Env.extendCtx (Sig (S x ep  atyA)) $ tcType tyB
  return (Pi (Unbound.bind (x, ep,  Unbound.embed atyA) atyB), Type)

-- Check the type of a function
tcTerm (Lam bnd) (Just (Pi bnd2)) = do
  -- unbind the variables in the lambda expression and pi type
  ( (x, ep1,  Unbound.unembed -> Annot ma),
    body,
    (_, ep2,  Unbound.unembed -> tyA),
    tyB
    ) <-
    Unbound.unbind2Plus bnd bnd2
-- epsilons should match up
  guard (ep1 == ep2) 
  -- check tyA matches type annotation on binder, if present
  maybe (return ()) (Equal.equate tyA) ma
  -- check the type of the body of the lambda expression
  (ebody, etyB) <- Env.extendCtx (Sig (S x ep1  tyA)) (checkType body tyB)
  return
    ( Lam (Unbound.bind (x, ep1,  Unbound.embed (Annot (Just tyA))) ebody),
      Pi bnd2
    )
tcTerm (Lam _) (Just nf) =
  Env.err [DS "Lambda expression should have a function type, not", DD nf]
-- infer the type of a lambda expression, when an annotation
-- on the binder is present
tcTerm (Lam bnd) Nothing = do
  ((x, {- SOLN EP -}ep,{- STUBWITH -} (Unbound.unembed -> Annot annot)), body) <- Unbound.unbind bnd
  tyA <- maybe (Env.err [DS "Must annotate lambda"]) return annot
  -- check that the type annotation is well-formed
  atyA <- tcType tyA
  -- infer the type of the body of the lambda expression
  (ebody, atyB) <- Env.extendCtx (Sig (S x ep  atyA)) (inferType body)
  return
    ( Lam (Unbound.bind (x, ep,  Unbound.embed (Annot (Just atyA))) ebody),
      Pi (Unbound.bind (x, ep,  Unbound.embed atyA) atyB)
    )
tcTerm (App t1 a2) Nothing = do
  (at1, ty1) <- inferType t1
  (x, ep2,  tyA, tyB) <- Equal.ensurePi ty1
  guard (argEp a2 == ep2) 
  (at2, ty2) <- {- SOLN EP -}Env.withStage (argEp a2) ${- STUBWITH -} checkType (unArg a2) tyA
  let result = (App at1 a2{unArg=at2}, Unbound.subst x at2 tyB)
  return result
tcTerm (Ann tm ty) Nothing = do
  ty' <- tcType ty
  (tm', ty'') <- checkType tm ty'
  return (tm', ty'')
tcTerm (Pos p tm) mTy =
  Env.extendSourceLocation p tm $ tcTerm tm mTy
tcTerm (Paren tm) mTy = tcTerm tm mTy
tcTerm t@(TrustMe ann1) ann2 = do
  expectedTy <- matchAnnots t ann1 ann2
  return (TrustMe (Annot (Just expectedTy)), expectedTy)
tcTerm (TyUnit) Nothing = return (TyUnit, Type)
tcTerm (LitUnit) Nothing = return (LitUnit, TyUnit)
tcTerm (TyBool) Nothing = return (TyBool, Type)

tcTerm (LitBool b) Nothing = do
  return (LitBool b, TyBool)


tcTerm t@(If t1 t2 t3 ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2
  (at1, _) <- checkType t1 TyBool
  nf <- Equal.whnf at1
  let ctx b = case nf of
        Var x -> [Def x (LitBool b)]
        _ -> []
  (at2, _) <- Env.extendCtxs (ctx True) $ checkType t2 ty
  (at3, _) <- Env.extendCtxs (ctx False) $ checkType t3 ty
  return (If at1 at2 at3 (Annot (Just ty)), ty)


tcTerm (Let bnd) ann = do
  ((x, Unbound.unembed -> rhs), body) <- Unbound.unbind bnd
  (arhs, aty) <- inferType rhs 
  let sig = mkSig x aty
  (abody, ty) <- Env.extendCtxs [Sig sig, Def x arhs] $
      tcTerm body ann
  when (x `elem` Unbound.toListOf Unbound.fv ty) $
    Env.err [DS "Let bound variable", DD x, DS "escapes in type", DD ty]
  return (Let (Unbound.bind (x, Unbound.embed arhs) abody), ty)



tcTerm (TyEq a b) Nothing = do
  (aa, aTy) <- inferType a
  (ab, bTy) <- checkType b aTy
  return (TyEq aa ab, Type)
tcTerm t@(Refl ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2
  case ty of
    (TyEq a b) -> do
      Equal.equate a b
      return (Refl (Annot (Just ty)), ty)
    _ -> Env.err [DS "refl annotated with", DD ty]
tcTerm t@(Subst tm p ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2
  -- infer the type of the proof p
  (apf, tp) <- inferType p
  -- make sure that it is an equality between m and n
  (m, n) <- Equal.ensureTyEq tp
  -- if either side is a variable, add a definition to the context
  edecl <- do
    m' <- Equal.whnf m
    n' <- Equal.whnf n
    case (m', n') of
      (Var x, _) -> return [Def x n']
      (_, Var y) -> return [Def y m']
      (_, _) -> return []

  pdecl <- do
    p' <- Equal.whnf apf
    case p' of
      (Var x) -> return [Def x (Refl (Annot (Just tp)))]
      _ -> return []
  let refined = Env.extendCtxs (edecl ++ pdecl)
  (atm, _) <- refined $ checkType tm ty
  return (Subst atm apf (Annot (Just ty)), ty)
tcTerm t@(Contra p ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2
  (apf, ty') <- inferType p
  (a, b) <- Equal.ensureTyEq ty'
  a' <- Equal.whnf a
  b' <- Equal.whnf b
  case (a', b') of
    

    (LitBool b1, LitBool b2)
      | b1 /= b2 ->
        return (Contra apf (Annot (Just ty)), ty)
    (_, _) ->
      Env.err
        [ DS "I can't tell that",
          DD a,
          DS "and",
          DD b,
          DS "are contradictory"
        ]


tcTerm t@(Sigma bnd) Nothing = do
  ((x, Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
  aa <- tcType tyA
  ba <- Env.extendCtx (Sig (mkSig x aa)) $ tcType tyB
  return (Sigma (Unbound.bind (x, Unbound.embed aa) ba), Type)


tcTerm t@(Prod a b ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2
  case ty of
    (Sigma bnd) -> do
      ((x, Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
      (aa, _) <- checkType a tyA
      (ba, _) <- Env.extendCtxs [Sig (mkSig x tyA), Def x aa] $ checkType b tyB
      return (Prod aa ba (Annot (Just ty)), ty)
    _ ->
      Env.err
        [ DS "Products must have Sigma Type",
          DD ty,
          DS "found instead"
        ]


tcTerm t@(LetPair p bnd ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2
  (apr, pty) <- inferType p
  pty' <- Equal.whnf pty
  case pty' of
    Sigma bnd' -> do
      ((x, Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd'
      ((x', y'), body) <- Unbound.unbind bnd
      let tyB' = Unbound.subst x (Var x') tyB
      nfp <- Equal.whnf apr
      let ctx = case nfp of
            Var x0 ->
              [ Def
                  x0
                  ( Prod
                      (Var x')
                      (Var y')
                      (Annot (Just pty'))
                  )
              ]
            _ -> []
      (abody, bTy) <-
        Env.extendCtxs ([Sig (mkSig x' tyA), Sig (mkSig y' tyB')] ++ ctx) $
          checkType body ty
      return (LetPair apr (Unbound.bind (x', y') abody) (Annot (Just ty)), bTy)
    _ -> Env.err [DS "Scrutinee of pcase must have Sigma type"]


tcTerm t@(PrintMe ann1) ann2 = do
  expectedTy <- matchAnnots t ann1 ann2
  gamma <- Env.getLocalCtx
  Env.warn [DS "Unmet obligation.\nContext: ", DD gamma,
        DS "\nGoal: ", DD expectedTy]
  return (PrintMe (Annot (Just expectedTy)), expectedTy)

tcTerm tm (Just ty) = do
  (atm, ty') <- inferType tm
  Equal.equate ty' ty

  return (atm, ty)


---------------------------------------------------------------------
-- helper functions for type checking

-- | Merge together two sources of type information
-- The first annotation is assumed to come from an annotation on
-- the syntax of the term itself, the second as an argument to
-- 'checkType'
matchAnnots :: Term -> Annot -> Maybe Type -> TcMonad Type
matchAnnots e (Annot Nothing) Nothing =
  Env.err
    [DD e, DS "requires annotation"]
matchAnnots e (Annot Nothing) (Just t) = return t
matchAnnots e (Annot (Just t)) Nothing = do
  at <- tcType t
  return at
matchAnnots e (Annot (Just t1)) (Just t2) = do
  at1 <- tcType t1
  Equal.equate at1 t2
  return at1

-- | Make sure that the term is a type (i.e. has type 'Type')
tcType :: Term -> TcMonad Term
tcType tm = do
  (atm, _) <- Env.withStage Erased (checkType tm Type)
  return atm



--------------------------------------------------------
-- Using the typechecker for decls and modules and stuff
--------------------------------------------------------

-- | Typecheck a collection of modules. Assumes that each module
-- appears after its dependencies. Returns the same list of modules
-- with each definition typechecked
tcModules :: [Module] -> TcMonad [Module]
tcModules mods = foldM tcM [] mods
  where
    -- Check module m against modules in defs, then add m to the list.
    defs `tcM` m = do
      -- "M" is for "Module" not "monad"
      let name = moduleName m
      liftIO $ putStrLn $ "Checking module " ++ show name
      m' <- defs `tcModule` m
      return $ defs ++ [m']

-- | Typecheck an entire module.
tcModule ::
  -- | List of already checked modules (including their Decls).
  [Module] ->
  -- | Module to check.
  Module ->
  -- | The same module with all Decls checked and elaborated.
  TcMonad Module
tcModule defs m' = do
  checkedEntries <-
    Env.extendCtxMods importedModules $
      foldr
        tcE
        (return [])
        (moduleEntries m')
  return $ m' {moduleEntries = checkedEntries}
  where
    d `tcE` m = do
      -- Extend the Env per the current Decl before checking
      -- subsequent Decls.
      x <- tcEntry d
      case x of
        AddHint hint -> Env.extendHints hint m
        -- Add decls to the Decls to be returned
        AddCtx decls -> (decls ++) <$> (Env.extendCtxsGlobal decls m)
    -- Get all of the defs from imported modules (this is the env to check current module in)
    importedModules = filter (\x -> (ModuleImport (moduleName x)) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Decl.
data HintOrCtx
  = AddHint Sig
  | AddCtx [Decl]

-- | Check each sort of declaration in a module
tcEntry :: Decl -> TcMonad HintOrCtx
tcEntry (Def n term) = do
  oldDef <- Env.lookupDef n
  case oldDef of
    Nothing -> tc
    Just term' -> die term'
  where
    tc = do
      lkup <- Env.lookupHint n
      case lkup of
        Nothing -> do
          (aterm, ty) <- inferType term
          return $ AddCtx [Sig (S n {- SOLN EP -}Runtime{- STUBWITH -} ty), Def n aterm]
        Just sig ->
          let handler (Env.Err ps msg) = throwError $ Env.Err ps (msg $$ msg')
              msg' =
                disp
                  [ DS "When checking the term ",
                    DD term,
                    DS "against the signature",
                    DD sig
                  ]
           in do
                (eterm, ety) <-
                  Env.extendCtx (Sig sig) $ checkType term (sigType sig) `catchError` handler
                -- Put the elaborated version of term into the context.
                let esig = sig{sigType = ety}
                if (n `elem` Unbound.toListOf Unbound.fv eterm)
                  then return $ AddCtx [Sig esig, RecDef n eterm]
                  else return $ AddCtx [Sig esig, Def n eterm]
    die term' =
      Env.extendSourceLocation (unPosFlaky term) term $
        Env.err
          [ DS "Multiple definitions of",
            DD n,
            DS "Previous definition was",
            DD term'
          ]
tcEntry (Sig sig) = do
  duplicateTypeBindingCheck sig
  ety <- tcType (sigType sig)
  return $ AddHint (sig{sigType=ety})

tcEntry _ = Env.err "unimplemented"

-- | Make sure that we don't have the same name twice in the
-- environment. (We don't rename top-level module definitions.)
duplicateTypeBindingCheck :: Sig -> TcMonad ()
duplicateTypeBindingCheck sig = do
  -- Look for existing type bindings ...
  let n = sigName sig
  l <- Env.lookupTyMaybe n
  l' <- Env.lookupHint n
  -- ... we don't care which, if either are Just.
  case catMaybes [l, l'] of
    [] -> return ()
    -- We already have a type in the environment so fail.
    sig' : _ ->
      let (Pos p _) = sigType sig
          msg =
            [ DS "Duplicate type signature ",
              DD sig,
              DS "Previous was",
              DD sig'
            ]
       in Env.extendSourceLocation p sig $ Env.err msg


