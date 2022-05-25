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

import Text.PrettyPrint.HughesPJ (($$))

import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)


-- | Infer the type of a term. The returned type is not guaranteed to be checkable(?)
inferType :: Term -> TcMonad Type
inferType t = tcTerm t Nothing

-- | Check that the given term has the expected type.
-- The provided type does not necessarily to be in whnf, but it should be
-- already checked to be a good type
checkType :: Term -> Type -> TcMonad ()
checkType tm expectedTy = do
  nf <- Equal.whnf expectedTy
  void $ tcTerm tm (Just nf)

  
-- | Make sure that the term is a type (i.e. has type 'Type')
tcType :: Term -> TcMonad ()
tcType tm = void $ Env.withStage Irr $ checkType tm Type
    
-- | check a term, producing its type
-- The second argument is 'Nothing' in inference mode and
-- an expected type (in weak-head-normal form) in checking mode
tcTerm :: Term -> Maybe Type -> TcMonad Type
-- i-var
tcTerm t@(Var x) Nothing = do
  sig <- Env.lookupTy x   -- make sure the variable is accessible
  Env.checkStage (sigEp sig) 
  return (sigType sig)
-- i-type
tcTerm Type Nothing = return Type
-- i-pi
tcTerm (Pi bnd) Nothing = do
  ((x, {- SOLN EP -}ep,{- STUBWITH -} Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
  tcType tyA
  Env.extendCtx (TypeSig (Sig x ep  tyA)) $ tcType tyB
  return Type
-- c-lam: check the type of a function
tcTerm (Lam bnd) (Just (Pi bnd2)) = do
  -- unbind the variables in the lambda expression and pi type
  ( (x {- SOLN EP -}, ep1 {- STUBWITH -}),
    body,
    (_, ep2,  Unbound.unembed -> tyA),
    tyB
    ) <-
    Unbound.unbind2Plus bnd bnd2
-- epsilons should match up
  guard (ep1 == ep2) 
  -- check the type of the body of the lambda expression
  etyB <- Env.extendCtx (TypeSig (Sig x ep1  tyA)) (checkType body tyB)
  return (Pi bnd2)
   
tcTerm (Lam _) (Just nf) =
  Env.err [DS "Lambda expression should have a function type, not ", DD nf]

-- i-app
tcTerm (App t1 a2) Nothing = do
  ty1 <- inferType t1
  (x, ep2,  tyA, tyB) <- Equal.ensurePi ty1
  guard (argEp a2 == ep2) 
  ty2 <- {- SOLN EP -}Env.withStage (argEp a2) ${- STUBWITH -} checkType (unArg a2) tyA
  -- NOTE: we're replacing an inferrable variable with a 
  -- a checkable term. So the result will not necessarily 
  -- be checkable as a type.
  return (Unbound.subst x (unArg a2) tyB)

-- i-ann
tcTerm (Ann tm ty) Nothing = do
  tcType ty
  checkType tm ty
  return ty
  
-- practicalities
-- remember the current position in the type checking monad
tcTerm (Pos p tm) mTy =
  Env.extendSourceLocation p tm $ tcTerm tm mTy
-- ignore term, just return type annotation
tcTerm TrustMe (Just ty) = return ty
  
tcTerm TyUnit Nothing = return Type
tcTerm LitUnit Nothing = return TyUnit

-- i-bool
tcTerm TyBool Nothing = return Type


-- i-true/false
tcTerm (LitBool b) Nothing = do
  return TyBool


-- c-if
tcTerm t@(If t1 t2 t3) (Just ty) = do
  checkType t1 TyBool
  dtrue <- def t1 (LitBool True)
  dfalse <- def t1 (LitBool False)
  Env.extendCtxs dtrue $ checkType t2 ty
  Env.extendCtxs dfalse $ checkType t3 ty
  return ty


tcTerm (Let bnd) ann = do
  ((x, Unbound.unembed -> rhs), body) <- Unbound.unbind bnd
  aty <- inferType rhs 
  let sig = mkSig x aty
  ty <- Env.extendCtxs [TypeSig sig, Def x rhs] $
      tcTerm body ann
  when (x `elem` Unbound.toListOf Unbound.fv ty) $
    Env.err [DS "Let bound variable", DD x, DS "escapes in type", DD ty]
  return ty



tcTerm (TyEq a b) Nothing = do
  aTy <- inferType a
  bTy <- checkType b aTy
  return Type
tcTerm Refl (Just ty@(TyEq a b)) = do
  Equal.equate a b
  return ty
tcTerm Refl (Just ty) = 
  Env.err [DS "Refl annotated with ", DD ty]
tcTerm t@(Subst a b) (Just ty) = do
  -- infer the type of the proof 'b'
  tp <- inferType b
  -- make sure that it is an equality between m and n
  (m, n) <- Equal.ensureTyEq tp
  -- if either side is a variable, add a definition to the context
  edecl <- def m n
  -- if proof is a variable, add a definition to the context
  pdecl <- def b Refl
  _ <- Env.extendCtxs (edecl ++ pdecl) $ checkType a ty
  return ty
tcTerm t@(Contra p) (Just ty) = do
  ty' <- inferType p
  (a, b) <- Equal.ensureTyEq ty'
  a' <- Equal.whnf a
  b' <- Equal.whnf b
  case (a', b') of
    

    (LitBool b1, LitBool b2)
      | b1 /= b2 ->
        return ty
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
  tcType tyA
  Env.extendCtx (TypeSig (mkSig x tyA)) $ tcType tyB
  return Type


tcTerm t@(Prod a b) (Just ty) = do
  case ty of
    (Sigma bnd) -> do
      ((x, Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
      checkType a tyA
      Env.extendCtxs [TypeSig (mkSig x tyA), Def x a] $ checkType b tyB
      return (Sigma (Unbound.bind (x, Unbound.embed tyA) tyB))
    _ ->
      Env.err
        [ DS "Products must have Sigma Type",
          DD ty,
          DS "found instead"
        ]


tcTerm t@(LetPair p bnd) (Just ty) = do
  pty <- inferType p
  pty' <- Equal.whnf pty
  case pty' of
    Sigma bnd' -> do
      ((x, Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd'
      ((x', y'), body) <- Unbound.unbind bnd
      let tyB' = Unbound.subst x (Var x') tyB
      decl <- def p (Prod (Var x') (Var y'))
      Env.extendCtxs ([TypeSig (mkSig x' tyA), TypeSig (mkSig y' tyB')] ++ decl) $
          checkType body ty
      return ty
    _ -> Env.err [DS "Scrutinee of pcase must have Sigma type"]


tcTerm PrintMe (Just ty) = do
  gamma <- Env.getLocalCtx
  Env.warn [DS "Unmet obligation.\nContext: ", DD gamma,
        DS "\nGoal: ", DD ty]
  return ty

-- c-infer
tcTerm tm (Just ty) = do
  ty' <- inferType tm
  Equal.equate ty' ty

  return ty'

tcTerm tm Nothing = 
  Env.err [DS "Must have a type annotation to check ", DD tm]

---------------------------------------------------------------------
-- helper functions for type checking

-- | Create a Def if either side normalizes to a single variable
def :: Term -> Term -> TcMonad [Decl]
def t1 t2 = do
    nf1 <- Equal.whnf t1
    nf2 <- Equal.whnf t2
    case (nf1, nf2) of
      (Var x, _) -> return [Def x nf2]
      (_, Var x) -> return [Def x nf1]
      _ -> return []



--------------------------------------------------------
-- Using the typechecker for decls and modules and stuff
--------------------------------------------------------

-- | Typecheck a collection of modules. Assumes that each module
-- appears after its dependencies. Returns the same list of modules
-- with each definition typechecked
tcModules :: [Module] -> TcMonad [Module]
tcModules = foldM tcM []
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
        AddCtx decls -> (decls ++) <$> Env.extendCtxsGlobal decls m
    -- Get all of the defs from imported modules (this is the env to check current module in)
    importedModules = filter (\x -> ModuleImport (moduleName x) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Decl.
data HintOrCtx
  = AddHint Sig
  | AddCtx [Decl]

-- | Check each sort of declaration in a module
tcEntry :: Decl -> TcMonad HintOrCtx
tcEntry (Def n term) = do
  oldDef <- Env.lookupDef n
  maybe tc die oldDef
  where
    tc = do
      lkup <- Env.lookupHint n
      case lkup of
        Nothing -> do
          ty <- inferType term
          return $ AddCtx [TypeSig (Sig n {- SOLN EP -}Rel{- STUBWITH -} ty), Def n term]
        Just sig ->
          let handler (Env.Err ps msg) = throwError $ Env.Err ps (msg $$ msg')
              msg' =
                disp
                  [ 
                    DS "When checking the term ",
                    DD term,
                    DS "against the signature",
                    DD sig
                  ]
           in do
                Env.extendCtx (TypeSig sig) $ checkType term (sigType sig) `catchError` handler
                if n `elem` Unbound.toListOf Unbound.fv term
                  then return $ AddCtx [TypeSig sig, RecDef n term]
                  else return $ AddCtx [TypeSig sig, Def n term]
    die term' =
      Env.extendSourceLocation (unPosFlaky term) term $
        Env.err
          [ DS "Multiple definitions of",
            DD n,
            DS "Previous definition was",
            DD term'
          ]
tcEntry (TypeSig sig) = do
  duplicateTypeBindingCheck sig
  tcType (sigType sig)
  return $ AddHint sig
tcEntry (Demote ep) = return (AddCtx [Demote ep])


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


