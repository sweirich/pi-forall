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

-- | Infer the type of a term, producing an annotated version of the
-- term (whose type can *always* be inferred).
inferType :: Term -> TcMonad (Term, Type)
inferType t = tcTerm t Nothing

-- | Check that the given term has the expected type.
-- The provided type does not necessarily need to be in whnf, but it should be
-- elaborated (i.e. already checked to be a good type).
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
  sig <- Env.lookupTy x 
  return (t, sigType sig)
tcTerm t@(Type) Nothing = return (t, Type)
tcTerm (Pi bnd) Nothing = do
  ((x,  Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
  atyA <- tcType tyA
  atyB <- Env.extendCtx (Sig (S x  atyA)) $ tcType tyB
  return (Pi (Unbound.bind (x,  Unbound.embed atyA) atyB), Type)

-- Check the type of a function
tcTerm (Lam bnd) (Just (Pi bnd2)) = do
  -- unbind the variables in the lambda expression and pi type
  ( (x,  Unbound.unembed -> Annot ma),
    body,
    (_,  Unbound.unembed -> tyA),
    tyB
    ) <-
    Unbound.unbind2Plus bnd bnd2

  -- check tyA matches type annotation on binder, if present
  maybe (return ()) (Equal.equate tyA) ma
  -- check the type of the body of the lambda expression
  (ebody, etyB) <- Env.extendCtx (Sig (S x  tyA)) (checkType body tyB)
  return
    ( Lam (Unbound.bind (x,  Unbound.embed (Annot (Just tyA))) ebody),
      Pi bnd2
    )
tcTerm (Lam _) (Just nf) =
  Env.err [DS "Lambda expression has a function type, not", DD nf]
-- infer the type of a lambda expression, when an annotation
-- on the binder is present
tcTerm (Lam bnd) Nothing = do
  ((x,  (Unbound.unembed -> Annot annot)), body) <- Unbound.unbind bnd
  tyA <- maybe (Env.err [DS "Must annotate lambda"]) return annot
  -- check that the type annotation is well-formed
  atyA <- tcType tyA
  -- infer the type of the body of the lambda expression
  (ebody, atyB) <- Env.extendCtx (Sig (S x  atyA)) (inferType body)
  return
    ( Lam (Unbound.bind (x,  Unbound.embed (Annot (Just atyA))) ebody),
      Pi (Unbound.bind (x,  Unbound.embed atyA) atyB)
    )
tcTerm (App t1 a2) Nothing = do
  (at1, ty1) <- inferType t1
  (x,  tyA, tyB) <- Equal.ensurePi ty1

  (at2, ty2) <-  checkType (unArg a2) tyA
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
tcTerm (TyBool) Nothing = Env.err [DS "unimplemented"]
tcTerm (LitBool b) Nothing = Env.err [DS "unimplemented"]

tcTerm t@(If t1 t2 t3 ann1) ann2 = Env.err [DS "unimplemented"]

tcTerm (Let bnd) ann =   Env.err [DS "unimplemented"]






tcTerm t@(Sigma bnd) Nothing = Env.err [DS "unimplemented"]

tcTerm t@(Prod a b ann1) ann2 = Env.err [DS "unimplemented"]

tcTerm t@(Pcase p bnd ann1) ann2 = Env.err [DS "unimplemented"]

tcTerm tm (Just ty) = do
  (atm, ty') <- inferType tm
  unless (Unbound.aeq ty' ty) $ Env.err [DS "Types don't match", DD ty, DS "and", DD ty']
  return (atm, ty)


---------------------------------------------------------------------
-- helper functions for type checking

-- | Merge together two sources of type information
-- The first annotation is assumed to come from an annotation on
-- the syntax of the term itself, the second as an argument to
-- 'checkType'.
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
-- And permit erased variables to be used
tcType :: Term -> TcMonad Term
tcType tm = do
  (atm, _) <- (checkType tm Type)
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
          return $ AddCtx [Sig (S n  ty), Def n aterm]
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


