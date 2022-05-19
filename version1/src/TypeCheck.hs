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

-- | Infer the type of a term. The returned type is not guaranteed to be checkable(?)
inferType :: Term -> TcMonad Type
inferType t = tcTerm t Nothing

-- | Check that the given term has the expected type.
-- The provided type does not necessarily to be in whnf, but it should be
-- already checked to be a good type
checkType :: Term -> Type -> TcMonad Type
checkType tm expectedTy = do
  nf <- Equal.whnf expectedTy
  tcTerm tm (Just nf)
  
-- | Make sure that the term is a type (i.e. has type 'Type')
tcType :: Term -> TcMonad ()
tcType tm = (checkType tm Type) >> return ()
    
-- | check a term, producing an elaborated term
-- where all type annotations have been filled in.
-- The second argument is 'Nothing' in inference mode and
-- an expected type (in weak-head-normal form) in checking mode
tcTerm :: Term -> Maybe Type -> TcMonad Type
-- i-var
tcTerm t@(Var x) Nothing = do
  sig <- Env.lookupTy x 
  return (sigType sig)
-- i-type
tcTerm Type Nothing = return Type
-- i-pi
tcTerm (Pi bnd) Nothing = do
  ((x,  Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
  tcType tyA
  Env.extendCtx (Sig (S x  tyA)) $ tcType tyB
  return Type
-- c-lam: check the type of a function
tcTerm (Lam bnd) (Just (Pi bnd2)) = do
  -- unbind the variables in the lambda expression and pi type
  ( (x ),
    body,
    (_,  Unbound.unembed -> tyA),
    tyB
    ) <-
    Unbound.unbind2Plus bnd bnd2

  -- check the type of the body of the lambda expression
  etyB <- Env.extendCtx (Sig (S x  tyA)) (checkType body tyB)
  return (Pi bnd2)
   
tcTerm (Lam _) (Just nf) =
  Env.err [DS "Lambda expression should have a function type, not ", DD nf]

-- i-app
tcTerm (App t1 a2) Nothing = do
  ty1 <- inferType t1
  (x,  tyA, tyB) <- Equal.ensurePi ty1

  ty2 <-  checkType (unArg a2) tyA
  return (Unbound.subst x (Ann (unArg a2) tyA) tyB)

-- i-ann
tcTerm (Ann tm ty) Nothing = do
  ty' <- tcType ty
  checkType tm ty
  
-- practicalities
-- remember the current position in the type checking monad
tcTerm (Pos p tm) mTy =
  Env.extendSourceLocation p tm $ tcTerm tm mTy
-- ignore parentheses
tcTerm (Paren tm) mTy = tcTerm tm mTy
-- ignore term, just return type annotation
tcTerm t@(TrustMe) (Just ty) = return ty
  
tcTerm (TyUnit) Nothing = return Type
tcTerm (LitUnit) Nothing = return TyUnit

-- i-bool
tcTerm (TyBool) Nothing = Env.err [DS "unimplemented"]

-- i-true/false
tcTerm (LitBool b) Nothing = Env.err [DS "unimplemented"]

-- c-if
tcTerm t@(If t1 t2 t3) (Just ty) = Env.err [DS "unimplemented"]

tcTerm (Let bnd) ann =   Env.err [DS "unimplemented"]






tcTerm t@(Sigma bnd) Nothing = Env.err [DS "unimplemented"]

tcTerm t@(Prod a b) (Just ty) = Env.err [DS "unimplemented"]

tcTerm t@(LetPair p bnd) (Just ty) = Env.err [DS "unimplemented"]

tcTerm t@(PrintMe) (Just ty) = do
  gamma <- Env.getLocalCtx
  Env.warn [DS "Unmet obligation.\nContext: ", DD gamma,
        DS "\nGoal: ", DD ty]
  return ty

-- c-infer
tcTerm tm (Just ty) = do
  ty' <- inferType tm
  unless (Unbound.aeq ty' ty) $ Env.err [DS "Types don't match", DD ty, DS "and", DD ty']
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
          ty <- inferType term
          return $ AddCtx [Sig (S n  ty), Def n term]
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
                ety <-
                  Env.extendCtx (Sig sig) $ checkType term (sigType sig) `catchError` handler
                -- Put the elaborated version of term into the context.
                let esig = sig{sigType = ety}
                if (n `elem` Unbound.toListOf Unbound.fv term)
                  then return $ AddCtx [Sig esig, RecDef n term]
                  else return $ AddCtx [Sig esig, Def n term]
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
  tcType (sigType sig)
  return $ AddHint sig

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


