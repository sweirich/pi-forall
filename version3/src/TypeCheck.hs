{- pi-forall -}

-- | The main routines for type-checking
{-# HLINT ignore "Use forM_" #-}
module TypeCheck (tcModules, inferType, checkType) where

import Control.Monad.Except

import Data.Maybe ( catMaybes )


import Environment (D (..), TcMonad)
import Environment qualified as Env
import Equal qualified
import PrettyPrint (Disp (disp), pp, debug)
import Syntax
import Debug.Trace

import Text.PrettyPrint.HughesPJ (($$), render)

import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound




---------------------------------------------------------------------

-- | Infer/synthesize the type of a term
inferType :: Term -> TcMonad Type
inferType t = case t of
  -- i-var
  (Var x) -> do
    decl <- Env.lookupTy x     -- make sure the variable is accessible
    Env.checkStage (declEp decl) 
    return (declType decl)

  -- i-type
  TyType -> return TyType

  -- i-pi
  (TyPi ep tyA bnd) -> do
    (x, tyB) <- Unbound.unbind bnd
    tcType tyA
    Env.extendCtx (Decl (TypeDecl x ep tyA)) (tcType tyB)
    return TyType

  -- i-app
  (App t1 t2) -> do
    ty1 <- inferType t1 
    let ensurePi = Equal.ensurePi 
    
    (ep1, tyA, bnd) <- ensurePi ty1
    unless (ep1 == argEp t2) $ Env.err 
      [DS "In application, expected", DD ep1, DS "argument but found", 
                                      DD t2, DS "instead." ]
    -- if the argument is Irrelevant, resurrect the context
    (if ep1 == Irr then Env.extendCtx (Demote Rel) else id) $ 
      checkType (unArg t2) tyA
    return (Unbound.instantiate bnd [unArg t2])
    

  -- i-ann
  (Ann tm ty) -> do
    tcType ty
    checkType tm ty
    return ty
  
  -- Practicalities
  -- remember the current position in the type checking monad
  (Pos p tm) ->
    Env.extendSourceLocation p tm $ inferType tm
  
  -- Extensions to the core language
  -- i-unit
  TyUnit -> return TyType
  LitUnit -> return TyUnit

  -- i-bool
  TyBool -> return TyType 

  -- i-true/false
  (LitBool b) -> return TyBool 

  -- i-if
  (If t1 t2 t3) -> do
      checkType t1 TyBool
      ty <- inferType t2
      checkType t3 ty
      return ty 
  -- i-eq
  (TyEq a b) -> do
    aTy <- inferType a
    checkType b aTy
    return TyType 

  -- i-sigma
  (TySigma tyA bnd) -> do
    (x, tyB) <- Unbound.unbind bnd
    tcType tyA
    Env.extendCtx (mkDecl x tyA) $ tcType tyB
    return TyType 



  -- cannot synthesize the type of the term
  tm -> 
    Env.err [DS "Must have a type for", DD tm] 


-------------------------------------------------------------------------

-- | Make sure that the term is a "type" (i.e. that it has type 'Type')
tcType :: Term -> TcMonad ()
tcType tm = Env.withStage Irr $  checkType tm TyType

-------------------------------------------------------------------------
-- | Check that the given term has the expected type
checkType :: Term -> Type -> TcMonad ()
checkType tm ty' = do
  ty <- Equal.whnf ty' 
  case tm of 
    -- c-lam: check the type of a function
    (Lam ep1  bnd) -> case ty of
      (TyPi ep2 tyA bnd2) -> do
        -- unbind the variables in the lambda expression and pi type
        (x, body,_,tyB) <- Unbound.unbind2Plus bnd bnd2
-- epsilons should match up
        unless (ep1 == ep2) $ Env.err [DS "In function definition, expected", DD ep2, DS "parameter", DD x, 
                                      DS "but found", DD ep1, DS "instead."] 
        -- check the type of the body of the lambda expression
        Env.extendCtx (Decl (TypeDecl x ep1 tyA)) (checkType body tyB)
      _ -> Env.err [DS "Lambda expression should have a function type, not", DD ty]

    -- Practicalities
    (Pos p tm) -> 
      Env.extendSourceLocation p tm $ checkType tm ty

    TrustMe -> return ()

    PrintMe -> do
      gamma <- Env.getLocalCtx
      Env.warn [DS "Unmet obligation.\nContext:", DD gamma,
            DS "\nGoal:", DD ty]  

    -- Extensions to the core language
    -- c-if
    (If t1 t2 t3) -> do
      checkType t1 TyBool
      dtrue <- Equal.unify [] t1 (LitBool True)
      dfalse <- Equal.unify [] t1 (LitBool False)
      Env.extendCtxs dtrue $ checkType t2 ty
      Env.extendCtxs dfalse $ checkType t3 ty 

    -- c-let
    (Let rhs bnd) -> do
      (x, body) <- Unbound.unbind bnd
      aty <- inferType rhs 
      Env.extendCtxs [mkDecl x aty, Def x rhs] $
          checkType body ty 

    -- c-refl
    Refl -> case ty of 
            (TyEq a b) -> Equal.equate a b
            _ -> Env.err [DS "Refl annotated with", DD ty]
    -- c-subst
    (Subst a b) -> do
      -- infer the type of the proof 'b'
      tp <- inferType b
      -- make sure that it is an equality between m and n
      (m, n) <- Equal.ensureTyEq tp
      -- if either side is a variable, add a definition to the context
      edecl <- Equal.unify [] m n
      -- if proof is a variable, add a definition to the context
      pdecl <- Equal.unify [] b Refl
      Env.extendCtxs (edecl ++ pdecl) $ checkType a ty
    -- c-contra 
    (Contra p) -> do
      ty' <- inferType p
      (a, b) <- Equal.ensureTyEq ty'
      a' <- Equal.whnf a
      b' <- Equal.whnf b
      case (a', b') of
        

        (LitBool b1, LitBool b2)
          | b1 /= b2 ->
            return ()
        (_, _) ->
          Env.err
            [ DS "I can't tell that",
              DD a,
              DS "and",
              DD b,
              DS "are contradictory"
            ]
    
    -- c-prod
    (Prod a b) -> do
      case ty of
        (TySigma tyA bnd) -> do
          (x, tyB) <- Unbound.unbind bnd
          checkType a tyA
          Env.extendCtxs [mkDecl x tyA, Def x a] $ checkType b tyB
        _ ->
          Env.err
            [ DS "Products must have Sigma Type",
              DD ty,
              DS "found instead"
            ]
    

    -- c-letpair
    (LetPair p bnd) -> do
      ((x, y), body) <- Unbound.unbind bnd
      pty <- inferType p
      pty' <- Equal.whnf pty
      case pty' of
        TySigma tyA bnd' -> do
          let tyB = Unbound.instantiate bnd' [Var x]
          decl <- Equal.unify [] p (Prod (Var x) (Var y))
          Env.extendCtxs ([mkDecl x tyA, mkDecl y tyB] ++ decl) $
              checkType body ty
        _ -> Env.err [DS "Scrutinee of LetPair must have Sigma type"]
    


    -- c-infer
    tm -> do
      ty' <- inferType tm
      Equal.equate ty' ty
    



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
  -- | List of already checked modules (including their entries).
  [Module] ->
  -- | Module to check.
  Module ->
  -- | The same module with all entries checked and elaborated.
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
      -- Extend the Env per the current Entry before checking
      -- subsequent entries.
      x <- tcEntry d
      case x of
        AddHint hint -> Env.extendHints hint m
        -- Add decls to the entries to be returned
        AddCtx decls -> (decls ++) <$> Env.extendCtxsGlobal decls m
    -- Get all of the defs from imported modules (this is the env to check current module in)
    importedModules = filter (\x -> ModuleImport (moduleName x) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Entry.
data HintOrCtx
  = AddHint TypeDecl
  | AddCtx [Entry]

-- | Check each sort of declaration in a module
tcEntry :: Entry -> TcMonad HintOrCtx
tcEntry (Def n term) = do
  oldDef <- Env.lookupDef n
  maybe tc die oldDef
  where
    tc = do
      lkup <- Env.lookupHint n
      case lkup of
        Nothing -> do
          ty <- inferType term
          return $ AddCtx [Decl (TypeDecl n Rel ty), Def n term]
        Just decl ->
          let handler (Env.Err ps msg) = throwError $ Env.Err ps (msg $$ msg')
              msg' =
                disp
                  [ 
                    DS "When checking the term",
                    DD term,
                    DS "against the type",
                    DD decl
                  ]
           in do
                Env.extendCtx (Decl decl) $ checkType term (declType decl) `catchError` handler
                return $ AddCtx [Decl decl, Def n term]
    die term' =
      Env.extendSourceLocation (unPosFlaky term) term $
        Env.err
          [ DS "Multiple definitions of",
            DD n,
            DS "Previous definition was",
            DD term'
          ]
tcEntry (Decl decl) = do
  duplicateTypeBindingCheck decl
  tcType (declType decl)
  return $ AddHint decl
tcEntry (Demote ep) = return (AddCtx [Demote ep])




-- | Make sure that we don't have the same name twice in the
-- environment. (We don't rename top-level module definitions.)
duplicateTypeBindingCheck :: TypeDecl -> TcMonad ()
duplicateTypeBindingCheck decl = do
  -- Look for existing type bindings ...
  let n = declName decl
  l <- Env.lookupTyMaybe n
  l' <- Env.lookupHint n
  -- ... we don't care which, if either are Just.
  case catMaybes [l, l'] of
    [] -> return ()
    -- We already have a type in the environment so fail.
    decl' : _ ->
      let p = unPosFlaky $ declType decl
          msg =
            [ DS "Duplicate type declaration",
              DD decl,
              DS "Previous was",
              DD decl'
            ]
       in Env.extendSourceLocation p decl $ Env.err msg


