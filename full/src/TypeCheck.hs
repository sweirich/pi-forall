{- pi-forall -}

-- | The main routines for type-checking
module TypeCheck (tcModules, inferType, checkType) where

import Control.Monad.Except
import Data.List (nub)

import Data.Maybe ( catMaybes )


import Environment (D (..), TcMonad)
import Environment qualified as Env
import Equal qualified
import PrettyPrint (Disp (disp))
import Syntax
import Debug.Trace

import Text.PrettyPrint.HughesPJ (($$), render)

import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)


-- | Infer/synthesize the type of a term
inferType :: Term -> Int -> TcMonad Type
inferType t k = tcTerm t Nothing k

-- | Check that the given term has the expected type
checkType :: Term -> Type -> Int -> TcMonad ()
checkType tm (Pos _ ty) k = checkType tm ty k  -- ignore source positions/annotations
checkType tm (Ann ty _) k = checkType tm ty k
checkType tm ty k = do
  nf <- Equal.whnf ty
  void $ tcTerm tm (Just nf) k



-- | Make sure that the term is a "type" (i.e. that it has type 'Type')
tcType :: Term -> Int -> TcMonad ()
tcType tm k = void $ Env.withStage Irr $ checkType tm Type k

---------------------------------------------------------------------

-- | Combined type checking/inference function
-- The second argument is 'Just expectedType' in checking mode and 'Nothing' in inference mode
-- In either case, this function returns the type of the term
tcTerm :: Term -> Maybe Type -> Int -> TcMonad Type
-- i-var
tcTerm t@(Var x) Nothing k = do
  sig <- Env.lookupTy x   -- make sure the variable is accessible
  Env.checkStage (rho (sigEp sig))
  return (sigType sig)
-- i-type
tcTerm Type Nothing k = return Type
-- i-pi
tcTerm (Pi (Mode ep (Dep j)) tyA bnd) Nothing k = do
  unless (j < k) $ Env.err [DS "level of Pi-quantification must be less than ", DD k]
  (x, tyB) <- Unbound.unbind bnd
  tcType tyA j
  Env.extendCtx (TypeSig (Sig x (Mode ep (Dep j)) tyA)) (tcType tyB k)
  return Type
-- i-arrow
tcTerm (Pi (Mode ep NonDep) tyA bnd) Nothing k = do
  (x, tyB) <- Unbound.unbind bnd
  tcType tyA k
  tcType tyB k   -- x can't appear in B
  return Type
-- c-lam: check the type of a function
tcTerm (Lam ep1  bnd) (Just (Pi (Mode ep2 lvl) tyA bnd2)) k = do
  -- unbind the variables in the lambda expression and pi type
  (x, body,_,tyB) <- Unbound.unbind2Plus bnd bnd2
-- epsilons should match up
  unless (ep1 == ep2) $ Env.err [DS "In function definition, expected", DD ep2, DS "parameter", DD x, 
                                 DS "but found", DD ep1, DS "instead."] 
  -- check the type of the body of the lambda expression
  Env.extendCtx (TypeSig (Sig x (Mode ep1 lvl) tyA)) (checkType body tyB k)
  return (Pi (Mode ep1 lvl) tyA bnd2)
tcTerm (Lam _ _) (Just nf) k =
  Env.err [DS "Lambda expression should have a function type, not", DD nf]
-- i-app
tcTerm (App t1 t2) Nothing k = do
  ty1 <- inferType t1 k
  let ensurePi = Equal.ensurePi 
  
  (Mode ep1 lvl, tyA, bnd) <- ensurePi ty1
  unless (ep1 == argEp t2) $ Env.err 
    [DS "In application, expected", DD ep1, DS "argument but found", 
                                    DD t2, DS "instead." ]
  -- if the argument is Irrelevant, resurrect the context
  let argLvl = case lvl of { NonDep -> k ; Dep j -> j }
  (if ep1 == Irr then Env.extendCtx (Demote Rel) else id) $ 
    checkType (unArg t2) tyA argLvl
  return (Unbound.instantiate bnd [unArg t2])
  

-- i-ann
tcTerm (Ann tm ty) Nothing k = do
  tcType ty k
  checkType tm ty k
  return ty
  
-- practicalities
-- remember the current position in the type checking monad
tcTerm (Pos p tm) mTy k =
  Env.extendSourceLocation p tm $ tcTerm tm mTy k
-- ignore term, just return type annotation
tcTerm TrustMe (Just ty) k = return ty
  
-- i-unit
tcTerm TyUnit Nothing k = return Type
tcTerm LitUnit Nothing k = return TyUnit

-- i-bool
tcTerm TyBool Nothing k = return Type


-- i-true/false
tcTerm (LitBool b) Nothing k = do
  return TyBool


-- c-if
tcTerm t@(If t1 t2 t3) mty k = do
  case mty of 
    Just ty -> do
      checkType t1 TyBool k
      dtrue <- def t1 (LitBool True)
      dfalse <- def t1 (LitBool False)
      Env.extendCtxs dtrue $ checkType t2 ty k
      Env.extendCtxs dfalse $ checkType t3 ty k
      return ty
    Nothing -> do
      checkType t1 TyBool k
      ty <- inferType t2 k
      checkType t3 ty k
      return ty


tcTerm (Let rhs bnd) mty k = do
  (x, body) <- Unbound.unbind bnd
  aty <- inferType rhs k
  ty <- Env.extendCtxs [mkSig x aty (Dep k), Def x rhs] $
      tcTerm body mty k
  case mty of 
    Just _ -> return ty
    Nothing -> return $ Unbound.subst x rhs ty

-- Type constructor application
tcTerm (TCon c params) Nothing k = do
  (Telescope delta, _, j) <- Env.lookupTCon c
  unless (j <= k) $ Env.err [DS "level too low for use of type constructor ", DD c]
  unless (length params == length delta) $
    Env.err
      [ DS "Datatype constructor",
        DD c,
        DS $
          "should have " ++ show (length delta)
            ++ "parameters, but was given",
        DD (length params)
      ]
  tcArgTele params delta k
  return Type

-- Data constructor application
-- we don't know the expected type, so see if there
-- is only one datacon of that name that takes no
-- parameters
tcTerm t@(DCon c args) Nothing k = do
  matches <- Env.lookupDConAll c
  case matches of
    [(tname, (Telescope [], ConstructorDef _ _ (Telescope deltai),j))] -> do
      unless (j <= k) $ Env.err [DS "level too low for data con c ", DS c]
      let numArgs = length deltai
      unless (length args == numArgs) $
        Env.err
          [ DS "Constructor",
            DS c,
            DS "should have",
            DD numArgs,
            DS "data arguments, but was given",
            DD (length args),
            DS "arguments."
          ]
      tcArgTele args deltai k
      return $ TCon tname []
      
    [_] ->
      Env.err
        [ DS "Cannot infer the parameters to data constructors.",
          DS "Add an annotation."
        ]
    _ -> Env.err [DS "Ambiguous data constructor", DS c]

-- we know the expected type of the data constructor
-- so look up its type in the context
tcTerm t@(DCon c args) (Just ty) k = do
  case ty of
    (TCon tname params) -> do
      (Telescope delta, Telescope deltai, j) <- Env.lookupDCon c tname
      unless (j <= k) $ Env.err [DS "level to low for use of datacon ", DD c]
      let isTypeSig :: Decl -> Bool
          isTypeSig (TypeSig _) = True
          isTypeSig _ = False
      let numArgs = length (filter isTypeSig deltai)
      unless (length args == numArgs) $
        Env.err
          [ DS "Constructor",
            DS c,
            DS "should have",
            DD numArgs,
            DS "data arguments, but was given",
            DD (length args),
            DS "arguments."
          ]
      newTele <- substTele delta params deltai
      tcArgTele args newTele k
      return ty
    _ ->
      Env.err [DS "Unexpected type", DD ty, DS "for data constructor", DD t]

-- Must have an annotation for Case
tcTerm t@(Case scrut alts) (Just ty) k = do
  sty <- inferType scrut k
  scrut' <- Equal.whnf scrut
  (c, args) <- Equal.ensureTCon sty
  let checkAlt (Match bnd) = do
        (pat, body) <- Unbound.unbind bnd
        -- add variables from pattern to context
        -- could fail if branch is in-accessible
        decls <- declarePat pat (Mode Rel (Dep k)) (TCon c args)
        -- add defs to the contents from scrut = pat
        -- could fail if branch is in-accessible
        decls' <- Equal.unify [] scrut' (pat2Term pat)
        Env.extendCtxs (decls ++ decls') $ checkType body ty k
        
        return ()
  let pats = map (\(Match bnd) -> fst (unsafeUnbind bnd)) alts
  mapM_ checkAlt alts
  exhaustivityCheck scrut' sty pats
  return ty

tcTerm (TyEq a b) Nothing k = do
  aTy <- inferType a k
  checkType b aTy k
  return Type
tcTerm Refl (Just ty@(TyEq a b)) k = do
  Equal.equate a b
  return ty
tcTerm Refl (Just ty) k = 
  Env.err [DS "Refl annotated with", DD ty]
tcTerm t@(Subst a b) (Just ty) k = do
  -- infer the type of the proof 'b'
  tp <- inferType b k
  -- make sure that it is an equality between m and n
  (m, n) <- Equal.ensureTyEq tp
  -- if either side is a variable, add a definition to the context
  edecl <- def m n
  -- if proof is a variable, add a definition to the context
  pdecl <- def b Refl
  _ <- Env.extendCtxs (edecl ++ pdecl) $ checkType a ty k
  return ty
tcTerm t@(Contra p) (Just ty) k = do
  ty' <- inferType p k
  (a, b) <- Equal.ensureTyEq ty'
  a' <- Equal.whnf a
  b' <- Equal.whnf b
  case (a', b') of
    
    (DCon da _, DCon db _)
      | da /= db ->
        return ty
    
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


tcTerm t@(Sigma tyA (Dep j) bnd) Nothing k = do
  (x, tyB) <- Unbound.unbind bnd
  tcType tyA j
  Env.extendCtx (mkSig x tyA (Dep j)) $ tcType tyB k
  return Type
tcTerm t@(Sigma tyA NonDep bnd) Nothing k = do
  (x, tyB) <- Unbound.unbind bnd
  tcType tyA k
  tcType tyB k
  return Type


tcTerm t@(Prod a b) (Just ty) k = do
  case ty of
    (Sigma tyA (Dep j) bnd) -> do
      (x, tyB) <- Unbound.unbind bnd
      checkType a tyA j
      Env.extendCtxs [mkSig x tyA (Dep j), Def x a] $ checkType b tyB k
      return (Sigma tyA (Dep j) (Unbound.bind x tyB))
    (Sigma tyA NonDep bnd) -> do
      (x, tyB) <- Unbound.unbind bnd
      checkType a tyA k
      checkType b tyB k
      return (Sigma tyA NonDep (Unbound.bind x tyB))
    _ ->
      Env.err
        [ DS "Products must have Sigma Type",
          DD ty,
          DS "found instead"
        ]


tcTerm t@(LetPair p bnd) (Just ty) k = do
  ((x, y), body) <- Unbound.unbind bnd
  pty <- inferType p k
  pty' <- Equal.whnf pty
  case pty' of
    Sigma tyA (Dep j) bnd' -> do
      let tyB = Unbound.instantiate bnd' [Var x]
      decl <- def p (Prod (Var x) (Var y))
      Env.extendCtxs ([mkSig x tyA (Dep j), mkSig y tyB (Dep k)] ++ decl) $
          checkType body ty k
      return ty
    Sigma tyA NonDep bnd' -> do
      let tyB = Unbound.instantiate bnd' [Var x]
      decl <- def p (Prod (Var x) (Var y))
      Env.extendCtxs ([mkSig x tyA (Dep k), mkSig y tyB (Dep k)] ++ decl) $
          checkType body ty k
      return ty
    _ -> Env.err [DS "Scrutinee of LetPair must have Sigma type"]


tcTerm PrintMe (Just ty) k = do
  gamma <- Env.getLocalCtx
  Env.warn [DS "Unmet obligation.\nContext:", DD gamma,
        DS "\nGoal:", DD ty]
  return ty

tcTerm (Displace t j) Nothing k = do
  case t of 
    (Pos _ (Var x)) -> do
      unless (j <= k) $ Env.err [DD "cannot displace more than the context", DD k]
      sig <- Env.lookupTy x   -- make sure the variable is accessible
      Env.checkStage (rho (sigEp sig))
      return (displace j (sigType sig))
    u -> 
      Env.err [DS "Found displacement", DD (show t)]

-- c-infer
tcTerm tm (Just ty) k = do
  ty' <- inferType tm k
  Equal.equate ty' ty
  return ty'

tcTerm tm Nothing k = 
  Env.err [DS "Must have a type annotation to check", DD tm]

---------------------------------------------------------------------
-- helper functions for type checking

-- | Create a Def if either side normalizes to a single variable
def :: Term -> Term -> TcMonad [Decl]
def t1 t2 = do
    nf1 <- Equal.whnf t1
    nf2 <- Equal.whnf t2
    case (nf1, nf2) of
      (Var x, Var y) | x == y -> return []
      (Var x, _) -> return [Def x nf2]
      (_, Var x) -> return [Def x nf1]
      _ -> return []


---------------------------------------------------------------------
-- helper functions for datatypes

-- | type check a list of data constructor arguments against a telescope
tcArgTele :: [Arg] -> [Decl] -> Int -> TcMonad ()
tcArgTele [] [] k = return ()
tcArgTele args (Def x ty : tele) k = do
  tele' <- doSubst [(x,ty)] tele
  tcArgTele args tele' k
tcArgTele (Arg ep1 tm : terms) (TypeSig (Sig x (Mode ep2 l) ty) : tele) k 
  | ep1 == ep2 = do
      let tmk = case l of Dep j -> j ; NonDep -> k
      Env.withStage ep1 $ checkType tm ty tmk
      tele' <- doSubst [(x, tm)] tele
      tcArgTele terms tele' k
  | otherwise =
  Env.err
    [ DD ep1,
      DS "argument provided when",
      DD ep2,
      DS "argument was expected"
    ]
tcArgTele [] _ k =
  Env.err [DD "Too few arguments provided."]
tcArgTele _ [] k =
  Env.err [DD "Too many arguments provided."]
tcArgTele _  tele k = 
  Env.err [DS "Invalid telescope", DD tele]

-- | Substitute a list of terms for the variables bound in a telescope
-- This is used to instantiate the parameters of a data constructor
-- to find the types of its arguments.
-- The first argument should only contain 'Rel' type declarations.
substTele :: [Decl] -> [Arg] -> [Decl] -> TcMonad [Decl]
substTele tele args = doSubst (mkSubst tele (map unArg args))
  where
    mkSubst [] [] = []
    mkSubst (TypeSig (Sig x (Mode Rel _) _) : tele') (tm : tms) =
      (x, tm) : mkSubst tele' tms
    mkSubst _ _ = error "Internal error: substTele given illegal arguments"



-- Propagate the given substitution through the telescope, potentially
-- reworking the constraints
doSubst :: [(TName, Term)] -> [Decl] -> TcMonad [Decl]
doSubst ss [] = return []
doSubst ss (Def x ty : tele') = do
  let tx' = Unbound.substs ss (Var x)
  let ty' = Unbound.substs ss ty
  decls1 <- Equal.unify [] tx' ty'
  decls2 <- Env.extendCtxs decls1 (doSubst ss tele')
  return $ decls1 ++ decls2
doSubst ss (TypeSig sig : tele') = do
  tynf <- Equal.whnf (Unbound.substs ss (sigType sig))
  let sig' = sig{sigType = tynf}
  tele'' <- doSubst ss tele'
  return $ TypeSig sig' : tele''
doSubst _ tele = 
  Env.err [DS "Invalid telescope", DD tele]

-----------------------------------------------------------

-- | Create a binding for each of the variables in the pattern
-- TODO check j and k
declarePat :: Pattern -> Epsilon -> Type -> TcMonad [Decl]
declarePat (PatVar x)       ep ty  = return [TypeSig (Sig x ep ty)]
declarePat (PatCon dc pats) (Mode Rel j) ty = do 
  (tc,params) <- Equal.ensureTCon ty
  (Telescope delta, Telescope deltai, k) <- Env.lookupDCon dc tc
  tele <- substTele delta params deltai
  declarePats dc pats tele
declarePat pat (Mode Irr _) _ty =
  Env.err [DS "Cannot pattern match irrelevant arguments in pattern", DD pat]

-- | Given a list of pattern arguments and a telescope, create a binding for 
-- each of the variables in the pattern, 
declarePats :: DCName -> [(Pattern, Rho)] -> [Decl] -> TcMonad [Decl]
declarePats dc pats (Def x ty : tele) = do
  let ds1 = [Def x ty]
  ds2 <- Env.extendCtxs ds1 $ declarePats dc pats tele
  return (ds1 ++ ds2)
declarePats dc ((pat, _) : pats) (TypeSig (Sig x ep ty) : tele) = do
  ds1 <- declarePat pat ep ty
  let tm = pat2Term pat
  ds2 <- Env.extendCtxs ds1 $ declarePats dc pats (Unbound.subst x tm tele)
  return (ds1 ++ ds2)
declarePats dc []   [] = return []
declarePats dc []    _ = Env.err [DS "Not enough patterns in match for data constructor", DD dc]
declarePats dc pats [] = Env.err [DS "Too many patterns in match for data constructor", DD dc]
declarePats dc _    _ = Env.err [DS "Invalid telescope", DD dc]

-- | Convert a pattern to a term 
pat2Term :: Pattern ->  Term
pat2Term (PatVar x) = Var x
pat2Term (PatCon dc pats) = DCon dc (pats2Terms pats) 
  where
    pats2Terms :: [(Pattern, Rho)] -> [Arg]
    pats2Terms [] = []
    pats2Terms ((p, ep) : ps) = Arg ep t : ts where
      t = pat2Term p 
      ts = pats2Terms ps
       

-- | Check all of the types contained within a telescope
tcTypeTele :: [Decl] -> Int -> TcMonad ()
tcTypeTele [] k = return ()
tcTypeTele (Def x tm : tl) k = do
  ty1 <- Env.withStage Irr $ inferType (Var x) k
  Env.withStage Irr $ checkType tm ty1 k
  let decls = [Def x tm] 
  Env.extendCtxs decls $ tcTypeTele tl k
tcTypeTele (TypeSig sig : tl) k = do
  let l = case sigEp sig of { Mode _ NonDep -> k ; Mode _ (Dep j) -> j}
  tcType (sigType sig) l
  Env.extendCtx (TypeSig sig) $ tcTypeTele tl k
tcTypeTele tele k = 
  Env.err [DS "Invalid telescope: ", DD tele]



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
          ty <- inferType term 0
          return $ AddCtx [TypeSig (Sig n (Mode Rel (Dep 0)) ty), Def n term]
        Just sig ->
          let handler (Env.Err ps msg) = throwError $ Env.Err ps (msg $$ msg')
              msg' =
                disp
                  [ 
                    DS "When checking the term",
                    DD term,
                    DS "against the signature",
                    DD sig
                  ]
           in do
                Env.extendCtx (TypeSig sig) $ checkType term (sigType sig) (sigLevel sig) `catchError` handler
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
  tcType (sigType sig) (sigLevel sig)
  return $ AddHint sig
tcEntry (Demote ep) = return (AddCtx [Demote ep])


-- rule Decl_data
tcEntry (Data t (Telescope delta) cs k) =
  do
    -- Check that the telescope for the datatype definition is well-formed
    edelta <- tcTypeTele delta k
    ---- check that the telescope provided
    ---  for each data constructor is wellfomed, and elaborate them
    let elabConstructorDef defn@(ConstructorDef pos d (Telescope tele)) =
          Env.extendSourceLocation pos defn $
            Env.extendCtx (DataSig t (Telescope delta) k) $
              Env.extendCtxTele delta $ do
                etele <- tcTypeTele tele k
                return (ConstructorDef pos d (Telescope tele))
    ecs <- mapM elabConstructorDef cs
    -- Implicitly, we expect the constructors to actually be different...
    let cnames = map (\(ConstructorDef _ c _) -> c) cs
    unless (length cnames == length (nub cnames)) $
      Env.err [DS "Datatype definition", DD t, DS "contains duplicated constructors"]
    -- finally, add the datatype to the env and perform action m
    return $ AddCtx [Data t (Telescope delta) ecs k]
tcEntry (DataSig _ _ _) = Env.err [DS "internal construct"]
tcEntry (RecDef _ _) = Env.err [DS "internal construct"]



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
            [ DS "Duplicate type signature",
              DD sig,
              DS "Previous was",
              DD sig'
            ]
       in Env.extendSourceLocation p sig $ Env.err msg

-----------------------------------------------------------
-- Checking that pattern matching is exhaustive
-----------------------------------------------------------

-- | Given a particular type and a list of patterns, make
-- sure that the patterns cover all potential cases for that
-- type.
-- If the list of patterns starts with a variable, then it doesn't
-- matter what the type is, the variable is exhaustive. (This code
-- does not report unreachable patterns.)
-- Otherwise, the scrutinee type must be a type constructor, so the
-- code looks up the data constructors for that type and makes sure that
-- there are patterns for each one.
exhaustivityCheck :: Term -> Type -> [Pattern] -> TcMonad ()
exhaustivityCheck scrut ty (PatVar x : _) = return ()
exhaustivityCheck scrut ty pats = do
  (tcon, tys) <- Equal.ensureTCon ty
  (Telescope delta, mdefs, k) <- Env.lookupTCon tcon
  case mdefs of
    Just datacons -> do
      loop pats datacons
      where
        loop [] [] = return ()
        loop [] dcons = do
          l <- checkImpossible dcons
          if null l
            then return ()
            else Env.err $ DS "Missing case for" : map DD l
        loop (PatVar x : _) dcons = return ()
        loop (PatCon dc args : pats') dcons = do
          (ConstructorDef _ _ (Telescope tele), dcons') <- removeDCon dc dcons
          tele' <- substTele delta tys tele
          let (aargs, pats'') = relatedPats dc pats'
          -- check the arguments of the data constructor
          checkSubPats dc tele' (args : aargs)
          loop pats'' dcons'

        -- make sure that the given list of constructors is impossible
        -- in the current environment
        checkImpossible :: [ConstructorDef] -> TcMonad [DCName]
        checkImpossible [] = return []
        checkImpossible (ConstructorDef _ dc (Telescope tele) : rest) = do
          this <-
            ( do
                tele' <- substTele delta tys tele
                tcTypeTele tele' 0 --TODO!!
                return [dc]
              )
              `catchError` (\_ -> return [])
          others <- checkImpossible rest
          return (this ++ others)
    Nothing ->
      Env.err [DS "Cannot determine constructors of", DD ty]


-- | Given a particular data constructor name and a list of data
-- constructor definitions, pull the definition out of the list and
-- return it paired with the remainder of the list.
removeDCon ::
  DCName ->
  [ConstructorDef] ->
  TcMonad (ConstructorDef, [ConstructorDef])
removeDCon dc (cd@(ConstructorDef _ dc' _) : rest)
  | dc == dc' =
    return (cd, rest)
removeDCon dc (cd1 : rest) = do
  (cd2, rr) <- removeDCon dc rest
  return (cd2, cd1 : rr)
removeDCon dc [] = Env.err [DS $ "Internal error: Can't find " ++ show dc]

-- | Given a particular data constructor name and a list of patterns,
-- pull out the subpatterns that occur as arguments to that data
-- constructor and return them paired with the remaining patterns.
relatedPats :: DCName -> [Pattern] -> ([[(Pattern, Rho)]], [Pattern])
relatedPats dc [] = ([], [])
relatedPats dc (pc@(PatVar _) : pats) = ([], pc : pats)
relatedPats dc ((PatCon dc' args) : pats)
  | dc == dc' =
    let (aargs, rest) = relatedPats dc pats
     in (args : aargs, rest)
relatedPats dc (pc : pats) =
  let (aargs, rest) = relatedPats dc pats
   in (aargs, pc : rest)


-- | Occurs check for the subpatterns of a data constructor. Given
-- the telescope specifying the types of the arguments, plus the
-- subpatterns identified by relatedPats, check that they are each
-- exhaustive.

-- for simplicity, this function requires that all subpatterns
-- are pattern variables.
checkSubPats :: DCName -> [Decl] -> [[(Pattern, Rho)]] -> TcMonad ()
checkSubPats dc [] _ = return ()
checkSubPats dc (Def _ _ : tele) patss = checkSubPats dc tele patss
checkSubPats dc (TypeSig _ : tele) patss
  | (not . null) patss && not (any null patss) = do
    let hds = map (fst . head) patss
    let tls = map tail patss
    case hds of
      [PatVar _ ] -> checkSubPats dc tele tls
      _ -> Env.err [DS "All subpatterns must be variables in this version."]
checkSubPats dc t ps =
  Env.err [DS "Internal error in checkSubPats", DD dc, DS (show ps)]


