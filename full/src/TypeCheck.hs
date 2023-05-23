{- pi-forall -}

-- | The main routines for type-checking
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use list comprehension" #-}
module TypeCheck (tcModules, inferType, checkType) where

import Control.Monad.Except
import Data.List (nub)
import GHC.Generics (Generic)
import Data.Maybe ( catMaybes, fromMaybe )

import LevelSolver
import Environment (D (..), Locality(..), TcMonad)
import Environment qualified as Env
import Equal qualified
import PrettyPrint (Disp (disp), pp)
import Syntax

import Debug.Trace

import Text.PrettyPrint.HughesPJ (($$), render)

import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)


-- | Infer/synthesize the type of a term
-- If we can infer a type of a term, we can always infer its smallest level
inferType :: Term -> Level -> TcMonad (Type, Term)
inferType t = tcTerm t Nothing

-- | Check that the given term has the expected type
-- Sometimes we can also infer the level of the term, but not always
checkType :: Term -> Type -> Level -> TcMonad (Term)
checkType tm (Pos _ ty) k = checkType tm ty k  -- ignore source positions/annotations
checkType tm (Ann ty _) k = checkType tm ty k
checkType tm ty k = do
  nf <- Equal.whnf ty
  (_,t) <- tcTerm tm (Just nf) k
  return t


-- | Make sure that the term is a "type" (i.e. that it has type 'Type')
-- | and find out its level, if possible.
tcType :: Term -> Level -> TcMonad (Term)
tcType tm k = Env.withStage Irr $ checkType tm Type k

---------------------------------------------------------------------

localize :: Level -> Maybe Level -> Level
localize = fromMaybe

getLevel :: Maybe Level -> TcMonad Level
getLevel mk = case mk of
          Just k -> return k
          Nothing -> Env.err [DS "BUG: No level in sig"]
---------------------------------------------------------------------

-- | Combined type checking/inference function
-- The second argument is 'Just expectedType' in checking mode and 'Nothing' in inference mode
-- If the second argument is Nothing`, then the third argument may be `Just k` in order to 
-- pass through a known level
-- In either case, this function returns the type of the term and a lower bound of its level
tcTerm :: Term -> Maybe Type -> Level -> TcMonad (Type, Term)

-- i-var
tcTerm t@(Var x) Nothing mk = do
  ms <- Env.lookupTyMaybe Global x
  case ms of
    Just sig -> do
      -- global variable, try to displace
      jx <- Unbound.fresh (Unbound.string2Name ("jV" ++ show x))
      tcTerm (Displace (Var x) (LVar jx)) Nothing mk
    Nothing -> do
      sig <- Env.lookupTy x        -- make sure the variable is accessible
      l <- getLevel (sigLevel sig) -- make sure that it is annotated with a level
      Env.checkStage (sigRho sig)
      Env.extendLevelConstraint (Le l mk)
      return (sigType sig, Var x)

-- i-type
tcTerm Type Nothing mk = do
  Env.extendLevelConstraint (Le (LConst 0) mk)
  return (Type, Type)

-- i-pi
tcTerm (Pi (Mode ep lvl) tyA bnd) Nothing mk = do
  (x, tyB) <- Unbound.unbind bnd
  case lvl of
    Just j -> do
      tyA' <- tcType tyA j
      tyB' <- Env.extendCtx (TypeSig (Sig x ep (Just j) tyA')) (tcType tyB mk)
      Env.extendLevelConstraint (Lt j mk)
      return (Type, Pi (Mode ep (Just j)) tyA' (Unbound.bind x tyB'))
    Nothing -> do
      tyA' <- tcType tyA mk
      tyB' <- tcType tyB mk   -- x can't appear in B
      return (Type, Pi (Mode ep Nothing) tyA' (Unbound.bind x tyB'))

-- c-lam: check the type of a function
tcTerm (Lam ep1  bnd) (Just (Pi (Mode ep2 lvl) tyA bnd2)) mk = do
  -- unbind the variables in the lambda expression and pi type
  (x, body,_,tyB) <- Unbound.unbind2Plus bnd bnd2
  -- epsilons should match up
  unless (ep1 == ep2) $ Env.err [DS "In function definition, expected", DD ep2, DS "parameter", DD x,
                                 DS "but found", DD ep1, DS "instead."]
  let j = localize mk lvl
  -- check the type of the body of the lambda expression
  body' <- Env.extendCtx (TypeSig (Sig x ep1 (Just j) tyA)) (checkType body tyB mk)
  return (Pi (Mode ep1 lvl) tyA bnd2, Lam ep1 (Unbound.bind x body'))
tcTerm (Lam _ _) (Just nf) k =
  Env.err [DS "Lambda expression should have a function type, not", DD nf]

-- i-app
tcTerm (App t1 t2) Nothing mk = do
  (ty1, t1') <- inferType t1 mk
  (Mode ep1 lvl, tyA, bnd) <- Equal.ensurePi ty1
  unless (ep1 == argEp t2) $ Env.err
    [DS "In application, expected", DD ep1, DS "argument but found",
                                    DD t2, DS "instead." ]
  -- if the argument is Irrelevant, resurrect the context
  -- check the argument against the localized level
  t2' <- (if ep1 == Irr then Env.extendCtx (Demote Rel) else id) $
          checkType (unArg t2) tyA (localize mk lvl)
  return (Unbound.instantiate bnd [unArg t2], App t1' (Arg ep1 t2'))


-- i-ann
tcTerm (Ann tm ty) Nothing mk = do
  ty' <- tcType ty mk
  tm' <- checkType tm ty' mk
  return (ty', Ann tm' ty')

-- practicalities
-- remember the current position in the type checking monad
tcTerm (Pos p tm) mTy mk =
  Env.extendSourceLocation p tm $ tcTerm tm mTy mk

-- ignore term, just return type annotation
tcTerm TrustMe (Just ty) mk = do
  ty' <- tcType ty mk
  return (ty', TrustMe)

-- i-unit
tcTerm TyUnit Nothing k = return (Type, TyUnit)
tcTerm LitUnit Nothing k = return (Type, LitUnit)

-- i-bool
tcTerm TyBool _ k = Env.err [DS "Booleans are datatypes in this version"]
tcTerm LitBool{} _ k = Env.err [DS "Booleans are datatypes in this version"]
tcTerm If{} mty mk = Env.err [DS "Booleans are datatypes in this version"]

tcTerm (Let rhs bnd) mty mk = do
  (x, body) <- Unbound.unbind bnd
  -- allow the level of the binding to be lower than 
  -- the level of the expression, if it needs to be
  -- NOTE: check what happens if x escapes in the type?
  lvar <- Unbound.fresh (Unbound.string2Name "l")
  (aty, rhs') <- inferType rhs (LVar lvar)
  Env.extendLevelConstraint (Le (LVar lvar) mk)
  (ty, body') <- Env.extendCtxs [mkSig x aty (LVar lvar), Def x rhs] $
      tcTerm body mty mk
  let tm' = Let rhs' (Unbound.bind x body')
  case mty of
    Just _ -> return (ty, tm')
    Nothing -> return (Unbound.subst x rhs ty, tm')

-- Type constructor application, j0 is displacement amount
tcTerm (TCon c j0 params) Nothing mk = do
  (Telescope delta, _, j) <- Env.lookupTCon c
  Env.extendLevelConstraint (Le (j0 <> j) mk)
  let numParams = length (filter isTypeSig delta)
  unless (length params == numParams) $
    Env.err
      [ DS "Datatype constructor",
        DD c,
        DS "should have",
        DD (length delta),
        DS "parameters, but was given",
        DD (length params),
        DS "parameters."
      ]
  Telescope delta' <- Equal.displaceTele j0 (Telescope delta)
  params' <- tcArgTele params delta' mk
  return (Type, TCon c j0 params')

-- Data constructor application
-- we don't know the expected type, so see if there
-- is only one datacon of that name that takes no
-- parameters
-- TODO: check level of TCon + displacement <= mk
tcTerm t@(DCon c j0 args) Nothing mk = do
  matches <- Env.lookupDConAll c
  case matches of
    [(tname, (Telescope [], cd@(ConstructorDef _ _ (Telescope deltai) _)))] -> do
      (_, _, k) <- Env.lookupTCon tname
      -- we know j <= k, so we check k + j0 <= mk
      Env.extendLevelConstraint (Le (j0 <> k) mk)
      let numArgs = length (filter isTypeSig deltai)
      unless (length args == numArgs) $
        Env.err
          [ DS "Constructor",
            DD cd,
            DS "should have",
            DD numArgs,
            DS "data arguments, but was given",
            DD (length args),
            DS "arguments."
          ]
      Telescope deltai' <- Equal.displaceTele j0 (Telescope deltai)
      args' <- tcArgTele args deltai' mk
      return (TCon tname j0 [], DCon c j0 args)

    [_] ->
      Env.err
        [ DS "Cannot infer the parameters to data constructors.",
          DS "Add an annotation."
        ]
    _ -> Env.err [DS "Ambiguous data constructor", DS c]

-- we know the expected type of the data constructor
-- so look up its type in the context
tcTerm t@(DCon c j0 args) (Just ty) mk = do
  case ty of
    (TCon tname k0 params) -> do
      Env.extendLevelConstraint (Eq j0 k0)
      (Telescope delta, Telescope deltai, _) <- Env.lookupDCon c tname
      (_, _, k) <- Env.lookupTCon tname
      -- we know j <= k, so we check k + k0 <= mk
      Env.extendLevelConstraint (Le (k0 <> k) mk)
      let numArgs = length (filter isTypeSig deltai)
      unless (length args == numArgs) $
        Env.err
          [ DS "Constructor",
            DS c,
            DD deltai,
            DS "should have",
            DD numArgs,
            DS "data arguments, but was given",
            DD (length args),
            DS "arguments."
          ]
      Telescope delta' <- Equal.displaceTele j0 (Telescope delta)
      Telescope deltai' <- Equal.displaceTele j0 (Telescope deltai)
      newTele <- substTele delta params deltai'
      args' <- tcArgTele args newTele mk
      return (ty, DCon c j0 args')
    _ ->
      Env.err [DS "Unexpected type", DD ty, DS "for data constructor", DD t]

-- Must have an annotation for Case
-- What about the level of the RHS of the case? Doing current level now, but could
-- restrict to scrutinee level
tcTerm t@(Case scrut alts) (Just ty) mk = do
  j <- LVar <$> Unbound.fresh (Unbound.string2Name "jS")
  Env.extendLevelConstraint (Le j mk)
  (sty, scrut') <- inferType scrut j
  scrut'' <- Equal.whnf scrut'
  (c, d0, args) <- Equal.ensureTCon sty
  let checkAlt (Match bnd) = do
        (pat, body) <- Unbound.unbind bnd
        -- add variables from pattern to context
        -- could fail if branch is in-accessible
        decls <- declarePat pat (Mode Rel (Just j)) sty
        -- add defs to the contents from scrut = pat
        -- could fail if branch is in-accessible
        patTm <- pat2Term pat
        patTm' <- Env.extendCtxs decls $ checkType patTm sty j
        decls' <- Equal.unify [] scrut'' patTm'
        body' <- Env.extendCtxs (decls ++ decls') $ do
          checkType body ty mk
        return (Match (Unbound.bind pat body'))

  let pats = map (\(Match bnd) -> fst (unsafeUnbind bnd)) alts
  alts' <- mapM checkAlt alts
  exhaustivityCheck scrut' sty pats
  return (ty, Case scrut' alts')

tcTerm t@(TyEq a b) Nothing mk = do
  (aTy, a') <- inferType a mk
  b' <- checkType b aTy mk
  return (Type, TyEq a' b')

tcTerm Refl (Just ty@(TyEq a b)) mk = do
  Equal.equate a b
  return (ty, Refl)
tcTerm Refl (Just ty) k =
  Env.err [DS "Refl annotated with", DD ty]


tcTerm t@(Subst a b) (Just ty) mk = do
  -- infer the type of the proof 'b'
  (tp, b') <- inferType b mk
  -- make sure that it is an equality between m and n
  (m, n) <- Equal.ensureTyEq tp
  -- if either side is a variable, add a definition to the context
  edecl <- def m n
  -- if proof is a variable, add a definition to the context
  pdecl <- def b Refl
  a' <- Env.extendCtxs (edecl ++ pdecl) $ checkType a ty mk
  return (ty, Subst a' b')

tcTerm t@(Contra p) (Just ty) mk = do
  (ty', p') <- inferType p mk
  (a, b) <- Equal.ensureTyEq ty'
  a' <- Equal.whnf a
  b' <- Equal.whnf b
  case (a', b') of

    (DCon da _ _, DCon db _ _)
      | da /= db ->
        return (ty, p')

    (LitBool b1, LitBool b2)
      | b1 /= b2 ->
        return (ty, p')
    (_, _) ->
      Env.err
        [ DS "I can't tell that",
          DD a,
          DS "and",
          DD b,
          DS "are contradictory"
        ]

tcTerm Sigma{} _ mk = Env.err [DS "The parser for 'full' expands Sigmas into datatypes"]
tcTerm Prod{} _ k = Env.err [DS "The parser for 'full' expands Sigmas into datatypes"]
tcTerm LetPair{} _ k =  Env.err [DS "The parser for 'full' expands Sigmas into datatypes"]

tcTerm PrintMe (Just ty) mk = do
  gamma <- Env.getLocalCtx
  cs <- Env.dumpConstraints
  let dcs = displayConstraints (Env.simplify cs)
  Env.warn $ [DS "Unmet obligation.\nContext:", DD gamma,
        DS "\nGoal:", DD ty,
        DS "\nConstraints:"] ++ dcs
  ty' <- tcType ty mk
  return (ty', PrintMe)

tcTerm (Displace t j) Nothing mk = do
  case t of
    (Var x) -> do
      msig <- Env.lookupTyMaybe Global x
      case msig of
        Just sig -> do
            Env.checkStage (sigRho sig)       -- make sure the variable is accessible
            k <- getLevel (sigLevel sig)      -- global level of "x"
            Env.extendLevelConstraint (Le (j <> k) mk)
            ty <- Equal.displace j (sigType sig)    -- displace its type
            return (ty, Displace (Var x) j)
        Nothing -> Env.err [DS "Can only displace top-level vars", DD x]
    u ->
      Env.err [DS "Found displacement", DD (show t)]

-- c-infer
tcTerm tm (Just ty) mk = do
  (ty', tm') <- inferType tm mk
  Equal.equate ty' ty
  return (ty', tm')

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
tcArgTele :: [Arg] -> [Decl] -> Level -> TcMonad [Arg]
tcArgTele [] [] mk = return []
tcArgTele args (Def x ty : tele) mk = do
  tele' <- doSubst [(x,ty)] tele
  tcArgTele args tele' mk
tcArgTele (Arg ep1 tm : terms) (TypeSig (Sig x ep2 l ty) : tele) mk
  | ep1 == ep2 = do
      tm' <- Env.withStage ep1 $ checkType tm ty (localize mk l)
      tele' <- doSubst [(x, tm)] tele
      (Arg ep1 tm' :) <$> tcArgTele terms tele' mk
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
    mkSubst (TypeSig (Sig x Rel _ _) : tele') (tm : tms) =
      (x, tm) : mkSubst tele' tms
    mkSubst (TypeSig (Sig x Irr _ _) : tele') _ =
      error $ "Internal error: " <> pp x <> " is irrelevant"
    mkSubst [] (tm: _) =
      error $ "Internal error: " <> pp tm <> " is extra"
    mkSubst (TypeSig (Sig x _ _ _) : _) [] =
      error $ "Internal error: " <> pp x <> " has no arg in mkSubst"
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
-- TODO: check j and k
declarePat :: Pattern -> Epsilon -> Type -> TcMonad [Decl]
declarePat (PatVar x)       (Mode rho j) ty = return [TypeSig (Sig x rho j ty)]
declarePat (PatCon dc pats) (Mode Rel (Just j)) ty = do
  (tc, j0, params) <- Equal.ensureTCon ty
  (Telescope delta, Telescope deltai, k) <- Env.lookupDCon dc tc
  Env.extendLevelConstraint (Le (j0 <> k) j)
  tele <- substTele delta params deltai
  declarePats dc pats j tele
declarePat pat (Mode Rel Nothing) _ty =
  Env.err [DS "Need a concrete level here"]
declarePat pat (Mode Irr _) _ty =
  Env.err [DS "Cannot pattern match irrelevant arguments in pattern", DD pat]

-- | Given a list of pattern arguments and a telescope, create a binding for 
-- each of the variables in the pattern, 
declarePats :: DCName -> [(Pattern, Rho)] -> Level -> [Decl] -> TcMonad [Decl]
declarePats dc pats j (Def x ty : tele) = do
  let ds1 = [Def x ty]
  ds2 <- Env.extendCtxs ds1 $ declarePats dc pats j tele
  return (ds1 ++ ds2)
declarePats dc ((pat, _) : pats) j (TypeSig (Sig x r l ty) : tele) = do
  let k = localize j l
  ds1 <- declarePat pat (Mode r (Just k)) ty
  tm <- pat2Term pat
  tele' <- doSubst [(x, tm)] tele
  -- let tele' = map ((Unbound.subst :: TName -> Term -> Decl -> Decl) x tm) tele
  ds2 <- Env.extendCtxs ds1 $ declarePats dc pats j tele'
  return (ds1 ++ ds2)
declarePats dc []  j [] = return []
declarePats dc []  j  _ = Env.err [DS "Not enough patterns in match for data constructor", DD dc]
declarePats dc pats j [] = Env.err [DS "Too many patterns in match for data constructor", DD dc]
declarePats dc _    j _ = Env.err [DS "Invalid telescope", DD dc]

-- | Convert a pattern to a term 
pat2Term :: Pattern -> TcMonad Term
pat2Term (PatVar x) = return $ Var x
pat2Term (PatCon dc pats) = do
  d <- LVar <$> Unbound.fresh (Unbound.string2Name "d")
  args <- pats2Terms pats
  return $ DCon dc d args
  where
    pats2Terms :: [(Pattern, Rho)] -> TcMonad [Arg]
    pats2Terms [] = return []
    pats2Terms ((p, ep) : ps) = do
      t <- pat2Term p
      ts <- pats2Terms ps
      return $ Arg ep t : ts


-- | Check all of the types contained within a telescope
tcTypeTele :: [Decl] -> Level -> TcMonad [Decl]
tcTypeTele [] k = return []
tcTypeTele (Def x tm : tl) mk = do
  (ty1, vx) <- Env.withStage Irr $ inferType (Var x) mk
  tm' <- Env.withStage Irr $ checkType tm ty1 mk
  let decls = [Def x tm]
  tele' <- Env.extendCtxs decls $ tcTypeTele tl mk
  return (Def x tm' : tele')
tcTypeTele (TypeSig sig : tl) mk = do
  l <- case sigLevel sig of
             Just j -> do
                Env.extendLevelConstraint (Lt j mk)
                return j
             Nothing ->
                return mk
  ty' <- tcType (sigType sig) l
  tl' <- Env.extendCtx (TypeSig sig { sigLevel = Just l}) $ tcTypeTele tl mk
  return (TypeSig (sig { sigType = ty'}) : tl')
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
        AddCtx decls -> do
          (decls ++) <$> Env.extendCtxsGlobal decls m
    -- Get all of the defs from imported modules (this is the env to check current module in)
    importedModules = filter (\x -> ModuleImport (moduleName x) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Decl.
data HintOrCtx
  = AddHint Sig
  | AddCtx [Decl]

displayConstraints :: [(Env.SourceLocation, LevelConstraint)] -> [D]
displayConstraints = concatMap (\(Env.SourceLocation p _, c) -> [DD p, DD c])

dumpAndSolve :: (Unbound.Alpha a, Disp a) => a -> TcMonad [(LName, Level)]
dumpAndSolve tm = do
  let vs  = (Unbound.toListOf Unbound.fv tm :: [LName])
  let ss' = zip (nub vs) (repeat (LConst 0))
  cs <- Env.dumpConstraints
  mss <- liftIO $ solveConstraints (map snd cs)
  case mss of
        Nothing -> Env.err $ [DS "Cannot satisfy level constraints.",
                     DS "Term is:", DD tm,
                     DS "Constraints are "] ++ displayConstraints (Env.simplify cs)
        Just ss -> return (ss ++ ss')

-- | Check each sort of declaration in a module
tcEntry :: Decl -> TcMonad HintOrCtx
tcEntry (Def n term) = do
  oldDef <- Env.lookupDef Any n
  maybe tc die oldDef
  where
    tc = do
      lkup <- Env.lookupHint n
      case lkup of
        Nothing -> do
          kv <- Unbound.fresh (Unbound.string2Name "k")
          (ty, term') <- inferType term (LVar kv)
          ss <- dumpAndSolve (ty, term)
          let decls = Unbound.substs ss [TypeSig (Sig n Rel (Just (LVar kv)) ty), Def n term']
          return $ AddCtx decls
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
                term' <- Env.extendCtx (TypeSig sig) $
                  checkType term (sigType sig) (fromMaybe (LConst 0) (sigLevel sig))
                   `catchError` handler
                ss <- dumpAndSolve (term', sigType sig)
                if n `elem` Unbound.toListOf Unbound.fv term
                  then return $ AddCtx (Unbound.substs ss [TypeSig sig, RecDef n term'])
                  else return $ AddCtx (Unbound.substs ss [TypeSig sig, Def n term'])
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
  kv <- Unbound.fresh (Unbound.string2Name "kS")
  let l = fromMaybe (LVar kv) (sigLevel sig)
  ty' <- tcType (sigType sig) l
  return $ AddHint (sig { sigType = ty' })
tcEntry (Demote ep) = return (AddCtx [Demote ep])


-- rule Decl_data
tcEntry decl@(Data t (Telescope delta) cs k) =
  do
    -- Check that the telescope for the datatype definition is well-formed
    -- in this case, the telescope indicates parameters to the data decl
    -- all arguments must be named in this telescope, but they may or may not
    -- have a fixed level
    -- `k` is the level of the datatype `t` itself
    edelta <- tcTypeTele delta k
    -- add the `k` as the level of any parameters that don't have a fixed level.
    let ldelta = map (localizeDecl k) delta
    -- Check that the telescope provided
    -- for each data constructor is wellfomed, and elaborate them
    -- In this case, the telescopes are "types" for the datacons, so named
    -- arguments require explicit levels (and unification variables are generated if they
    -- are not present). 
    let elabConstructorDef defn@(ConstructorDef pos d (Telescope tele) ck) =
          Env.extendSourceLocation pos defn $
            Env.extendCtx (DataSig t (Telescope delta) k) $
              Env.extendCtxTele ldelta $ do
                Env.extendLevelConstraint (Le ck k)
                etele <- tcTypeTele tele ck
                return (ConstructorDef pos d (Telescope etele) ck)
    ecs <- mapM elabConstructorDef cs
    -- Implicitly, we expect the constructors to actually be different...
    let cnames = map (\(ConstructorDef _ c _ _) -> c) cs
    unless (length cnames == length (nub cnames)) $
      Env.err [DS "Datatype definition", DD t, DS "contains duplicated constructors"]
    -- solve the level constraints and add the elaborated decl to the context
    ss <- dumpAndSolve decl
    return $ AddCtx (Unbound.substs ss [Data t (Telescope edelta) ecs k])
tcEntry DataSig{} = Env.err [DS "internal construct"]
tcEntry RecDef{} = Env.err [DS "internal construct"]

localizeDecl :: Level -> Decl -> Decl
localizeDecl k (TypeSig sig) = TypeSig (sig { sigLevel = Just (localize k (sigLevel sig)) })
localizeDecl k d = d



-- | Make sure that we don't have the same name twice in the
-- environment. (We don't rename top-level module definitions.)
duplicateTypeBindingCheck :: Sig -> TcMonad ()
duplicateTypeBindingCheck sig = do
  -- Look for existing type bindings ...
  let n = sigName sig
  l <- Env.lookupTyMaybe Local n
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
  (tcon, j0, tys) <- Equal.ensureTCon ty
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
          (ConstructorDef _ _ (Telescope tele) _, dcons') <- removeDCon dc dcons
          tele' <- substTele delta tys tele
          let (aargs, pats'') = relatedPats dc pats'
          -- check the arguments of the data constructor
          checkSubPats dc tele' (args : aargs)
          loop pats'' dcons'

        -- make sure that the given list of constructors is impossible
        -- in the current environment
        checkImpossible :: [ConstructorDef] -> TcMonad [DCName]
        checkImpossible [] = return []
        checkImpossible (ConstructorDef _ dc (Telescope tele) ck : rest) = do
          this <-
            ( do
                tele' <- substTele delta tys tele
                _ <- tcTypeTele tele' ck
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
removeDCon dc (cd@(ConstructorDef _ dc' _ _) : rest)
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

{-
-- Bounds are <= and >= for each variable
data Bound = Bound { upper :: [Level], lower :: [Level] }
  deriving (Generic, Show, Eq, Ord, Unbound.Alpha, Unbound.Subst Level)

type Bounds = [(LName,Bound)]

-- x < l <=> x <= l + 1   l /= 0
-- l < x <=> l + 1 <= x
findBound :: LName -> Bounds -> Bound
findBound x bs =
  case lookup x bs of
    Just b -> b
    Nothing -> Bound [] []

addConstraint :: LevelConstraint -> Bounds -> (Bounds, [LevelConstraint])
addConstraint c bs =
  case c of
        Eq (LVar x) t -> let b = findBound x bs in
          ((x, Bound { upper = [t], lower = [t] }) : bs, [])
        Lt (LVar x) t -> let b = findBound x bs in
          ((x, b { upper = (LAdd (LConst 1) t):upper b}): bs, [])
        Le (LVar x) t -> let b = findBound x bs in
          ((x, b { upper = (t:upper b) }) : bs, [])
        Lt t (LVar x) -> let b = findBound x bs in
          ((x, b { lower = (LAdd (LConst 1) t):lower b}) : bs, [])
        Le t (LVar x) -> let b = findBound x bs in
          ((x, b { lower = t:lower b}) : bs, [])
        _ -> (bs, [c])
-}

{-

simplifyConstraints :: [LevelConstraint] -> [LevelConstraint]
simplifyConstraints (Eq l1 l2 : cs) | l1 == l2 =
    simplifyConstraints cs
simplifyConstraints (Eq (LVar x) l : cs) =
    Eq (LVar x) l : simplifyConstraints (Unbound.subst x l cs)
simplifyConstraints (Eq l (LVar x) : cs) =
    Eq (LVar x) l : simplifyConstraints (Unbound.subst x l cs)
simplifyConstraints (Eq (LAdd (LConst x1) y1) (LAdd (LConst x2) y2) : cs)
  | x1 == x2 =
    simplifyConstraints (Eq y1 y2 : cs)
simplifyConstraints (Eq x1 y1 : cs) =
  Eq x1 y1 : simplifyConstraints cs
simplifyConstraints (Lt x y : cs) =
  let new = case (x,y) of
              (LConst x1, LConst x2) -> if x1 < x2 then [] else [Lt x y]
              _ -> [Lt x y]
    in
      new ++ simplifyConstraints cs
simplifyConstraints (Le x y : cs) =
  let new = case (x,y) of
              (LConst x1, LConst x2) -> if x1 <= x2 then [] else [Le x y]
              _ -> [Le x y]
    in
      new ++ simplifyConstraints cs
simplifyConstraints [] = []

constraints2bounds :: [LevelConstraint] -> ( Bounds, [LevelConstraint] )
constraints2bounds = go [] where
  go b (c : cs) = (b'', c' ++ cs') where
    (b', c') = addConstraint c b
    (b'', cs') = go b' cs
  go b [] = (b, [])

constraints2subst :: [LevelConstraint] -> [(LName, Level)]
constraints2subst = go where
  go ((Eq (LVar x) l):cs) = (x,l): go cs
  go ((Le l (LVar x)):cs) = (x,l): go cs
  go (_:cs) = go cs
  go [] = []

  -}