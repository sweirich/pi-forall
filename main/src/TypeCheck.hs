{- PiForall language -}

-- | The main routines for type-checking
module TypeCheck (tcModules, inferType, checkType) where

import Control.Monad.Except
{- SOLN DATA -}
import Data.List (nub)
{- STUBWITH -}
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
  sig <- Env.lookupTy x {- SOLN EP -}
  -- make sure the variable is accessible
  Env.checkStage (sigEp sig) {- STUBWITH -}
  return (t, sigType sig)
tcTerm t@(Type) Nothing = return (t, Type)
tcTerm (Pi bnd) Nothing = do
  ((x, {- SOLN EP -}ep,{- STUBWITH -} Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
  atyA <- tcType tyA
  atyB <- Env.extendCtx (Sig (S x {- SOLN EP -} ep {- STUBWITH -} atyA)) $ tcType tyB
  return (Pi (Unbound.bind (x, {- SOLN EP -} ep, {- STUBWITH -} Unbound.embed atyA) atyB), Type)

-- Check the type of a function
tcTerm (Lam bnd) (Just (Pi bnd2)) = do
  -- unbind the variables in the lambda expression and pi type
  ( (x, {- SOLN EP -} ep1, {- STUBWITH -} Unbound.unembed -> Annot ma),
    body,
    (_, {- SOLN EP -} ep2, {- STUBWITH -} Unbound.unembed -> tyA),
    tyB
    ) <-
    Unbound.unbind2Plus bnd bnd2
{- SOLN EP -} -- epsilons should match up
  guard (ep1 == ep2) {- STUBWITH -}
  -- check tyA matches type annotation on binder, if present
  maybe (return ()) (Equal.equate tyA) ma
  -- check the type of the body of the lambda expression
  (ebody, etyB) <- Env.extendCtx (Sig (S x {- SOLN EP -} ep1 {- STUBWITH -} tyA)) (checkType body tyB)
  return
    ( Lam (Unbound.bind (x, {- SOLN EP -} ep1, {- STUBWITH -} Unbound.embed (Annot (Just tyA))) ebody),
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
  (ebody, atyB) <- Env.extendCtx (Sig (S x {- SOLN EP -} ep {- STUBWITH -} atyA)) (inferType body)
  return
    ( Lam (Unbound.bind (x, {- SOLN EP -} ep, {- STUBWITH -} Unbound.embed (Annot (Just atyA))) ebody),
      Pi (Unbound.bind (x, {- SOLN EP -} ep, {- STUBWITH -} Unbound.embed atyA) atyB)
    )
tcTerm (App t1 a2) Nothing = do
  (at1, ty1) <- inferType t1
  (x, {- SOLN EP -} ep2, {- STUBWITH -} tyA, tyB) <- Equal.ensurePi ty1
{- SOLN EP -}
  guard (argEp a2 == ep2) {- STUBWITH -}
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
tcTerm (TyBool) Nothing = {- SOLN HW -} return (TyBool, Type)
{- STUBWITH Env.err [DS "unimplemented"] -}
tcTerm (LitBool b) Nothing = {- SOLN HW -} do
  return (LitBool b, TyBool)
{- STUBWITH Env.err [DS "unimplemented"] -}

tcTerm t@(If t1 t2 t3 ann1) ann2 = {- SOLN HW -} do
  ty <- matchAnnots t ann1 ann2
  (at1, _) <- checkType t1 TyBool
  nf <- Equal.whnf at1
  let ctx b = case nf of
        Var x -> [Def x (LitBool b)]
        _ -> []
  (at2, _) <- Env.extendCtxs (ctx True) $ checkType t2 ty
  (at3, _) <- Env.extendCtxs (ctx False) $ checkType t3 ty
  return (If at1 at2 at3 (Annot (Just ty)), ty)
{- STUBWITH Env.err [DS "unimplemented"] -}

tcTerm (Let bnd) ann = {- SOLN HW -} do
  ((x, Unbound.unembed -> rhs), body) <- Unbound.unbind bnd
  (arhs, aty) <- inferType rhs 
  let sig = mkSig x aty
  (abody, ty) <- Env.extendCtxs [Sig sig, Def x arhs] $
      tcTerm body ann
  when (x `elem` Unbound.toListOf Unbound.fv ty) $
    Env.err [DS "Let bound variable", DD x, DS "escapes in type", DD ty]
  return (Let (Unbound.bind (x, Unbound.embed arhs) abody), ty)
{- STUBWITH   Env.err [DS "unimplemented"] -}
{- SOLN DATA -}
-- Type constructor application
tcTerm (TCon c params) Nothing = do
  (Telescope delta, _) <- Env.lookupTCon c
  unless (length params == length delta) $
    Env.err
      [ DS "Datatype constructor",
        DD c,
        DS $
          "should have " ++ show (length delta)
            ++ "parameters, but was given",
        DD (length params)
      ]
  eparams <- tsTele params delta
  return (TCon c eparams, Type)

-- Data constructor application
-- we don't know the expected type, so see if there
-- is only one datacon of that name that takes no
-- parameters
tcTerm t@(DCon c args (Annot Nothing)) Nothing = do
  matches <- Env.lookupDConAll c
  case matches of
    [(tname, (Telescope [], ConstructorDef _ _ (Telescope deltai)))] -> do
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
      eargs <- tcArgTele args deltai
      let ty = TCon tname []
      return (DCon c eargs (Annot (Just ty)), ty)
    [_] ->
      Env.err
        [ DS "Cannot infer the parameters to data constructors.",
          DS "Add an annotation."
        ]
    _ -> Env.err [DS "Ambiguous data constructor", DS c]

-- we know the expected type of the data constructor
-- so look up its type in the context
tcTerm t@(DCon c args ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2
  case ty of
    (TCon tname params) -> do
      (Telescope delta, Telescope deltai) <- Env.lookupDCon c tname
      let numArgs = length (filter isAssnSig deltai)
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
      eargs <- tcArgTele args newTele
      return (DCon c eargs (Annot (Just ty)), ty)
    _ ->
      Env.err [DS "Unexpected type", DD ty, DS "for data constructor", DD t]

-- If we are in inference mode, then we do not use refinement
-- otherwise, we must have a typing annotation
tcTerm t@(Case scrut alts ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2
  (ascrut, sty) <- inferType scrut
  scrut' <- Equal.whnf ascrut
  whnfTCon <- Equal.ensureTCon sty
  let checkAlt (Match bnd) = do
        (pat, body) <- Unbound.unbind bnd
        -- add variables from pattern to context
        -- could fail if branch is in-accessible
        (decls, evars) <- declarePatTCon pat whnfTCon
        -- add defs to the contents from scrut = pat
        -- could fail if branch is in-accessible
        decls' <- equateWithPatTCon scrut' pat whnfTCon
        (ebody, _) <- Env.extendCtxs (decls ++ decls') $
            checkType body ty
        {- STUBWITH -}
{- SOLN DATA -}
        return (Match (Unbound.bind pat ebody))
  let pats = map (\(Match bnd) -> fst (unsafeUnbind bnd)) alts
  aalts <- mapM checkAlt alts
  exhaustivityCheck scrut' sty pats
  return (Case ascrut aalts (Annot (Just ty)), ty)
{- STUBWITH -}
{- SOLN EQUAL -}
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
    {- STUBWITH -}
{- SOLN DATA -}
    (DCon da _ _, DCon db _ _)
      | da /= db ->
        return (Contra apf (Annot (Just ty)), ty)
    {- STUBWITH -}
{- SOLN EQUAL -}
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
{- STUBWITH -}

tcTerm t@(Sigma bnd) Nothing = {- SOLN EQUAL -} do
  ((x, Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
  aa <- tcType tyA
  ba <- Env.extendCtx (Sig (mkSig x aa)) $ tcType tyB
  return (Sigma (Unbound.bind (x, Unbound.embed aa) ba), Type)
{- STUBWITH Env.err [DS "unimplemented"] -}

tcTerm t@(Prod a b ann1) ann2 = {- SOLN EQUAL -} do
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
{- STUBWITH Env.err [DS "unimplemented"] -}

tcTerm t@(LetPair p bnd ann1) ann2 = {- SOLN EQUAL -} do
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
{- STUBWITH Env.err [DS "unimplemented"] -}

tcTerm t@(PrintMe ann1) ann2 = do
  expectedTy <- matchAnnots t ann1 ann2
  gamma <- Env.getLocalCtx
  Env.warn [DS "Unmet obligation.\nContext: ", DD gamma,
        DS "\nGoal: ", DD expectedTy]
  return (PrintMe (Annot (Just expectedTy)), expectedTy)

tcTerm tm (Just ty) = do
  (atm, ty') <- inferType tm
{- SOLN EQUAL -}
  Equal.equate ty' ty
{- STUBWITH   unless (Unbound.aeq ty' ty) $ Env.err [DS "Types don't match", DD ty, DS "and", DD ty'] -}
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
  (atm, _) <- {- SOLN EP -} Env.withStage Erased {- STUBWITH -}(checkType tm Type)
  return atm

{- SOLN DATA -}
---------------------------------------------------------------------
-- helper functions for type constructor creation

-- | type check a list of type constructor arguments against a telescope
tsTele :: [Arg] -> [Assn] -> TcMonad [Arg]
tsTele = tcArgTele
  
---------------------------------------------------------------------
-- | type check a list of data constructor arguments against a telescope
tcArgTele :: [Arg] -> [Assn] -> TcMonad [Arg]
tcArgTele [] [] = return []
tcArgTele args (AssnProp (Eq tx ty) : tele) = do
  Equal.equate tx ty
  tcArgTele args tele
tcArgTele (Arg ep1 tm : terms) (AssnSig sig : tele') | ep1 == sigEp sig = do
  (etm, ety) <- Env.withStage ep1 $ checkType tm (sigType sig)
  tele'' <- doSubst [(sigName sig, etm)] tele'
  eterms <- tcArgTele terms tele''
  return $ Arg ep1 etm : eterms
tcArgTele (Arg ep1 _ : _) (AssnSig sig2 : _) =
  Env.err
    [ DD ep1,
      DS "argument provided when",
      DD (sigEp sig2),
      DS "argument was expected"
    ]
tcArgTele [] _ =
  Env.err [DD "Too few arguments provided."]
tcArgTele _ [] =
  Env.err [DD "Too many arguments provided."]

-- | Substitute a list of terms for the variables bound in a telescope
-- This is used to instantiate the parameters of a data constructor
-- to find the types of its arguments.
-- The first argument should only contain 'Runtime' type declarations.
substTele :: [Assn] -> [Arg] -> [Assn] -> TcMonad [Assn]
substTele tele args delta = doSubst (mkSubst tele (map unArg args)) delta
  where
    mkSubst [] [] = []
    mkSubst (AssnSig (S x Runtime _) : tele') (tm : tms) =
      (x, tm) : mkSubst tele' tms
    mkSubst _ _ = error "Internal error: substTele given illegal arguments"

-- From a constraint, fetch all declarations
-- derived from unifying the two terms
-- If the terms are not unifiable, throw an error
-- Note: we could do better with our unification
amb :: Term -> Bool
amb (App t1 t2) = True
amb (Pi _) = True
amb (If _ _ _ _) = True
amb (Sigma _) = True
amb (LetPair _ _ _) = True
amb (Let _) = True
amb (Case _ _ _) = True
amb _ = False

constraintToDecls :: Term -> Term -> TcMonad [Decl]
constraintToDecls tx ty = do
  txnf <- Equal.whnf tx
  tynf <- Equal.whnf ty
  if (Unbound.aeq txnf tynf)
    then return []
    else case (txnf, tynf) of
      (Var y, yty) -> return [Def y yty]
      (yty, Var y) -> return [Def y yty]
      (TCon s1 tms1, TCon s2 tms2)
        | s1 == s2 -> matchArgs tms1 tms2
      (Prod a1 a2 _, Prod b1 b2 _) -> matchTerms [a1, a2] [b1, b2]
      (TyEq a1 a2, TyEq b1 b2) -> matchTerms [a1, a2] [b1, b2]
      (DCon s1 a1s _, DCon s2 a2s _)
        | s1 == s2 -> matchArgs a1s a2s
      _ ->
        if amb txnf || amb tynf
          then return []
          else Env.err [DS "Cannot equate", DD txnf, DS "and", DD tynf]
  where
    matchTerms ts1 ts2 = matchArgs (map (Arg Runtime) ts1) (map (Arg Runtime) ts2)
    matchArgs (Arg _ t1 : a1s) (Arg _ t2 : a2s) = do
      ds <- constraintToDecls t1 t2
      ds' <- matchArgs a1s a2s
      return $ ds ++ ds'
    matchArgs [] [] = return []
    matchArgs _ _ = Env.err [DS "internal error (constraintToDecls)"]

-- Propagate the given substitution through the telescope, potentially
-- reworking the constraints.
doSubst :: [(TName, Term)] -> [Assn] -> TcMonad [Assn]
doSubst ss [] = return []
doSubst ss (AssnProp (Eq tx ty) : tele') = do
  let tx' = Unbound.substs ss tx
  let ty' = Unbound.substs ss ty
  -- (_decls, tsf) <- match tx' ty'
  decls <- constraintToDecls tx' ty'
  tele <- Env.extendCtxs decls $ (doSubst ss tele')
  return $ (AssnProp (Eq tx' ty') : tele)
doSubst ss (AssnSig sig : tele') = do
  tynf <- Equal.whnf (Unbound.substs ss (sigType sig))
  let sig' = sig{sigType = tynf}
  tele'' <- doSubst ss tele'
  return $ AssnSig sig' : tele''

-----------------------------------------------------------
-- helper functions for checking pattern matching

forgetTCon :: Equal.WhnfTCon -> Type
forgetTCon (Equal.WhnfTCon n ps) = 
  case n of
    "Bool" -> TyBool
    "One" -> TyUnit
    _ -> TCon n ps

-- | Create a binding in the context for each of the variables in
-- the pattern.
-- Also returns the erased variables so that they can be checked
declarePat :: Pattern -> Epsilon -> Type -> TcMonad ([Decl], [TName])
declarePat (PatVar x) ep y = return ([Sig (S x ep y)], [])
declarePat pat Runtime ty = do 
  whnfTCon <- Equal.ensureTCon ty
  declarePatTCon pat whnfTCon
declarePat pat Erased _ty =
  Env.err [DS "Cannot pattern match erased arguments in pattern ", DD pat]

declarePatTCon :: Pattern -> Equal.WhnfTCon -> TcMonad ([Decl], [TName])
declarePatTCon (PatCon d pats) (Equal.WhnfTCon c params) = do
  (Telescope delta, Telescope deltai) <- Env.lookupDCon d c
  tele <- substTele delta params deltai
  declarePats d pats tele
declarePatTCon (PatBool _) (Equal.WhnfTCon "Bool" []) = do
  return ([],[])
declarePatTCon PatUnit (Equal.WhnfTCon "One" []) = do
  return ([],[])
declarePatTCon (PatVar x) y = 
  Env.err [DS "Internal error: declarePatTCon, found ", DD (PatVar x)]
declarePatTCon pat ty =
  Env.err [DS "Cannot match pattern", DD pat, DS "with type", DD (forgetTCon ty)]


declarePats :: DCName -> [(Pattern, Epsilon)] -> [Assn] -> TcMonad ([Decl], [TName])
declarePats dc [] [] = return ([], [])
declarePats dc pats (AssnProp (Eq tx ty) : tele) = do
  new_decls <- constraintToDecls tx ty
  (decls, names) <- Env.extendCtxs new_decls $ declarePats dc pats tele
  return (new_decls ++ decls, names)
declarePats dc ((pat, _) : pats) (AssnSig (S x ep ty) : tele) = do
  (ds1, v1) <- declarePat pat ep ty
  tm <- pat2Term pat ty
  (ds2, v2) <- declarePats dc pats (Unbound.subst x tm tele)
  return ((ds1 ++ ds2), (v1 ++ v2))
declarePats dc [] _ = Env.err [DS "Not enough patterns in match for data constructor", DD dc]
declarePats dc pats [] = Env.err [DS "Too many patterns in match for data constructor", DD dc]

-- | Convert a pattern to an (annotated) term so that we can substitute it for
-- variables in telescopes. Because data constructors must be annotated with
-- their types, we need to have the expected type of the pattern available.
pat2Term :: Pattern -> Type -> TcMonad Term
pat2Term (PatCon dc pats) ty@(TCon n params) = do
  (Telescope delta, Telescope deltai) <- Env.lookupDCon dc n
  tele <- substTele delta params deltai
  args <- pats2Terms pats tele
  return (DCon dc args (Annot (Just ty)))
  where
    pats2Terms :: [(Pattern, Epsilon)] -> [Assn] -> TcMonad [Arg]
    pats2Terms [] [] = return []
    pats2Terms ps (AssnProp (Eq tx' ty') : tele') = do
      decls <- constraintToDecls tx' ty'
      Env.extendCtxs decls $ pats2Terms ps tele'
    pats2Terms ((p, _) : ps) (AssnSig (S x ep ty1) : d) = do
      t <- pat2Term p ty1
      ts <- pats2Terms ps (Unbound.subst x t d)
      return (Arg ep t : ts)
    pats2Terms _ _ = Env.err [DS "Invalid number of args to pattern", DD dc]
pat2Term (PatBool b) ty = pure $ LitBool b
pat2Term (PatUnit) ty = pure $ LitUnit
pat2Term (PatVar x) ty = return (Var x)
pat2Term _ _ = Env.err [DS "Internal error: pat2Term"]

-- | Create a list of variable definitions from the scrutinee
-- of a case expression and the pattern in a branch. Scrutinees
-- that are not variables or constructors applied to vars may not
-- produce any equations.
equateWithPat :: Term -> Pattern -> Type -> TcMonad [Decl]
equateWithPat (Var x) pat ty = do
  tm <- pat2Term pat ty
  return [Def x tm]
equateWithPat tm pat ty = do 
  whnfTCon <- Equal.ensureTCon ty
  equateWithPatTCon tm pat whnfTCon

equateWithPatTCon :: Term -> Pattern -> Equal.WhnfTCon -> TcMonad [Decl]
equateWithPatTCon (Var x) pat ty = do
  tm <- pat2Term pat (forgetTCon ty)
  return [Def x tm]
equateWithPatTCon (LitBool b) (PatBool b') (Equal.WhnfTCon "Bool" []) | b == b' = pure []
equateWithPatTCon LitUnit PatUnit (Equal.WhnfTCon "One" []) = pure []
equateWithPatTCon (DCon dc args _) (PatCon dc' pats) (Equal.WhnfTCon n params)
  | dc == dc' = do
    (Telescope delta, Telescope deltai) <- Env.lookupDCon dc n
    tele <- substTele delta params deltai
    let eqWithPats :: [Term] -> [(Pattern, Epsilon)] -> [Assn] -> TcMonad [Decl]
        eqWithPats [] [] [] = return []
        eqWithPats ts ps (AssnProp (Eq tx ty) : tl) = do
          decls <- constraintToDecls tx ty
          Env.extendCtxs decls $ eqWithPats ts ps tl
        eqWithPats (t : ts) ((p, _) : ps) (AssnSig (S x _ ty) : tl) = do
          t' <- Equal.whnf t
          decls <- equateWithPat t' p ty
          decls' <- eqWithPats ts ps (Unbound.subst x t' tl)
          return (decls ++ decls')
        eqWithPats _ _ _ =
          Env.err [DS "Invalid number of args to pattern", DD dc]
    eqWithPats (map unArg args) pats tele
equateWithPatTCon (DCon dc args _) (PatCon dc' pats) (Equal.WhnfTCon n params) = do
  Env.warn
    [ DS "The case for",
      DD dc',
      DS "is unreachable.",
      DS "However, this implementation cannot yet allow it",
      DS "to be omitted."
    ]
    >> return []
equateWithPatTCon _ _ _ = return []

-- | Check all of the types contained within a telescope
-- returns a telescope where all of the types have been annotated
tcTypeTele :: [Assn] -> TcMonad [Assn]
tcTypeTele [] = return []
tcTypeTele (AssnProp (Eq tm1 tm2) : tl) = do
  (tm1', ty1) <- Env.withStage Erased $ inferType tm1
  (tm2', _) <- Env.withStage Erased $ checkType tm2 ty1
  decls <- constraintToDecls tm1' tm2'
  tele' <- Env.extendCtxs decls $ tcTypeTele tl
  return (AssnProp (Eq tm1' tm2') : tele')
tcTypeTele (AssnSig sig : tl) = do
  ty' <- tcType (sigType sig)
  let sig' = sig{sigType = ty'}
  tele' <- Env.extendCtx (Sig sig') $ tcTypeTele tl
  return (AssnSig sig' : tele')

{- STUBWITH -}

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

{- SOLN DATA -}
-- rule Decl_data
tcEntry (Data t (Telescope delta) cs) =
  do
    -- Check that the telescope for the datatype definition is well-formed
    edelta <- tcTypeTele delta
    ---- check that the telescope provided
    ---  for each data constructor is wellfomed, and elaborate them
    let elabConstructorDef defn@(ConstructorDef pos d (Telescope tele)) =
          Env.extendSourceLocation pos defn $
            Env.extendCtx (DataSig t (Telescope edelta)) $
              Env.extendCtxTele edelta $ do
                etele <- tcTypeTele tele
                return (ConstructorDef pos d (Telescope etele))
    ecs <- mapM elabConstructorDef cs
    -- Implicitly, we expect the constructors to actually be different...
    let cnames = map (\(ConstructorDef _ c _) -> c) cs
    unless (length cnames == length (nub cnames)) $
      Env.err [DS "Datatype definition", DD t, DS "contains duplicated constructors"]
    -- finally, add the datatype to the env and perform action m
    return $ AddCtx [Data t (Telescope edelta) ecs]
tcEntry (DataSig _ _) = Env.err [DS "internal construct"]
tcEntry (RecDef _ _) = Env.err [DS "internal construct"]

{- STUBWITH tcEntry _ = Env.err "unimplemented" -}

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

{- SOLN DATA -}
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
exhaustivityCheck scrut TyUnit [PatUnit] = return ()
exhaustivityCheck scrut TyBool [PatBool b] = return ()
exhaustivityCheck scrut ty pats = do
  (Equal.WhnfTCon tcon tys) <- Equal.ensureTCon ty
  (Telescope delta, mdefs) <- Env.lookupTCon tcon
  case mdefs of
    Just datacons -> loop pats datacons
      where
        loop [] [] = return ()
        loop [] dcons = do
          l <- checkImpossible dcons
          if null l
            then return ()
            else Env.err $ [DS "Missing case for "] ++ map DD l
        loop [PatUnit] [ConstructorDef _ "tt" (Telescope [])]  = do
          return ()
        loop (PatUnit : _) _ = Env.err [DS "loop PatUnit"]
        loop (PatBool b : pats') dcons = do
          (cd@(ConstructorDef _ _ _, dcons')) <- removeDcon (show b) dcons
          loop pats' dcons'
        loop ((PatVar x) : _) dcons = return ()
        loop ((PatCon dc args) : pats') dcons = do
          (cd@(ConstructorDef _ _ (Telescope tele), dcons')) <- removeDcon dc dcons
          tele' <- substTele delta tys tele
          let (aargs, pats'') = relatedPats dc pats'
          checkSubPats dc tele' (args : aargs)
          loop pats'' dcons'

        -- make sure that the given list of constructors is impossible
        -- in the current environment
        checkImpossible :: [ConstructorDef] -> TcMonad [DCName]
        checkImpossible [] = return []
        checkImpossible cd@(ConstructorDef _ dc (Telescope tele) : rest) = do
          this <-
            ( do
                tele' <- substTele delta tys tele
                _ <- tcTypeTele tele'
                return [dc]
              )
              `catchError` (\_ -> return [])
          others <- checkImpossible rest
          return (this ++ others)
    Nothing ->
      Env.err [DS "Cannot determine constructors of", DD ty]

-- this could be because the scrutinee is not unifiable with the pattern
-- or because the constraints on the pattern are not satisfiable

-- | Given a particular data constructor name and a list of data
-- constructor definitions, pull the definition out of the list and
-- return it paired with the remainder of the list.
removeDcon ::
  DCName ->
  [ConstructorDef] ->
  TcMonad (ConstructorDef, [ConstructorDef])
removeDcon dc (cd@(ConstructorDef _ dc' _) : rest)
  | dc == dc' =
    return (cd, rest)
removeDcon dc (cd1 : rest) = do
  (cd2, rr) <- removeDcon dc rest
  return (cd2, cd1 : rr)
removeDcon dc [] = Env.err [DS $ "Internal error: Can't find" ++ show dc]

-- | Given a particular data constructor name and a list of patterns,
-- pull out the subpatterns that occur as arguments to that data
-- constructor and return them paired with the remaining patterns.
relatedPats :: DCName -> [Pattern] -> ([[(Pattern, Epsilon)]], [Pattern])
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
checkSubPats :: DCName -> [Assn] -> [[(Pattern, Epsilon)]] -> TcMonad ()
checkSubPats dc [] _ = return ()
checkSubPats dc (AssnProp _ : tele) patss = checkSubPats dc tele patss
checkSubPats dc (AssnSig _ : tele) patss
  | length patss > 0 && (all ((> 0) . length) patss) = do
    let hds = map (fst . head) patss
    let tls = map tail patss
    case hds of
      (PatVar _ : []) -> checkSubPats dc tele tls
      _ -> Env.err [DS "All subpatterns must be variables in this version."]
checkSubPats dc t ps =
  Env.err [DS "Internal error in checkSubPats", DD dc, DS (show ps)]

{- STUBWITH -}
