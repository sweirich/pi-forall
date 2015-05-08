{- PiForall language -}

{-# LANGUAGE ViewPatterns, TypeSynonymInstances, 
             ExistentialQuantification, NamedFieldPuns, 
             ParallelListComp, FlexibleContexts, ScopedTypeVariables, 
             TupleSections, FlexibleInstances #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | The main routines for type-checking 
module TypeCheck(tcModules, inferType, checkType) where

import Syntax
import Environment
import PrettyPrint
import Equal

import Unbound.LocallyNameless hiding (Data, Refl)
import Control.Applicative 
import Control.Monad.Except
import Text.PrettyPrint.HughesPJ
import Data.Maybe
import Data.List(nub)
import Unbound.LocallyNameless.Ops (unsafeUnbind)



-- | Infer the type of a term, producing an annotated version of the 
-- term (whose type can *always* be inferred).
inferType :: Term -> TcMonad (Term,Type)
inferType t = tcTerm t Nothing

-- | Check that the given term has the expected type.  
-- The provided type does not necessarily need to be in whnf, but it should be
-- elaborated (i.e. already checked to be a good type).
checkType :: Term -> Type -> TcMonad (Term, Type)
checkType tm expectedTy = do
  nf <- whnf expectedTy
  tcTerm tm (Just nf)

-- | check a term, producing an elaborated term
-- where all of the type annotations have been filled in
-- The second argument is 'Nothing' in inference mode and 
-- an expected type (must be in whnf) in checking mode
tcTerm :: Term -> Maybe Type -> TcMonad (Term,Type)

tcTerm t@(Var x) Nothing = do
  ty  <- lookupTy x
  return (t,ty)
  
tcTerm t@(Type) Nothing = return (t,Type)  
  
tcTerm (Pi bnd) Nothing = do 
  ((x, unembed -> tyA), tyB) <- unbind bnd
  atyA <- tcType tyA 
  atyB <- extendCtx (Sig x atyA) $ tcType tyB
  return (Pi (bind (x, embed atyA) atyB), Type) 
      
-- Check the type of a function    
tcTerm (Lam bnd) (Just (Pi bnd2)) = do
  -- unbind the variables in the lambda expression and pi type
  ((x,unembed -> Annot ma), body, 
   (_, unembed -> tyA), tyB) <- unbind2Plus bnd bnd2
  -- check tyA matches type annotation on binder, if present
  maybe (return ()) (equate tyA) ma
  -- check the type of the body of the lambda expression
  (ebody, etyB) <- extendCtx (Sig x tyA) (checkType body tyB)
  return (Lam (bind (x, embed (Annot (Just tyA))) ebody), 
          Pi bnd2)  
tcTerm (Lam _) (Just nf) = 
  err [DS "Lambda expression has a function type, not", DD nf]

-- infer the type of a lambda expression, when an annotation
-- on the binder is present
tcTerm (Lam bnd) Nothing = do
  ((x,(unembed -> Annot annot)), body) <- unbind bnd 
  tyA  <- maybe (err [DS "Must annotate lambda"]) (return) annot
  -- check that the type annotation is well-formed
  atyA <- tcType tyA
  -- infer the type of the body of the lambda expression
  (ebody, atyB) <- extendCtx (Sig x atyA) (inferType body)
  return (Lam (bind (x, embed (Annot (Just atyA))) ebody), 
          Pi  (bind (x, embed atyA) atyB))  

tcTerm (App t1 t2) Nothing = do  
  (at1, ty1)    <- inferType t1  
  (x, tyA, tyB) <- ensurePi ty1 
  (at2, ty2)    <- checkType t2 tyA
  let result = (App at1 at2, subst x at2 tyB)
  return result
                     
-- Check the type of a function    
tcTerm (ErasedLam bnd) (Just (ErasedPi bnd2)) = do
  -- unbind the variables in the lambda expression and pi type
  ((x,unembed -> Annot ma), body, 
   (_, unembed -> tyA), tyB) <- unbind2Plus bnd bnd2
  -- check tyA matches type annotation on binder, if present
  maybe (return ()) (equate tyA) ma
  -- check the type of the body of the lambda expression
  (ebody, etyB) <- extendCtx (Sig x tyA) (checkType body tyB)
  -- make sure that an 'erased' variable isn't used
  when (x `elem` fv (erase ebody)) $
    err [DS "Erased variable", DD x, 
         DS "used in body"]
  return (ErasedLam (bind (x, embed (Annot (Just tyA))) ebody), 
          ErasedPi bnd2)    
tcTerm (ErasedLam _) (Just nf) = 
  err [DS "Lambda expression has a function type, not", DD nf]    
    
-- infer the type of a lambda expression, when an annotation
-- on the binder is present
tcTerm (ErasedLam bnd) Nothing = do
  ((x,(unembed -> Annot annot)), body) <- unbind bnd 
  tyA <- maybe (err [DS "Must annotate lambda"]) (return) annot
  -- check that the type annotation is well-formed
  atyA <- tcType tyA
  -- infer the type of the body of the lambda expression
  (ebody, atyB) <- extendCtx (Sig x atyA) (inferType body)
    -- make sure that an 'erased' variable isn't used
  when (x `elem` fv (erase ebody)) $
    err [DS "Erased variable", DD x, 
         DS "used in body"]
  return (ErasedLam (bind (x, embed (Annot (Just atyA))) ebody), 
          ErasedPi  (bind (x, embed atyA) atyB))  

tcTerm (ErasedApp t1 t2) Nothing = do  
  (at1, ty1)    <- inferType t1  
  (x, tyA, tyB) <- ensureErasedPi ty1 
  (at2, ty2)    <- checkType t2 tyA
  let result = (ErasedApp at1 at2, subst x at2 tyB)
  return result
  
tcTerm (ErasedPi bnd) Nothing = do 
  ((x, unembed -> tyA), tyB) <- unbind bnd
  atyA <- tcType tyA 
  atyB <- extendCtx (Sig x atyA) $ tcType tyB
  return (ErasedPi (bind (x, embed atyA) atyB), Type)   


tcTerm (Ann tm ty) Nothing = do
  ty'         <- tcType ty
  (tm', ty'') <- checkType tm ty'
  
  return (tm', ty'')   
  
tcTerm (Pos p tm) mTy = 
  extendSourceLocation p tm $ tcTerm tm mTy
  
tcTerm (Paren tm) mTy = tcTerm tm mTy
  
tcTerm t@(TrustMe ann1) ann2 = do  
  expectedTy <- matchAnnots t ann1 ann2
  return (TrustMe (Annot (Just expectedTy)), expectedTy)

tcTerm (TyUnit) Nothing = return (TyUnit, Type)

tcTerm (LitUnit) Nothing = return (LitUnit, TyUnit)

tcTerm (TyBool) Nothing = return (TyBool,Type)
  
  
tcTerm (LitBool b) Nothing = do
  return (LitBool b, TyBool)
  
  
tcTerm t@(If t1 t2 t3 ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2   
  (at1,_) <- checkType t1 TyBool
  nf <- whnf at1 
  let ctx b = case nf of 
        Var x -> [Def x (LitBool b)]
        _     -> []
  (at2, _) <- extendCtxs (ctx True) $ checkType t2 ty
  (at3, _) <- extendCtxs (ctx False) $ checkType t3 ty
  return (If at1 at2 at3 (Annot (Just ty)), ty)
        
  
tcTerm (Let bnd) ann = do       
  ((x,unembed->rhs),body) <- unbind bnd
  (arhs,aty) <- inferType rhs    
  (abody,ty) <- extendCtxs [Sig x aty, Def x arhs] $ 
                tcTerm body ann
  when (x `elem` fv ty) $
    err [DS "Let bound variable", DD x, DS "escapes in type", DD ty]  
  return (Let (bind (x,embed arhs) abody), ty)
          
  
-- Type constructor application      
tcTerm (TCon c params) Nothing = do   
  (delta, _) <- lookupTCon c 
  unless (length params == teleLength delta) $
    err [DS "Datatype constructor", DD c, 
         DS $ "should have " ++ show (teleLength delta) ++
         "parameters, but was given", DD (length params)]
  eparams <- tsTele params delta
  return (TCon c eparams, Type)
  
-- Data constructor application  
-- we don't know the expected type, so see if there
-- is only one datacon of that name that takes no
-- parameters
tcTerm t@(DCon c args (Annot Nothing)) Nothing = do
  matches <- lookupDConAll c 
  case matches of
    [(tname,(Empty,ConstructorDef _ _ deltai))] -> do
      let numArgs   = teleLength deltai
      unless (length args == numArgs) $
            err [DS "Constructor", DS c,
                 DS "should have", DD numArgs, 
                 DS "data arguments, but was given", 
                 DD (length args), DS "arguments."]
      eargs  <- tcArgTele args deltai
      let ty = TCon tname []
      return (DCon c eargs (Annot (Just ty)),ty)
    [_] -> err [DS "Cannot infer the parameters to data constructors.",
                DS "Add an annotation."]
    _ -> err [DS "Ambiguous data constructor", DS c]       
  
-- we know the expected type of the data constructor
-- so look up its type in the context
tcTerm t@(DCon c args ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2
  case ty of
    (TCon tname params) -> do  
      (delta, deltai) <- lookupDCon c tname
      let numArgs   = teleLength deltai
      unless (length args == numArgs) $
        err [DS "Constructor", DS c,
             DS "should have", DD numArgs, 
             DS "data arguments, but was given", 
             DD (length args), DS "arguments."]
      newTele <- substTele delta params deltai
      eargs   <- tcArgTele args newTele
      return (DCon c eargs (Annot (Just ty)), ty) 
    _ -> 
      err [DS "Unexpected type", DD ty, DS "for data constructor", DD t]
  
-- If we are in inference mode, then 
--      we do not use refinement        
-- otherwise, we must have a typing annotation        
tcTerm t@(Case scrut alts ann1) ann2 = do  
  ty <- matchAnnots t ann1 ann2
  (ascrut, sty) <- inferType scrut
  scrut' <- whnf ascrut
  (n, params) <- ensureTCon sty
  let checkAlt (Match bnd) = do
         (pat, body) <- unbind bnd
         -- add variables from pattern to context
         -- could fail if branch is in-accessible
         (decls, evars) <- declarePat pat Runtime (TCon n params)
         -- add defs to the contents from scrut = pat
         -- could fail if branch is in-accessible
         decls'     <- equateWithPat scrut' pat (TCon n params)
         (ebody, _) <- extendCtxs (decls ++ decls') $ 
                          checkType body ty
             
         -- make sure 'erased' components aren't used 
         when (any (`elem` (fv (erase ebody))) evars) $
           err [DS "Erased variable bound in match used"]
           
         return (Match (bind pat ebody))
  let pats = map (\(Match bnd) -> fst (unsafeUnbind bnd)) alts         
  aalts <- mapM checkAlt alts
  exhaustivityCheck scrut' sty pats
  return (Case ascrut aalts (Annot (Just ty)), ty)
  
  
tcTerm (TyEq a b) Nothing =  do
  (aa,aTy) <- inferType a 
  (ab,bTy) <- checkType b aTy
  return (TyEq aa ab, Type) 


tcTerm t@(Refl ann1) ann2 =  do
  ty <- matchAnnots t ann1 ann2
  case ty of 
    (TyEq a b) -> do
      equate a b
      return (Refl (Annot (Just ty)), ty)  
    _ -> err [DS "refl annotated with", DD ty]
  
tcTerm t@(Subst tm p ann1) ann2 =  do
  ty <- matchAnnots t ann1 ann2
  -- infer the type of the proof p
  (apf, tp) <- inferType p 
  -- make sure that it is an equality between m and n
  (m,n)     <- ensureTyEq tp
  -- if either side is a variable, add a definition to the context 
  edecl <- do 
    m'        <- whnf m
    n'        <- whnf n
    case (m',n') of 
        (Var x, _) -> return [Def x n']
        (_, Var y) -> return [Def y m']
        (_,_) -> return [] 
        
  pdecl <- do
    p'        <- whnf apf
    case p' of 
      (Var x) -> return [Def x (Refl (Annot (Just tp)))]
      _       -> return []
  let refined = extendCtxs (edecl ++ pdecl)
  (atm, _) <- refined $ checkType tm ty
  return (Subst atm apf (Annot (Just ty)), ty)
    
tcTerm t@(Contra p ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2
  (apf, ty') <- inferType p 
  (a,b) <- ensureTyEq ty'
  a' <- whnf a
  b' <- whnf b
  case (a',b') of 
    
    (DCon da _ _, DCon db _ _) | da /= db -> 
      return (Contra apf (Annot (Just ty)), ty)
      
    (LitBool b1, LitBool b2) | b1 /= b2 ->
      return (Contra apf (Annot (Just ty)), ty)
    (_,_) -> err [DS "I can't tell that", DD a, DS "and", DD b,
                  DS "are contradictory"]

    
tcTerm t@(Sigma bnd) Nothing = do        
  ((x,unembed->tyA),tyB) <- unbind bnd
  aa <- tcType tyA
  ba <- extendCtx (Sig x aa) $ tcType tyB
  return (Sigma (bind (x,embed aa) ba), Type)
  
  
tcTerm t@(Prod a b ann1) ann2 = do
  ty <- matchAnnots t ann1 ann2
  case ty of
     (Sigma bnd) -> do
      ((x, unembed-> tyA), tyB) <- unbind bnd
      (aa,_) <- checkType a tyA
      (ba,_) <- extendCtxs [Sig x tyA, Def x aa] $ checkType b tyB
      return (Prod aa ba (Annot (Just ty)), ty)
     _ -> err [DS "Products must have Sigma Type", DD ty, 
                   DS "found instead"]
    
        
tcTerm t@(Pcase p bnd ann1) ann2 = do   
  ty <- matchAnnots t ann1 ann2
  (apr, pty) <- inferType p
  pty' <- whnf pty
  case pty' of 
    Sigma bnd' -> do
      ((x,unembed->tyA),tyB) <- unbind bnd'
      ((x',y'),body) <- unbind bnd
      let tyB' = subst x (Var x') tyB
      nfp  <- whnf apr
      let ctx = case nfp of 
            Var x0 -> [Def x0 (Prod (Var x') (Var y') 
                              (Annot (Just pty')))]
            _     -> []              
      (abody, bTy) <- extendCtxs ([Sig x' tyA, Sig y' tyB'] ++ ctx) $
        checkType body ty
      return (Pcase apr (bind (x',y') abody) (Annot (Just ty)), bTy)
    _ -> err [DS "Scrutinee of pcase must have Sigma type"]

      
tcTerm tm (Just ty) = do
  (atm, ty') <- inferType tm 
  equate ty' ty

  return (atm, ty)                     
  



---------------------------------------------------------------------
-- helper functions for type checking 
      
-- | Merge together two sources of type information
-- The first annotation is assumed to come from an annotation on 
-- the syntax of the term itself, the second as an argument to 
-- 'checkType'.  
matchAnnots :: Term -> Annot -> Maybe Type -> TcMonad Type
matchAnnots e (Annot Nothing) Nothing     = err 
 [DD e, DS "requires annotation"]
matchAnnots e (Annot Nothing) (Just t)    = return t
matchAnnots e (Annot (Just t)) Nothing    = do
  at <- tcType t                                          
  return at
matchAnnots e (Annot (Just t1)) (Just t2) = do
  at1 <- tcType t1                                          
  equate at1 t2
  return at1
  
-- | Make sure that the term is a type (i.e. has type 'Type') 
tcType :: Term -> TcMonad Term
tcType tm = do
  (atm, _) <- checkType tm Type
  return atm
                      
                    
---------------------------------------------------------------------
-- helper functions for type constructor creation

-- | type check a list of type constructor arguments against a telescope
tsTele :: [Term] -> Telescope -> TcMonad [Term]
tsTele tms tele = do
  args <- tcArgTele (map (Arg Runtime) tms) tele
  return (map unArg args)

---------------------------------------------------------------------
-- helper functions for data constructor creation

-- | calculate the length of a telescope
teleLength :: Telescope -> Int
teleLength Empty = 0
teleLength (Constraint _ _ tele) = teleLength tele
teleLength (Cons _ _ _ tele) = 1 + teleLength tele

-- | type check a list of data constructor arguments against a telescope
tcArgTele ::  [Arg] -> Telescope -> TcMonad [Arg]
tcArgTele [] Empty = return []
tcArgTele args (Constraint tx ty tele) = do
  equate tx ty
  tcArgTele args tele
tcArgTele (Arg ep1 tm:terms) (Cons ep2 x ty tele') | ep1 == ep2 = do
  (etm, ety) <- checkType tm ty
  tele'' <- doSubst [(x,etm)] tele'
  eterms <- tcArgTele terms tele''
  return $ Arg ep1 etm:eterms
tcArgTele (Arg ep1 _ : _) (Cons ep2 _ _ _) = 
  err [DD ep1, DS "argument provided when", 
       DD ep2, DS "argument was expected"]
tcArgTele [] _ =  
  err [DD "Too few arguments provided."]
tcArgTele _ Empty =  
  err [DD "Too many arguments provided."]

-- | Substitute a list of terms for the variables bound in a telescope
-- This is used to instantiate the parameters of a data constructor
-- to find the types of its arguments.
-- The first argument should only contain 'Runtime' type declarations.
substTele :: Telescope -> [ Term ] -> Telescope -> TcMonad Telescope
substTele tele args delta = doSubst (mkSubst tele args) delta where
  mkSubst Empty [] = []
  mkSubst (Cons Runtime x _ tele') (tm : tms) = 
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
amb (Pcase _ _ _ ) = True
amb (Let _ ) = True
amb (ErasedLam _) = True
amb (ErasedPi _) = True
amb (ErasedApp _ _) = True
amb (Case _ _ _) = True
amb _ = False
  
constraintToDecls :: Term -> Term -> TcMonad [Decl]
constraintToDecls tx ty = do
  txnf  <- whnf tx
  tynf  <- whnf ty
  if (aeq txnf tynf) then return []
    else case (txnf, tynf) of
    (Var y, yty) -> return [Def y yty]
    (yty, Var y) -> return [Def y yty]
    (TCon s1 tms1, TCon s2 tms2) 
        | s1 == s2 -> matchTerms tms1 tms2
    (Prod a1 a2 _, Prod b1 b2 _) -> matchTerms [a1,a2] [b1,b2]
    (TyEq a1 a2, TyEq b1 b2) -> matchTerms [a1,a2] [b1,b2]
    (DCon s1 a1s _,  DCon s2 a2s _)
        | s1 == s2 -> matchArgs a1s a2s
    _ -> 
      if amb txnf || amb tynf 
      then return [] 
      else err [DS "Cannot equate", DD txnf, DS "and", DD tynf] 
           
 where
    matchTerms ts1 ts2 = matchArgs (map (Arg Runtime) ts1) (map (Arg Runtime) ts2)
    matchArgs (Arg _ t1 : a1s) (Arg _ t2 : a2s) = do
        ds   <- constraintToDecls t1 t2
        ds'  <- matchArgs a1s a2s
        return $ ds ++ ds'
    matchArgs [] [] = return []
    matchArgs _ _   = err [DS "internal error (constraintToDecls)"]


-- Propagate the given substitution through the telescope, potentially 
-- reworking the constraints.
doSubst :: [(TName,Term)] -> Telescope -> TcMonad Telescope
doSubst ss Empty = return Empty
doSubst ss (Constraint tx ty tele') = do
  let tx' = substs ss tx
  let ty' = substs ss ty
  -- (_decls, tsf) <- match tx' ty'
  decls <- constraintToDecls tx' ty'
  tele  <- extendCtxs decls $ (doSubst ss tele')
  return $ (Constraint tx' ty' tele)
doSubst ss (Cons ep x ty tele') = do
  tynf <- whnf (substs ss ty)
  tele'' <- doSubst ss tele'  
  return $ Cons ep x tynf tele''


-----------------------------------------------------------
-- helper functions for checking pattern matching
           
-- | Create a binding in the context for each of the variables in 
-- the pattern. 
-- Also returns the erased variables so that they can be checked
declarePat :: Pattern -> Epsilon -> Type -> TcMonad ([Decl], [TName])
declarePat (PatVar x) Runtime y = return ([Sig x y],[])
declarePat (PatVar x) Erased  y = return ([Sig x y],[x])
declarePat (PatCon d pats) Runtime (TCon c params) = do
  (delta, deltai) <- lookupDCon d c
  tele <- substTele delta params deltai   
  declarePats d pats tele
declarePat (PatCon d pats) Erased (TCon c params) = 
  err [DS "Cannot pattern match erased arguments"]
declarePat pat ep ty = 
  err [DS "Cannot match pattern", DD pat, DS "with type", DD ty]
  
declarePats :: DCName -> [(Pattern,Epsilon)] -> Telescope -> TcMonad ([Decl],[TName])
declarePats dc [] Empty = return ([],[])
declarePats dc pats (Constraint tx ty tele) = do
  new_decls <- constraintToDecls tx ty
  (decls, names) <- extendCtxs new_decls $ declarePats dc pats tele
  return (new_decls ++ decls, names)
declarePats dc ((pat,_):pats) (Cons ep x ty tele) = do
  (ds1,v1) <- declarePat pat ep ty  
  tm <- pat2Term pat ty
  (ds2,v2) <- declarePats dc pats (subst x tm tele)
  return ((ds1 ++ ds2),(v1 ++ v2))
declarePats dc [] _     = err [DS "Not enough patterns in match for data constructor", DD dc]
declarePats dc pats  Empty = err [DS "Too many patterns in match for data constructor", DD dc]
           
                       
-- | Convert a pattern to an (annotated) term so that we can substitute it for
-- variables in telescopes. Because data constructors must be annotated with
-- their types, we need to have the expected type of the pattern available.
pat2Term :: Pattern -> Type -> TcMonad Term
pat2Term (PatCon dc pats) ty@(TCon n params) = do
  (delta, deltai) <- lookupDCon dc n
  tele <- substTele delta params deltai
  args <- pats2Terms pats tele 
  return (DCon dc args (Annot (Just ty)))
     where
      pats2Terms :: [(Pattern,Epsilon)] -> Telescope -> TcMonad [Arg]
      pats2Terms [] Empty = return []
      pats2Terms ps (Constraint tx' ty' tele') =  do
        decls <- constraintToDecls tx' ty'
        extendCtxs decls $ pats2Terms ps tele'
      pats2Terms ((p,_) : ps) (Cons ep x ty1 d) = do
        ty' <- whnf ty1
        t <- pat2Term p ty'
        ts <- pats2Terms ps (subst x t d)
        return (Arg ep t : ts)
      pats2Terms _ _ = err [DS "Invalid number of args to pattern", DD dc]
pat2Term (PatCon _ _) ty = error "Internal error: should be a tcon"
pat2Term (PatVar x) ty = return (Var x)
                       
-- | Create a list of variable definitions from the scrutinee 
-- of a case expression and the pattern in a branch. Scrutinees
-- that are not variables or constructors applied to vars may not 
-- produce any equations.
equateWithPat :: Term -> Pattern -> Type -> TcMonad [Decl]
equateWithPat (Var x) pat ty = do
  tm <- pat2Term pat ty
  return [Def x tm]
equateWithPat (DCon dc args _) (PatCon dc' pats) (TCon n params)
  | dc == dc' = do
    (delta, deltai) <- lookupDCon dc n
    tele <- substTele delta params deltai
    let eqWithPats :: [Term] -> [(Pattern,Epsilon)] -> Telescope -> TcMonad [Decl]
        eqWithPats [] [] Empty = return []
        eqWithPats ts ps (Constraint tx ty tl) = do
          decls <- constraintToDecls tx ty
          extendCtxs decls $ eqWithPats ts ps tl
        eqWithPats (t : ts) ((p,_) : ps) (Cons _ x ty tl) = do
          t' <- whnf t
          decls  <- equateWithPat t' p ty
          decls' <- eqWithPats ts ps (subst x t' tl)
          return (decls ++ decls')
        eqWithPats _ _ _ = 
          err [DS "Invalid number of args to pattern", DD dc]
    eqWithPats (map unArg args) pats tele
equateWithPat (DCon dc args _) (PatCon dc' pats) (TCon n params) = do
  warn [DS "The case for", DD dc', DS "is unreachable.",
        DS "However, this implementation cannot yet allow it",
        DS "to be omitted."] >> return []
equateWithPat _ _ _ = return []  


-- | Check all of the types contained within a telescope 
-- returns a telescope where all of the types have been annotated
tcTypeTele :: Telescope -> TcMonad Telescope
tcTypeTele Empty = return Empty
tcTypeTele (Constraint tm1 tm2 tl) = do
  (tm1', ty1) <- inferType tm1
  (tm2',_)    <- checkType tm2 ty1
  decls       <- constraintToDecls tm1' tm2' 
  tele'       <- extendCtxs decls $ tcTypeTele tl
  return (Constraint tm1' tm2' tele')
tcTypeTele (Cons ep x ty tl) = do
  ty' <- tcType ty
  tele' <- extendCtx (Sig x ty') $ tcTypeTele tl
  return (Cons ep x ty' tele')

  
--------------------------------------------------------
-- Using the typechecker for decls and modules and stuff
--------------------------------------------------------

-- | Typecheck a collection of modules. Assumes that each module
-- appears after its dependencies. Returns the same list of modules
-- with each definition typechecked 
tcModules :: [Module] -> TcMonad [Module]
tcModules mods = foldM tcM [] mods
  -- Check module m against modules in defs, then add m to the list.
  where defs `tcM` m = do -- "M" is for "Module" not "monad"
          let name = moduleName m
          liftIO $ putStrLn $ "Checking module " ++ show name
          m' <- defs `tcModule` m
          return $ defs++[m']

-- | Typecheck an entire module.
tcModule :: [Module]        -- ^ List of already checked modules (including their Decls).
         -> Module          -- ^ Module to check.
         -> TcMonad Module  -- ^ The same module with all Decls checked and elaborated.
tcModule defs m' = do checkedEntries <- extendCtxMods importedModules $
                                          foldr tcE (return [])
                                                  (moduleEntries m')
                      return $ m' { moduleEntries = checkedEntries }
  where d `tcE` m = do
          -- Extend the Env per the current Decl before checking
          -- subsequent Decls.
          x <- tcEntry d
          case x of
            AddHint  hint  -> extendHints hint m
                           -- Add decls to the Decls to be returned
            AddCtx decls -> (decls++) <$> (extendCtxsGlobal decls m)
        -- Get all of the defs from imported modules (this is the env to check current module in)
        importedModules = filter (\x -> (ModuleImport (moduleName x)) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Decl.
data HintOrCtx = AddHint Hint
               | AddCtx [Decl]

-- | Check each sort of declaration in a module
tcEntry :: Decl -> TcMonad HintOrCtx
tcEntry (Def n term) = do
  oldDef <- lookupDef n
  case oldDef of
    Nothing -> tc
    Just term' -> die term'
  where
    tc = do
      lkup <- lookupHint n
      case lkup of
        Nothing -> do (aterm, ty) <- inferType term 
                      return $ AddCtx [Sig n ty, Def n aterm]
        Just ty ->
          let handler (Err ps msg) = throwError $ Err (ps) (msg $$ msg')
              msg' = disp [DS "When checking the term ", DD term,
                           DS "against the signature", DD ty]
          in do
            (eterm, ety) <- extendCtx (Sig n ty) $
                               checkType term ty `catchError` handler
            -- Put the elaborated version of term into the context.
            if (n `elem` fv eterm) then
                 return $ AddCtx [Sig n ety, RecDef n eterm]
              else
                 return $ AddCtx [Sig n ety, Def n eterm]
    die term' =
      extendSourceLocation (unPosFlaky term) term $
         err [DS "Multiple definitions of", DD n,
              DS "Previous definition was", DD term']

tcEntry (Sig n ty) = do
  duplicateTypeBindingCheck n ty
  ety <- tcType ty
  return $ AddHint (Hint n ety)

-- rule Decl_data
tcEntry (Data t delta cs) =
  do -- Check that the telescope for the datatype definition is well-formed
     edelta <- tcTypeTele delta
     ---- check that the telescope provided 
     ---  for each data constructor is wellfomed, and elaborate them
     let elabConstructorDef defn@(ConstructorDef pos d tele) =
            extendSourceLocation pos defn $ 
              extendCtx (DataSig t edelta) $
                extendCtxTele edelta $ do
                  etele <- tcTypeTele tele
                  return (ConstructorDef pos d etele)
     ecs <- mapM elabConstructorDef cs
     -- Implicitly, we expect the constructors to actually be different...
     let cnames = map (\(ConstructorDef _ c _) -> c) cs
     unless (length cnames == length (nub cnames)) $
       err [DS "Datatype definition", DD t, DS "contains duplicated constructors" ]
     -- finally, add the datatype to the env and perform action m
     return $ AddCtx [Data t edelta ecs]
tcEntry (DataSig _ _ ) = err [DS "internal construct"]     
tcEntry (RecDef _ _ )  = err [DS "internal construct"]     

     
-- | Make sure that we don't have the same name twice in the      
-- environment. (We don't rename top-level module definitions.)
duplicateTypeBindingCheck :: TName -> Term -> TcMonad ()
duplicateTypeBindingCheck n ty = do
  -- Look for existing type bindings ...
  l  <- lookupTyMaybe n
  l' <- lookupHint    n
  -- ... we don't care which, if either are Just.
  case catMaybes [l,l'] of
    [] ->  return ()
    -- We already have a type in the environment so fail.
    ty':_ ->
      let (Pos p  _) = ty
          msg = [DS "Duplicate type signature ", DD ty,
                 DS "for name ", DD n,
                 DS "Previous typing was", DD ty']
       in
         extendSourceLocation p ty $ err msg

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
exhaustivityCheck scrut ty (PatVar x:_) = return ()
exhaustivityCheck scrut ty pats = do
  (tcon, tys)   <- ensureTCon ty
  (delta,mdefs) <- lookupTCon tcon
  case mdefs of 
    Just datacons -> loop pats datacons
      where 
        loop [] [] = return ()
        loop [] dcons = do
          l <- checkImpossible dcons
          if null l then return ()
             else err $ [DS "Missing case for "] ++ map DD l
        loop ((PatVar x):_) dcons = return ()
        loop ((PatCon dc args):pats') dcons = do
          (cd@(ConstructorDef _ _ tele, dcons')) <- removeDcon dc dcons 
          tele' <- substTele delta tys tele 
          let (aargs, pats'') = relatedPats dc pats'
          checkSubPats dc tele' (args:aargs) 
          loop pats'' dcons'
          
        -- make sure that the given list of constructors is impossible
        -- in the current environment
        checkImpossible :: [ConstructorDef] -> TcMonad [DCName]
        checkImpossible [] = return []
        checkImpossible cd@(ConstructorDef _ dc tele : rest) = do
          this <- (do
                      tele' <- substTele delta tys tele
                      _     <- tcTypeTele tele'
                      return [dc]) `catchError` (\_ -> return [])                  
          others <- checkImpossible rest
          return (this ++ others)
            
    Nothing -> 
      err [DS "Cannot determine constructors of", DD ty]      
  
  
-- this could be because the scrutinee is not unifiable with the pattern
-- or because the constraints on the pattern are not satisfiable

  

                   
-- | Given a particular data constructor name and a list of data 
-- constructor definitions, pull the definition out of the list and
-- return it paired with the remainder of the list.    
removeDcon :: DCName -> [ConstructorDef] -> 
              TcMonad (ConstructorDef, [ConstructorDef])
removeDcon dc (cd@(ConstructorDef _ dc' _):rest) | dc == dc' =
  return (cd, rest)
removeDcon dc (cd1:rest) = do 
  (cd2, rr) <- removeDcon dc rest
  return (cd2, cd1:rr)
removeDcon dc [] = err [DS $ "Internal error: Can't find" ++ show dc]
  
-- | Given a particular data constructor name and a list of patterns,  
-- pull out the subpatterns that occur as arguments to that data 
-- constructor and return them paired with the remaining patterns.
relatedPats :: DCName -> [Pattern] -> ([[(Pattern,Epsilon)]], [Pattern])
relatedPats dc [] = ([],[])
relatedPats dc ((PatCon dc' args):pats) | dc == dc' = 
  let (aargs, rest) = relatedPats dc pats in
  (args:aargs, rest)
relatedPats dc (pc@(PatCon _ _):pats) = 
  let (aargs, rest) = relatedPats dc pats in
  (aargs, pc:rest)
relatedPats dc (pc@(PatVar _):pats) = ([], pc:pats)
        
-- | Occurs check for the subpatterns of a data constructor. Given 
-- the telescope specifying the types of the arguments, plus the 
-- subpatterns identified by relatedPats, check that they are each
-- exhaustive.

-- for simplicity, this function requires that all subpatterns 
-- are pattern variables. 
checkSubPats :: DCName -> Telescope -> [[(Pattern,Epsilon)]] -> TcMonad ()
checkSubPats dc Empty _ = return ()
checkSubPats dc (Constraint _ _ tele) patss = checkSubPats dc tele patss
checkSubPats dc (Cons _ name tyP tele) patss 
  | length patss > 0 && (all ((> 0) . length) patss)  = do 
    let hds = map (fst . head) patss 
    let tls = map tail patss 
    case hds of 
      (PatVar _ : []) -> checkSubPats dc tele tls
      _ -> err [DS "All subpatterns must be variables in this version."]
checkSubPats dc t ps =    
  err [DS "Internal error in checkSubPats", DD dc, DD t, DS (show ps)]            
  


