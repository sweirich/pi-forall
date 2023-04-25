{- pi-forall language -}

-- | Compare two terms for equality
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}

module Equal (whnf, equate, ensurePi,
              ensureTyEq,
              ensureTCon, unify, displace, equateLevel ) where

import Syntax
import Environment ( D(DS, DD), TcMonad, Locality(..) )
import qualified Environment as Env
import qualified Unbound.Generics.LocallyNameless as Unbound
import PrettyPrint (D(..), pp, Disp(..))

import Control.Monad.Except (unless, throwError, catchError, zipWithM, zipWithM_)
import Debug.Trace

type Result = [LevelConstraint]
success :: Result
success = []

equateLevel :: Level -> Level -> TcMonad Result
equateLevel (LConst i) (LConst j) =
  if i == j then return success
  else 
    Env.err [DS "Level mismatch",
              DS "Expected " , DD i, DS "Found ", DD j]
equateLevel l1 l2 = return [Eq l1 l2]

equateMaybeLevel :: Maybe Level -> Maybe Level -> TcMonad Result
equateMaybeLevel (Just i) (Just j) = equateLevel i j
equateMaybeLevel Nothing Nothing = return success
equateMaybeLevel i j = 
   Env.err [DS "Level annotation mismatch",
              DS "Expected " , DD i, DS "Found ", DD j]


equate :: Term -> Term -> TcMonad ()
equate t1 t2 = do
  cs <- equate' Shallow t1 t2
  mapM_ Env.extendLevelConstraint cs

-- Shallow: just compares structure
-- Deep: whnf then 
data Depth = Shallow | Deep deriving (Eq, Show)


tyErr :: (Disp a) => a -> a -> TcMonad b
tyErr t1 t2 = do
      gamma <- Env.getLocalCtx
      Env.err [DS "Expected", DD t1,
               DS "but found", DD t2,
               DS "in context:", DD gamma]


-- | compare two expressions for equality
-- first check if they are alpha equivalent then
-- if not, weak-head normalize and compare
-- throw an error if they cannot be matched up
equate' :: Depth -> Term -> Term -> TcMonad Result
equate' d (Pos p t1) t2 = equate' d t1 t2
equate' d t1 (Pos p t2) = equate' d t1 t2
equate' d (Ann t1 _) t2 = equate' d t1 t2
equate' d t1 (Ann t2 _) = equate' d t1 t2
equate' d t1 t2 = do
  (n1, n2) <- case d of 
    Deep -> (,) <$> whnf t1 <*> whnf t2
    Shallow -> return (t1, t2)
  if d == Deep then do
       traceM $ "whnf DEEP: " ++ pp n1 ++ " and " ++ pp n2
       return ()
     else return ()
  case (n1, n2) of
    (Type, Type) -> return success
    (Lam ep1 bnd1, Lam ep2 bnd2) -> do
      (_, b1, _, b2) <- Unbound.unbind2Plus bnd1 bnd2
      unless (ep1 == ep2) $ Env.err [DS "Epsilon mismatch: ", DD t2, DD t1]
      equate' Shallow b1 b2
    (Pi (Mode r1 l1) tyA1 bnd1, Pi (Mode r2 l2) tyA2 bnd2) -> do
      (_, tyB1, _, tyB2) <- Unbound.unbind2Plus bnd1 bnd2
      unless (r1 == r2) $
          tyErr n2 n1
      cs1 <- equateMaybeLevel l1 l2
      cs2 <- equate' Shallow tyA1 tyA2
      cs3 <- equate' Shallow tyB1 tyB2
      return (cs1 <> cs2 <> cs3)

    (Sigma tyA1 l1 bnd1, Sigma tyA2 l2 bnd2) -> do
      Just (x, tyB1, _, tyB2) <- Unbound.unbind2 bnd1 bnd2
      cs1 <- equateLevel l1 l2
      cs2 <- equate' Shallow tyA1 tyA2
      cs3 <- equate' Shallow tyB1 tyB2
      return (cs1 <> cs2 <> cs3)

    (TrustMe, TrustMe) ->  return success
    (PrintMe, PrintMe) ->  return success

    (TyUnit, TyUnit)   -> return success
    (LitUnit, LitUnit) -> return success

    (TyBool, TyBool)   -> return success

    (LitBool b1, LitBool b2) ->
      if b1 == b2 then return success
      else tyErr b2 b1

    (TyEq a b, TyEq c d2) -> do
      cs1 <- equate' Shallow a c
      cs2 <- equate' Shallow b d2
      return (cs1 <> cs2)

    (Refl,  Refl) -> return success

    (TCon c1 ts1, TCon c2 ts2) ->
      if c1 == c2 then do
        rs <- zipWithM (equateArgs d) [ts1] [ts2]
        return (mconcat rs)
      else
        tyErr c2 c1

    (DCon d1 a1, DCon d2 a2) | d1 == d2 -> do
      equateArgs d a1 a2
    (_,_) -> do 
        -- For terms that do not have matching head forms, 
        -- first see if they are "shallowly" equal i.e. alpha-equivalent
        -- if this fails, then try again after calling whnf on both sides
        let handler err = 
              case d of
                Shallow -> do
                  equate' Deep n1 n2
                Deep -> throwError err
        (case (n1, n2) of 
            (Var x,  Var y) | x == y -> return success
            (Displace (Var x) j, Displace (Var y) k) | x == y -> do
              isD <- Env.lookupFreelyDisplaceable x
              -- traceM $ "equating level " ++ pp j ++ " and " ++ pp k
              if isD then return success else equateLevel j k
            (Displace (Var x) j, Var y) | x == y -> return success
            (Var x, Displace (Var y) j) | x == y -> return success
            (App a1 a2, App b1 b2) -> do
              cs1 <- equate' Shallow a1 b1
              cs2 <- equateArg Shallow a2 b2
              return (cs1 <> cs2)
            
            (If a1 b1 c1, If a2 b2 c2) -> do
              cs1 <- equate' Shallow a1 a2 
              cs2 <- equate' Shallow b1 b2 
              cs3 <- equate' Shallow c1 c2
              return (cs1 <> cs2 <> cs3)

            (Let rhs1 bnd1, Let rhs2 bnd2) -> do
              Just (x, body1, _, body2) <- Unbound.unbind2 bnd1 bnd2
              cs1 <- equate' Shallow rhs1 rhs2
              cs2 <- equate' Shallow body1 body2
              return (cs1 <> cs2)

            (Prod a1 b1, Prod a2 b2) -> do
              cs1 <- equate' Shallow a1 a2
              cs2 <- equate' Shallow b1 b2
              return (cs1 <> cs2)

            (LetPair s1 bnd1, LetPair s2 bnd2) -> do
              cs1 <- equate' Shallow s1 s2
              Just ((x,y), body1, _, body2) <- Unbound.unbind2 bnd1 bnd2
              cs2 <- equate' Shallow body1 body2
              return (cs1 <> cs2) 

            (Subst at1 pf1, Subst at2 pf2) -> do
              cs1 <- equate' Shallow at1 at2
              cs2 <- equate' Shallow pf1 pf2
              return (cs1 <> cs2)

            (Contra a1, Contra a2) ->
              equate' Shallow a1 a2

            (Case s1 brs1, Case s2 brs2) ->
              if length brs1 == length brs2 then do
                  cs1 <- equate' Shallow s1 s2
                  -- require branches to be in the same order
                  -- on both expressions
                  let matchBr (Match bnd1) (Match bnd2) = do
                        mpb <- Unbound.unbind2 bnd1 bnd2
                        case mpb of
                          Just (p1, a1, p2, a2) | p1 == p2 -> do
                            equate' Shallow a1 a2
                          _ -> Env.err [DS "Cannot match branches in",
                                          DD n1, DS "and", DD n2]
                  rs <- zipWithM matchBr brs1 brs2
                  return (mconcat rs)
              else tyErr n2 n1
            (_,_) -> do
              tyErr n2 n1) `catchError` handler
  


-- | Match up args
equateArgs :: Depth -> [Arg] -> [Arg] -> TcMonad Result
equateArgs d (a1:t1s) (a2:t2s) = do
  cs <- equateArg d a1 a2
  ds <- equateArgs d t1s t2s
  return (cs ++ ds)
equateArgs d [] [] = return success
equateArgs d a1 a2 = tyErr (length a2) (length a1)
         

-- | Ignore irrelevant arguments when comparing 
equateArg :: Depth -> Arg -> Arg -> TcMonad Result
equateArg d (Arg Rel t1) (Arg Rel t2) = equate' d t1 t2
equateArg d (Arg Irr t1) (Arg Irr t2) = return success
equateArg d a1 a2 = tyErr a2 a1
  


-------------------------------------------------------

-- | Ensure that the given type 'ty' is a 'Pi' type
-- (or could be normalized to be such) and return the components of 
-- the type.
-- Throws an error if this is not the case.
ensurePi :: Type ->
  TcMonad (Epsilon, Type, Unbound.Bind TName Type)
ensurePi ty = do
  nf <- whnf ty
  case nf of
    (Pi ep  tyA bnd) -> do
      return (ep, tyA, bnd)
    _ -> Env.err [DS "Expected a function type, instead found", DD nf]


-- | Ensure that the given 'ty' is an equality type 
-- (or could be normalized to be such) and return     
-- the LHS and RHS of that equality
-- Throws an error if this is not the case.
ensureTyEq :: Term -> TcMonad (Term,Term)
ensureTyEq ty = do
  nf <- whnf ty
  case nf of
    TyEq m n -> return (m, n)
    _ -> Env.err [DS "Expected an equality type, instead found", DD nf]


-- | Ensure that the given type 'ty' is some tycon applied to 
--  params (or could be normalized to be such)
-- Throws an error if this is not the case 
ensureTCon :: Term -> TcMonad (TCName, [Arg])
ensureTCon aty = do
  nf <- whnf aty
  case nf of
    TCon n params -> return (n, params)
    _ -> Env.err [DS "Expected a data type but found", DD nf]



-------------------------------------------------------
-- | Convert a term to its weak-head normal form.             
whnf :: Term -> TcMonad Term
whnf (Var x) = do
  maybeDef <- Env.lookupDef Any x
  case maybeDef of
    (Just d) -> whnf d
    _ -> do
          maybeRecDef <- Env.lookupRecDef Any x
          case maybeRecDef of
            (Just d) -> whnf d
            _ -> return (Var x)
whnf t@(Displace (Var x) j) = do
  -- traceM $ "whnf: " ++ pp t
  maybeDef <- Env.lookupDef Global x
  case maybeDef of
    (Just d) -> displace j d >>= whnf
    _ -> do
      maybeDef2 <- Env.lookupRecDef Global x
      case maybeDef2 of
         (Just d) -> do 
          d' <- displace j d 
          -- traceM $ "displaced by " ++ pp j ++ ": " ++ pp d'
          whnf d'
         _ -> do
              -- traceM $ "whnf: no def "   
              return (Displace (Var x) j)
whnf (App t1 t2) = do
  nf <- whnf t1
  case nf of
    (Lam ep  bnd) -> do
      whnf (Unbound.instantiate bnd [unArg t2] )
    _ -> do
      return (App nf t2)

whnf (If t1 t2 t3) = do
  nf <- whnf t1
  case nf of
    (LitBool bo) -> if bo then whnf t2 else whnf t3
    _ -> return (If nf t2 t3)

whnf (LetPair a bnd) = do
  nf <- whnf a
  case nf of
    Prod b1 c -> do
      whnf (Unbound.instantiate bnd [b1, c])
    _ -> return (LetPair nf bnd)

-- ignore/remove type annotations and source positions when normalizing  
whnf (Ann tm _) = whnf tm
whnf (Pos _ tm) = whnf tm

whnf (Let rhs bnd)  = do
  -- (x,body) <- Unbound.unbind bnd
  whnf (Unbound.instantiate bnd [rhs])
whnf (Subst tm pf) = do
  pf' <- whnf pf
  case pf' of
    Refl -> whnf tm
    _ -> return (Subst tm pf')
whnf (Case scrut mtchs) = do
  nf <- whnf scrut
  case nf of
    (DCon d args) -> f mtchs where
      f (Match bnd : alts) = (do
          (pat, br) <- Unbound.unbind bnd
          ss <- patternMatches (Arg Rel nf) pat
          whnf (Unbound.substs ss br))
            `catchError` \ _ -> f alts
      f [] = Env.err $ [DS "Internal error: couldn't find a matching",
                    DS "branch for", DD nf, DS "in"] ++ map DD mtchs
    _ -> return (Case nf mtchs)

-- all other terms are already in WHNF
-- don't do anything special for them
whnf tm = return tm


-- | Determine whether the pattern matches the argument
-- If so return the appropriate substitution
-- otherwise throws an error
patternMatches :: Arg -> Pattern -> TcMonad [(TName, Term)]
patternMatches (Arg _ t) (PatVar x) = return [(x, t)]
patternMatches (Arg Rel t) pat = do
  nf <- whnf t
  case (nf, pat) of
    (DCon d [], PatCon d' pats)   | d == d' -> return []
    (DCon d args, PatCon d' pats) | d == d' ->
       concat <$> zipWithM patternMatches args (map fst pats)
    _ -> Env.err [DS "arg", DD nf, DS "doesn't match pattern", DD pat]
patternMatches (Arg Irr _) pat = do
  Env.err [DS "Cannot match against irrelevant args"]


-- | 'Unify' the two terms, producing a list of Defs
-- If there is an obvious mismatch, this function produces an error
-- If either term is "ambiguous" just fail instead.
unify :: [TName] -> Term -> Term -> TcMonad [Decl]
unify ns tx ty = do
  txnf <- whnf tx
  tynf <- whnf ty
  if Unbound.aeq txnf tynf
    then return []
    else case (txnf, tynf) of
      (Var y, yty) | y `notElem` ns -> return [Def y yty]
      (yty, Var y) | y `notElem` ns -> return [Def y yty]
      (Prod a1 a2, Prod b1 b2) -> unifyArgs [Arg Rel a1, Arg Rel a2] [Arg Rel b1, Arg Rel b2]
      (TyEq a1 a2, TyEq b1 b2) -> unifyArgs [Arg Rel a1, Arg Rel a2] [Arg Rel b1, Arg Rel b2]
      (TCon s1 tms1, TCon s2 tms2)
        | s1 == s2 -> unifyArgs tms1 tms2
      (DCon s1 a1s, DCon s2 a2s)
        | s1 == s2 -> unifyArgs a1s a2s
      (Lam ep1 bnd1, Lam ep2 bnd2) -> do
        (x, b1, _, b2) <- Unbound.unbind2Plus bnd1 bnd2
        unless (ep1 == ep2) $ do
          Env.err [DS "Cannot equate", DD txnf, DS "and", DD tynf]
        unify (x:ns) b1 b2
      (Pi (Mode r1 l1) tyA1 bnd1, Pi (Mode r2 l2) tyA2 bnd2) -> do
        (x, tyB1, _, tyB2) <- Unbound.unbind2Plus bnd1 bnd2
        cs <- equateMaybeLevel l1 l2
        mapM_ Env.extendLevelConstraint cs
        unless (r1 == r2) $ do
          Env.err [DS "Cannot equate", DD txnf, DS "and", DD tynf]
        ds1 <- unify ns tyA1 tyA2
        ds2 <- unify (x:ns) tyB1 tyB2
        return (ds1 ++ ds2)
      _ ->
        if amb txnf || amb tynf
          then return []
          else Env.err [DS "Cannot equate", DD txnf, DS "and", DD tynf]
  where
    unifyArgs (Arg _ t1 : a1s) (Arg _ t2 : a2s) = do
      ds <- unify ns t1 t2
      ds' <- unifyArgs a1s a2s
      return $ ds ++ ds'
    unifyArgs [] [] = return []
    unifyArgs _ _ = Env.err [DS "internal error (unify)"]

-- | Is a term "ambiguous" when it comes to unification?
-- In general, elimination forms are ambiguous because there are multiple 
-- solutions.
amb :: Term -> Bool
amb (App t1 t2) = True
amb If {} = True
amb (LetPair _ _) = True
amb (Case _ _) = True
amb _ = False



-----------------------------------------------------------------------------

displaceArg :: Level -> Arg -> TcMonad Arg
displaceArg j (Arg r t) = Arg r <$> displace j t

displacePat :: Level -> Pattern -> TcMonad Pattern
displacePat j (PatVar x) = return $ PatVar x
displacePat j (PatCon dc args) = do
  args' <- mapM (\(pat, rho) -> displacePat j pat >>= \pat' -> return (pat', rho)) args
  return $ PatCon dc args'

displaceBr :: Level -> Match -> TcMonad Match
displaceBr j (Match bnd) = do
  (pat, body) <- Unbound.unbind bnd
  p' <- displacePat j pat
  body' <- displace j body
  return (Match (Unbound.bind p' body'))

displace :: Level -> Term -> TcMonad Term
displace j t = case t of
    Var x -> Env.lookupTyMaybe Global x >>= \mb -> case mb of
                  Just _ -> return (Displace (Var x) j)
                  Nothing -> do 
                    -- traceM $ "not global: " ++ pp x
                    return $ Var x
    Lam r bnd -> do
      (x, a) <- Unbound.unbind bnd
      a' <- displace j a
      return $ Lam r (Unbound.bind x a')
    App f a -> App <$> displace j f <*> displaceArg j a
    Pi (Mode ep (Just k)) tyA bnd -> do
      (y, tyB) <- Unbound.unbind bnd
      -- x' <- Unbound.fresh (Unbound.string2Name $ "jD@" ++ pp lexp)
      -- let lx = LVar x'
      -- cs <- equateLevel lx (j <> lexp)
      -- mapM_ Env.extendLevelConstraint cs
      Pi (Mode ep (Just (j <> k))) <$> displace j tyA
                             <*> (Unbound.bind y <$> displace j tyB)
    Pi (Mode ep Nothing) tyA bnd -> do
      (y, tyB) <- Unbound.unbind bnd
      Pi (Mode ep Nothing) <$> displace j tyA
                               <*> (Unbound.bind y <$> displace j tyB)
    Ann tm ty -> Ann <$> displace j tm <*> displace j ty
    Pos pos tm -> Pos pos <$> displace j tm
    Let rhs bnd -> do
      (x,body) <- Unbound.unbind bnd
      Let <$> displace j rhs <*> (Unbound.bind x <$> displace j body)
    If a1 a2 a3 ->
      If <$> displace j a1 <*> displace j a2 <*> displace j a3
    Displace a j0 -> return $ Displace a (j <> j0)
    TyEq a b -> TyEq <$> displace j a <*> displace j b
    TCon tc args -> TCon tc <$> mapM (displaceArg j) args
    DCon dc args -> DCon dc <$> mapM (displaceArg j) args
    Case a brs -> 
      Case <$> displace j a <*> mapM (displaceBr j) brs
    Subst a b -> 
      Subst <$> displace j a <*> displace j b
    Contra a -> 
      Contra <$> displace j a
    
    Type -> return Type
    PrintMe -> return PrintMe
    TrustMe -> return TrustMe
    TyUnit -> return TyUnit
    LitUnit -> return LitUnit
    (LitBool b) -> return (LitBool b)
    TyBool -> return TyBool
    Refl -> return Refl
    _ -> do
      Env.warn $ "displace: " ++ pp t
      return t
      