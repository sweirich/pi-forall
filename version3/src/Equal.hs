{- pi-forall language -}

-- | Compare two terms for equality
module Equal (whnf, equate, ensurePi, unify
              {- SOLN EQUAL -},ensureTyEq {- STUBWITH -} 
               ) where

import Syntax
import Environment ( D(DS, DD), TcMonad )
import qualified Environment as Env
import qualified Unbound.Generics.LocallyNameless as Unbound

import Control.Monad.Except (unless, catchError, zipWithM, zipWithM_)

-- | compare two expressions for equality
-- first check if they are alpha equivalent then
-- if not, weak-head normalize and compare
-- throw an error if they cannot be matched up
equate :: Term -> Term -> TcMonad ()
equate t1 t2 | Unbound.aeq t1 t2 = return () 
equate t1 t2 = do
  n1 <- whnf t1  
  n2 <- whnf t2
  case (n1, n2) of 
    (TyType, TyType) -> return ()
    (Var x,  Var y) | x == y -> return ()
    (Lam ep1 bnd1, Lam ep2 bnd2) -> do
      (_, b1, _, b2) <- Unbound.unbind2Plus bnd1 bnd2
      unless (ep1 == ep2) $
          tyErr n1 n2 
      equate b1 b2
    (App a1 a2, App b1 b2) ->
      equate a1 b1 >> equateArg a2 b2
    (TyPi ep1 tyA1 bnd1, TyPi ep2 tyA2 bnd2) -> do 
      (_, tyB1, _, tyB2) <- Unbound.unbind2Plus bnd1 bnd2 
      unless (ep1 == ep2) $
          tyErr n1 n2 
      equate tyA1 tyA2                                             
      equate tyB1 tyB2

    (TrustMe, TrustMe) ->  return ()
    (PrintMe, PrintMe) ->  return ()
    
    (TyUnit, TyUnit)   -> return ()
    (LitUnit, LitUnit) -> return ()
    
    (TyBool, TyBool)   -> return ()
    
    (LitBool b1, LitBool b2) | b1 == b2 -> return ()
    
    (If a1 b1 c1, If a2 b2 c2) -> 
      equate a1 a2 >> equate b1 b2 >> equate c1 c2
      
    (Let rhs1 bnd1, Let rhs2 bnd2) -> do
      Just (x, body1, _, body2) <- Unbound.unbind2 bnd1 bnd2
      equate rhs1 rhs2
      equate body1 body2
            
    (TySigma tyA1 bnd1, TySigma tyA2 bnd2) -> do 
      Just (x, tyB1, _, tyB2) <- Unbound.unbind2 bnd1 bnd2
      equate tyA1 tyA2                                             
      equate tyB1 tyB2

    (Prod a1 b1, Prod a2 b2) -> do
      equate a1 a2
      equate b1 b2
      
    (LetPair s1 bnd1, LetPair s2 bnd2) -> do  
      equate s1 s2
      Just ((x,y), body1, _, body2) <- Unbound.unbind2 bnd1 bnd2
      equate body1 body2
    (TyEq a b, TyEq c d) -> do
      equate a c 
      equate b d      
    
    (Refl,  Refl) -> return ()
    
    (Subst at1 pf1, Subst at2 pf2) -> do
      equate at1 at2
      equate pf1 pf2
        
    (Contra a1, Contra a2) -> 
      equate a1 a2
      

    (_,_) -> tyErr n1 n2
 where tyErr n1 n2 = do 
          gamma <- Env.getLocalCtx
          Env.err [DS "Expected", DD n2,
               DS "but found", DD n1,
               DS "in context:", DD gamma]
       

-- | Match up args
equateArgs :: [Arg] -> [Arg] -> TcMonad ()    
equateArgs (a1:t1s) (a2:t2s) = do
  equateArg a1 a2
  equateArgs t1s t2s
equateArgs [] [] = return ()
equateArgs a1 a2 = do 
          gamma <- Env.getLocalCtx
          Env.err [DS "Expected", DD (length a2),
                   DS "but found", DD (length a1),
                   DS "in context:", DD gamma]

-- | Ignore irrelevant arguments when comparing 
equateArg :: Arg -> Arg -> TcMonad ()
equateArg (Arg Rel t1) (Arg Rel t2) = equate t1 t2
equateArg (Arg Irr t1) (Arg Irr t2) = return ()
equateArg a1 a2 =  
  Env.err [DS "Arg stage mismatch",
              DS "Expected " , DD a2, 
              DS "Found ", DD a1] 


-------------------------------------------------------

-- | Ensure that the given type 'ty' is a 'TyPi' type
-- (or could be normalized to be such) and return the components of 
-- the type.
-- Throws an error if this is not the case.
ensurePi :: Type -> 
  TcMonad (Epsilon,  Type, (Unbound.Bind TName Type))
ensurePi ty = do
  nf <- whnf ty
  case nf of 
    (TyPi ep  tyA bnd) -> do 
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
    
    

    

-------------------------------------------------------
-- | Convert a term to its weak-head normal form.             
whnf :: Term -> TcMonad Term  
whnf (Var x) = do      
  maybeDef <- Env.lookupDef x
  case maybeDef of 
    (Just d) -> whnf d 
    _ -> do
          maybeRecDef <- Env.lookupRecDef x 
          case maybeRecDef of 
            (Just d) -> whnf d
            _ -> return (Var x)
        
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
            
-- all other terms are already in WHNF
-- don't do anything special for them
whnf tm = return tm

-- | 'Unify' the two terms, producing a list of Defs
-- If there is an obvious mismatch, this function produces an error
-- If either term is "ambiguous" just ignore.
unify :: [TName] -> Term -> Term -> TcMonad [Decl]
unify ns tx ty = do
  txnf <- whnf tx
  tynf <- whnf ty
  if Unbound.aeq txnf tynf
    then return []
    else case (txnf, tynf) of
      (Var x, Var y) | x == y -> return []
      (Var y, yty) | y `notElem` ns -> return [Def y yty]
      (yty, Var y) | y `notElem` ns -> return [Def y yty]
      (Prod a1 a2, Prod b1 b2) -> unifyArgs [Arg Rel a1, Arg Rel a2] [Arg Rel b1, Arg Rel b2]  
      
      (TyEq a1 a2, TyEq b1 b2) -> (++) <$> unify ns a1 b1 <*> unify ns a2 b2 

      (Lam ep1  bnd1, Lam ep2  bnd2) -> do
        (x, b1, _, b2) <- Unbound.unbind2Plus bnd1 bnd2
        unless (ep1 == ep2) $ do
          Env.err [DS "Cannot equate", DD txnf, DS "and", DD tynf] 
        unify (x:ns) b1 b2
      (TyPi ep1  tyA1 bnd1, TyPi ep2  tyA2 bnd2) -> do
        (x, tyB1, _, tyB2) <- Unbound.unbind2Plus bnd1 bnd2 
        unless (ep1 == ep2) $ do
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
 
amb (Subst _ _) = True 
amb _ = False



