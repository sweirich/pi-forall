{- pi-forall language -}

-- | Compare two terms for equality
module Equal (whnf, equate, ensurePi, 
              ensureTyEq,  
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
    (Type, Type) -> return ()
    (Var x,  Var y) | x == y -> return ()
    (Lam bnd1, Lam bnd2) -> do
      (_, b1, _, b2) <- Unbound.unbind2Plus bnd1 bnd2

      equate b1 b2
    (App a1 a2, App b1 b2) ->
      equate a1 b1 >> equate a2 b2
    (Pi tyA1 bnd1, Pi tyA2 bnd2) -> do 
      (_, tyB1, _, tyB2) <- Unbound.unbind2Plus bnd1 bnd2 

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
            
    (Sigma tyA1 bnd1, Sigma tyA2 bnd2) -> do 
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
       



-------------------------------------------------------

-- | Ensure that the given type 'ty' is a 'Pi' type
-- (or could be normalized to be such) and return the components of 
-- the type.
-- Throws an error if this is not the case.
ensurePi :: Type -> 
  TcMonad ( Type, (Unbound.Bind TName Type))
ensurePi ty = do
  nf <- whnf ty
  case nf of 
    (Pi  tyA bnd) -> do 
      return ( tyA, bnd)
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
    (Lam  bnd) -> do
      whnf (Unbound.substBind bnd t2)
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
      ((x,y), body) <- Unbound.unbind bnd
      whnf (Unbound.substs [(x, b1), (y, c)] body)
    _ -> return (LetPair nf bnd)

-- ignore/remove type annotations and source positions when normalizing  
whnf (Ann tm _) = whnf tm
whnf (Pos _ tm) = whnf tm
 
whnf (Let rhs bnd)  = do
  -- (x,body) <- Unbound.unbind bnd
  whnf (Unbound.substBind bnd rhs)  
whnf (Subst tm pf) = do
  pf' <- whnf pf
  case pf' of 
    Refl -> whnf tm
    _ -> return (Subst tm pf')    
            
-- all other terms are already in WHNF
-- don't do anything special for them
whnf tm = return tm




