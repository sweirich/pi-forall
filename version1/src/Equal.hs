{- pi-forall language -}

-- | Compare two terms for equality
module Equal (whnf, equate, ensurePi, 
               
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
    (App a1 a2, App b1 b2) -> do
      equate a1 b1 
      equateArg a2 b2
    (Pi tyA1 bnd1, Pi tyA2 bnd2) -> do
      ((_), tyB1, 
       (_), tyB2) <- Unbound.unbind2Plus bnd1 bnd2 

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

equateArg :: Arg -> Arg -> TcMonad ()

equateArg (Arg t1) (Arg t2) = equate t1 t2


-------------------------------------------------------

-- | Ensure that the given type 'ty' is a 'Pi' type
-- (or could be normalized to be such) and return the components of 
-- the type.
-- Throws an error if this is not the case.
ensurePi :: Type -> 
  TcMonad (TName,  Type, Type)
ensurePi ty = do
  nf <- whnf ty
  case nf of 
    (Pi tyA bnd) -> do 
      ((x), tyB) <- Unbound.unbind bnd
      return (x, tyA, tyB)
    _ -> Env.err [DS "Expected a function type, instead found", DD nf]
    
    
    
    

    

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
        
whnf (App t1 a2) = do
  nf <- whnf t1 
  case nf of 
    (Lam bnd) -> do
      ((x ), body) <- Unbound.unbind bnd 
      whnf (Unbound.subst x (unArg a2) body)
    _ -> do
      return (App nf a2)
      
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
      whnf (Unbound.subst x b1 (Unbound.subst y c body))
    _ -> return (LetPair nf bnd)

-- ignore/remove type annotations and source positions when normalizing  
whnf (Ann tm _) = whnf tm
whnf (Pos _ tm) = whnf tm
 
  
    
            
-- all other terms are already in WHNF
-- don't do anything special for them
whnf tm = return tm




