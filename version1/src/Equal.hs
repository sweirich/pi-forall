{- PiForall language -}

-- | Compare two terms for equality
module Equal (whnf, equate, ensurePi, 
               
               ) where

import Syntax
import Environment ( D(DS, DD), TcMonad )
import qualified Environment as Env
import qualified Unbound.Generics.LocallyNameless as Unbound

import Control.Monad.Except (unless, catchError, zipWithM, zipWithM_)

-- | compare two expressions for equality
--   if the two terms and not already in whnf, first check if they are alpha equivalent 

--   ignore type annotations during comparison
--   throw an error if the two types cannot be matched up
equate :: Term -> Term -> TcMonad ()
equate t1 t2 = if (Unbound.aeq t1 t2) then return () else do
  --Env.warn [DS "Equating: ", DD t1, DS " and  ", DD t2]
  n1 <- whnf' False t1  
  n2 <- whnf' False t2
  case (n1, n2) of 
    (Type, Type) -> return ()
    (Var x,  Var y)  | x == y -> return ()
    (Lam bnd1, Lam bnd2) -> do
      (_, b1, _, b2) <- Unbound.unbind2Plus bnd1 bnd2
      equate b1 b2
    (App a1 a2, App b1 b2) -> do
      equate a1 b1 
      equateArgs [a2] [b2]
    (Pi bnd1, Pi bnd2) -> do
      ((_,  Unbound.unembed -> tyA1), tyB1, 
       (_,  Unbound.unembed -> tyA2), tyB2) <- Unbound.unbind2Plus bnd1 bnd2 

      equate tyA1 tyA2                                             
      equate tyB1 tyB2

{-
    (Ann at1 _, at2) -> equate at1 at2
    (at1, Ann at2 _) -> equate at1 at2
    (Paren at1, at2) -> equate at1 at2
    (at1, Paren at2) -> equate at1 at2
    (Pos _ at1, at2) -> equate at1 at2
    (at1, Pos _ at2) -> equate at1 at2
  -}

    (TrustMe, TrustMe) ->  return ()
    (PrintMe, PrintMe) ->  return ()
    
    (TyUnit, TyUnit)   -> return ()
    (LitUnit, LitUnit) -> return ()
    
    (TyBool, TyBool)   -> return ()
    
    (LitBool b1, LitBool b2) | b1 == b2 -> return ()
    
    (If a1 b1 c1, If a2 b2 c2) -> 
      equate a1 a2 >> equate b1 b2 >> equate c1 c2
      
    (Let bnd1, Let bnd2) -> do
      Just ((x,Unbound.unembed -> rhs1), body1, 
            (_,Unbound.unembed -> rhs2), body2) <- Unbound.unbind2 bnd1 bnd2
      equate rhs1 rhs2
      equate body1 body2
            
    (Sigma bnd1, Sigma bnd2) -> do 
      Just ((x, Unbound.unembed -> tyA1), tyB1, 
            (_, Unbound.unembed -> tyA2), tyB2) <- Unbound.unbind2 bnd1 bnd2
      equate tyA1 tyA2                                             
      equate tyB1 tyB2

    (Prod a1 b1, Prod a2 b2) -> do
      equate a1 a2
      equate b1 b2
      
    (LetPair s1 bnd1, LetPair s2 bnd2) -> do  
      equate s1 s2
      Just ((x,y), body1, _, body2) <- Unbound.unbind2 bnd1 bnd2
      equate body1 body2
      

    (Var x, _) -> recEquate x n2
    (_, Var x) -> recEquate x n1
    (_,_) -> tyErr n1 n2
 where tyErr n1 n2 = do 
          gamma <- Env.getLocalCtx
          Env.err [DS "Expected", DD n2,
               DS "but found", DD n1,
               DS "in context:", DD gamma]
       recEquate x n2 = do
         mrd <- Env.lookupRecDef x 
         case mrd of 
           Just d -> equate d n2
           Nothing -> tyErr (Var x) n2


-- | Match up args
equateArgs :: [Arg] -> [Arg] -> TcMonad ()    
equateArgs (a1:t1s) (a2:t2s) = do
  equate (unArg a1) (unArg a2)
  equateArgs t1s t2s

equateArgs [] [] = return ()
equateArgs a1 a2 = do 
          gamma <- Env.getLocalCtx
          Env.err [DS "Expected", DD (length a2),
                   DS "but found", DD (length a1),
                   DS "in context:", DD gamma]

  
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
    (Pi bnd) -> do 
      ((x,  Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
      return (x,  tyA, tyB)
    _ -> Env.err [DS "Expected a function type, instead found", DD nf]
    
    
    
    

    

-------------------------------------------------------
-- | Convert a term to its weak-head normal form.             

-- Compute whnf while unfolding recursive definitions as well as non-recursive
-- ones. But only unfold once.
whnf :: Term -> TcMonad Term
whnf t = do
  whnf' True t
  
whnf' :: Bool -> Term -> TcMonad Term       
whnf' b (Var x) = do      
  maybeDef <- Env.lookupDef x
  case (maybeDef) of 
    (Just d) -> whnf' b d 
    _ -> 
      if b then do
          maybeRecDef <- Env.lookupRecDef x 
          case maybeRecDef of 
            (Just d) -> whnf' False d
            _ -> return (Var x)
        else 
          return (Var x)

whnf' b (App t1 a2) = do
  nf <- whnf' b t1 
  case nf of 
    (Lam bnd) -> do
      ((x ), body) <- Unbound.unbind bnd 
      whnf' b (Unbound.subst x (unArg a2) body)
      
    _ -> do
      return (App nf a2)
      
      
whnf' b (If t1 t2 t3) = do
  nf <- whnf' b t1
  case nf of 
    (LitBool bo) -> if bo then whnf' b t2 else whnf' b t3
    _ -> return (If nf t2 t3)

whnf' b (LetPair a bnd) = do
  nf <- whnf' b a 
  case nf of 
    Prod b1 c -> do
      ((x,y), body) <- Unbound.unbind bnd
      whnf' b (Unbound.subst x b1 (Unbound.subst y c body))
    _ -> return (LetPair nf bnd)

-- just ignore type annotations and source positions when normalizing  
whnf' b (Ann tm _) = whnf' b tm
whnf' b (Paren tm) = whnf' b tm
whnf' b (Pos _ tm) = whnf' b tm
 
  
    
            
-- all other terms are already in WHNF
whnf' b tm = return tm




