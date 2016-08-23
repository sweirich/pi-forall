{- PiForall language -}


{-# LANGUAGE ViewPatterns,
             FlexibleContexts,
             CPP #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | Compare two terms for equality
module Equal (whnf, equate, ensurePi, 
              
               
               ) where

import Syntax
import Environment

import Unbound.Generics.LocallyNameless


-- | compare two expressions for equality
--   ignores type annotations during comparison
--   throws an error if the two types cannot be matched up
equate :: Term -> Term -> TcMonad ()
equate t1 t2 = if (aeq t1 t2) then return () else do
  n1 <- whnf' False t1  
  n2 <- whnf' False t2
  case (n1, n2) of 
    (Type, Type) -> return ()
    (Var x,  Var y)  | x == y -> return ()
    (Lam bnd1, Lam bnd2) -> do
      (_, b1, _, b2) <- unbind2Plus bnd1 bnd2
      equate b1 b2
    (App a1 a2, App b1 b2) -> do
      equate a1 b1 
      equate a2 b2
    (Pi bnd1, Pi bnd2) -> do
      ((_, unembed -> tyA1), tyB1, 
       (_, unembed -> tyA2), tyB2) <- unbind2Plus bnd1 bnd2
      equate tyA1 tyA2                                             
      equate tyB1 tyB2


    (Ann at1 _, at2) -> equate at1 at2
    (at1, Ann at2 _) -> equate at1 at2
    (Paren at1, at2) -> equate at1 at2
    (at1, Paren at2) -> equate at1 at2
    (Pos _ at1, at2) -> equate at1 at2
    (at1, Pos _ at2) -> equate at1 at2
    
    (TrustMe _, TrustMe _) ->  return ()
    
    (TyUnit, TyUnit)   -> return ()
    (LitUnit, LitUnit) -> return ()
    
    (TyBool, TyBool)   -> return ()
    
    (LitBool b1, LitBool b2) | b1 == b2 -> return ()
    
    (If a1 b1 c1 _, If a2 b2 c2 _) -> 
      equate a1 a2 >> equate b1 b2 >> equate c1 c2
      
    (Let bnd1, Let bnd2) -> do
      Just ((x,unembed -> rhs1), body1, 
            (_,unembed -> rhs2), body2) <- unbind2 bnd1 bnd2
      equate rhs1 rhs2
      equate body1 body2
            
    (Sigma bnd1, Sigma bnd2) -> do 
      Just ((x, unembed -> tyA1), tyB1, 
            (_, unembed -> tyA2), tyB2) <- unbind2 bnd1 bnd2
      equate tyA1 tyA2                                             
      equate tyB1 tyB2

    (Prod a1 b1 _, Prod a2 b2 _) -> do
      equate a1 a2
      equate b1 b2
      
    (Pcase s1 bnd1 _, Pcase s2 bnd2 _) -> do  
      equate s1 s2
      Just ((x,y), body1, _, body2) <- unbind2 bnd1 bnd2
      equate body1 body2
      


    (Var x, _) -> recEquate x n2
    (_, Var x) -> recEquate x n1
    (_,_) -> tyErr n1 n2
 where tyErr n1 n2 = do 
          gamma <- getLocalCtx
          err [DS "Expected", DD n2,
               DS "but found", DD n1,
               DS "in context:", DD gamma]
       recEquate x n2 = do
         mrd <- lookupRecDef x 
         case mrd of 
           Just d -> equate d n2
           Nothing -> tyErr (Var x) n2

  
  
-------------------------------------------------------

-- | Ensure that the given type 'ty' is a 'Pi' type
-- (or could be normalized to be such) and return the components of 
-- the type.
-- Throws an error if this is not the case.
ensurePi :: Type -> TcMonad (TName, Type, Type)
ensurePi ty = do
  nf <- whnf ty
  case nf of 
    (Pi bnd) -> do 
      ((x, unembed -> tyA), tyB) <- unbind bnd
      return (x, tyA, tyB)

    _ -> err [DS "Expected a function type, instead found", DD nf]
    

    
    
    

    

-------------------------------------------------------
-- | Convert a term to its weak-head normal form.             

-- Compute whnf while unfolding recursive definitions as well as non-recursive
-- ones. But only unfold once.
whnf :: Term -> TcMonad Term
whnf t = do
  whnf' False t
  
whnf' :: Bool -> Term -> TcMonad Term       
whnf' b (Var x) = do      
  maybeDef <- lookupDef x
  case (maybeDef) of 
    (Just d) -> whnf' b d 
    _ -> 
      if b then do
          maybeRecDef <- lookupRecDef x 
          case maybeRecDef of 
            (Just d) -> whnf' False d
            _ -> return (Var x)
        else 
          return (Var x)

whnf' b (App t1 t2) = do
  nf <- whnf' b t1 
  case nf of 
    (Lam bnd) -> do
      ((x,_),body) <- unbind bnd 
      whnf' b (subst x t2 body)
      
    _ -> do
      return (App nf t2)
      

      
whnf' b (If t1 t2 t3 ann) = do
  nf <- whnf' b t1
  case nf of 
    (LitBool bo) -> if bo then whnf' b t2 else whnf' b t3
    _ -> return (If nf t2 t3 ann)

whnf' b (Pcase a bnd ann) = do
  nf <- whnf' b a 
  case nf of 
    Prod b1 c _ -> do
      ((x,y), body) <- unbind bnd
      whnf' b (subst x b1 (subst y c body))
    _ -> return (Pcase nf bnd ann)

-- We should only be calling whnf on elaborated terms
-- Such terms don't contain annotations, parens or pos info    
-- So we'll throw errors to detect the case where we are 
-- normalizing source terms    
whnf' b t@(Ann tm ty) = 
  err [DS "Unexpected arg to whnf:", DD t]
whnf' b t@(Paren x)   = 
  err [DS "Unexpected arg to whnf:", DD t]
whnf' b t@(Pos _ x)   = 
  err [DS "Unexpected position arg to whnf:", DD t]
  
    
            


-- all other terms are already in WHNF
whnf' b tm = return tm




