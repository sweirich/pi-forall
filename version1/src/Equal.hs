{- PiForall language, OPLSS -}

{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | Compare two terms for equality
module Equal (whnf,equate,ensureType,ensurePi, 
               
               ) where

import Syntax
import Environment

import Unbound.LocallyNameless hiding (Data, Refl)


-- | compare two expressions for equality
--   ignores type annotations during comparison
--   throws an error if the two types cannot be matched up
equate :: Term -> Term -> TcMonad ()
equate t1 t2 = do 
  n1 <- whnf t1  
  n2 <- whnf t2
  case (n1, n2) of 
    (Type, Type) -> return ()
    (Var x,  Var y)  | x == y -> return ()
    (Lam bnd1, Lam bnd2) -> do
      Just (x, b1, _, b2) <- unbind2 bnd1 bnd2
      equate b1 b2
    (App a1 a2, App b1 b2) -> do
      equate a1 b1 
      equate a2 b2
    (Pi bnd1, Pi bnd2) -> do
      Just ((x, unembed -> tyA1), tyB1, 
            (_, unembed -> tyA2), tyB2) <- unbind2 bnd1 bnd2
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
                               
      





            
    (_,_) -> do 
      gamma <- getLocalCtx
      err [DS "Expected", DD t2, DS "which normalizes to", DD n2,
           DS "but found", DD t1,  DS "which normalizes to", DD n1,
           DS "in context:", DD gamma]

-- | Note: ignores erased args during comparison
equateArgs :: Arg -> Arg -> TcMonad ()    
equateArgs (Arg Runtime t1) (Arg Runtime t2) = do
  equate t1 t2
equateArgs a@(Arg Erased t1) (Arg Erased t2) = return ()
equateArgs a1 a2 = err [DS "Arguments do not match", 
                       DD a1, DS "and", DD a2]
  
-------------------------------------------------------

-- | Ensure that the given type 'ty' is some 'Type i' for 
-- some i
ensureType :: Term -> TcMonad ()
ensureType ty = do
  nf <- whnf ty
  case nf of 
    Type-> return ()
    _  -> err [DS "Expected a Type, instead found", DD nf]

-- | Ensure that the given type 'ty' is some sort of 'Pi' type
-- (or could be normalized to be such) and return the components of 
-- the type.
-- Throws an error if this is not the case.
ensurePi :: Term -> TcMonad (Epsilon, TName, Term, Term, Maybe Term)
ensurePi ty = do
  nf <- whnf ty
  case nf of 
    (Pi bnd) -> do 
      ((x, unembed -> tyA), tyB) <- unbind bnd
      return (Runtime, x, tyA, tyB, Nothing)
    (ErasedPi bnd) -> do 
      ((x, unembed -> tyA), tyB) <- unbind bnd
      return (Erased, x, tyA, tyB, Nothing)
    (PiC ep bnd) -> do
      ((x, unembed -> tyA), (constr, tyB)) <- unbind bnd
      return (ep, x, tyA, tyB, Just constr)      
    _ -> err [DS "Expected a function type, instead found", DD nf]
    
    
    
    

    

-------------------------------------------------------
-- | Convert a term to its weak-head normal form.             
-- If there is a variable in the active position with 
-- a definition in the context, expand it.    
whnf :: Term -> TcMonad Term
  
whnf (Var x) = do      
  maybeDef <- lookupDef x
  case (maybeDef) of 
    (Just d) -> whnf d 
    _ -> return (Var x)

whnf (App t1 t2) = do
  nf <- whnf t1 
  case nf of 
    (Lam bnd) -> do
      ((x,_),body) <- unbind bnd 
      whnf (subst x t2 body)
      
    _ -> do
      return (App nf t2)
      
whnf (ErasedApp t1 t2) = do
  nf <- whnf t1 
  case nf of 
    (ErasedLam bnd) -> do
      ((x,_),body) <- unbind bnd 
      whnf (subst x t2 body)
      
    _ -> do
      return (ErasedApp nf t2)

whnf (If t1 t2 t3 ann) = do
  nf <- whnf t1
  case nf of 
    (LitBool b) -> if b then whnf t2 else whnf t3
    _ -> return (If nf t2 t3 ann)

      

whnf t@(Ann tm ty) = 
  err [DS "Unexpected arg to whnf:", DD t]
whnf t@(Paren x)   = 
  err [DS "Unexpected arg to whnf:", DD t]
whnf t@(Pos _ x)   = 
  err [DS "Unexpected position arg to whnf:", DD t]

  
  
    

            


-- all other terms are already in WHNF
whnf tm = return tm




