{- PiForall language -}

-- | Compare two terms for equality
module Equal (whnf, equate, ensurePi, 
              ensureTyEq,  
               ) where

import Syntax
import Environment ( D(DS, DD), TcMonad )
import qualified Environment as Env
import qualified Unbound.Generics.LocallyNameless as Unbound

import Control.Monad.Except (unless, catchError, zipWithM, zipWithM_)

-- | Mark the type of terms that have been converted to whnf
newtype Whnf = WhnfType Term

-- | compare two expressions for equality
--   if the two terms and not already in whnf, first check if they are alpha equivalent 

--   ignore type annotations during comparison
--   throw an error if the two types cannot be matched up
equate :: Term -> Term -> TcMonad ()
equate t1 t2 = if (Unbound.aeq t1 t2) then return () else do
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
      ((_, {- SOLN EP -}ep1,{- STUBWITH -} Unbound.unembed -> tyA1), tyB1, 
       (_, {- SOLN EP -}ep2,{- STUBWITH -} Unbound.unembed -> tyA2), tyB2) <- Unbound.unbind2Plus bnd1 bnd2 
      unless (ep1 == ep2) $
          tyErr n1 n2 
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
      Just ((x,Unbound.unembed -> rhs1), body1, 
            (_,Unbound.unembed -> rhs2), body2) <- Unbound.unbind2 bnd1 bnd2
      equate rhs1 rhs2
      equate body1 body2
            
    (Sigma bnd1, Sigma bnd2) -> do 
      Just ((x, Unbound.unembed -> tyA1), tyB1, 
            (_, Unbound.unembed -> tyA2), tyB2) <- Unbound.unbind2 bnd1 bnd2
      equate tyA1 tyA2                                             
      equate tyB1 tyB2

    (Prod a1 b1 _, Prod a2 b2 _) -> do
      equate a1 a2
      equate b1 b2
      
    (LetPair s1 bnd1 _, LetPair s2 bnd2 _) -> do  
      equate s1 s2
      Just ((x,y), body1, _, body2) <- Unbound.unbind2 bnd1 bnd2
      equate body1 body2
    (TyEq a b, TyEq c d) -> do
      equate a c 
      equate b d      
    
    (Refl _,  Refl _) -> return ()
    
    -- Substitutions are never relevant for equality, nor are their proofs
    (Subst at1 _ _, ty2) -> equate at1 ty2 
    (ty1, Subst at2 _ _) -> equate ty1 at2 
        
    (Contra a1 _, Contra a2 _) -> return ()
      

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
  unless (argEp a1 == argEp a2) $
     Env.err [DS "Arg stage mismatch",
              DS "Expected " , DD a2, 
              DS "Found ", DD a1]

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
  TcMonad (TName, {- SOLN EP -}Epsilon, {- STUBWITH -} Type, Type)
ensurePi ty = do
  nf <- whnf ty
  case nf of 
    (Pi bnd) -> do 
      ((x, {- SOLN EP -}ep,{- STUBWITH -} Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
      return (x, {- SOLN EP -}ep,{- STUBWITH -} tyA, tyB)
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
      ((x, {- SOLN EP -}_,{- STUBWITH -} _),body) <- Unbound.unbind bnd 
      whnf' b (Unbound.subst x (unArg a2) body)
      
    _ -> do
      return (App nf a2)
      
      
whnf' b (If t1 t2 t3 ann) = do
  nf <- whnf' b t1
  case nf of 
    (LitBool bo) -> if bo then whnf' b t2 else whnf' b t3
    _ -> return (If nf t2 t3 ann)

whnf' b (LetPair a bnd ann) = do
  nf <- whnf' b a 
  case nf of 
    Prod b1 c _ -> do
      ((x,y), body) <- Unbound.unbind bnd
      whnf' b (Unbound.subst x b1 (Unbound.subst y c body))
    _ -> return (LetPair nf bnd ann)

-- We should only be calling whnf on elaborated terms
-- Such terms don't contain annotations, parens or pos info    
-- So we'll throw errors to detect the case where we are 
-- normalizing source terms    
whnf' b t@(Ann tm ty) = 
  Env.err [DS "Unexpected arg to whnf:", DD t]
whnf' b t@(Paren x)   = 
  Env.err [DS "Unexpected arg to whnf:", DD t]
whnf' b t@(Pos _ x)   = 
  Env.err [DS "Unexpected position arg to whnf:", DD t]
whnf' b (Let bnd)  = do
  ((x,Unbound.unembed->rhs),body) <- Unbound.unbind bnd
  whnf' b (Unbound.subst x rhs body)  
whnf' b (Subst tm pf annot) = do
  pf' <- whnf' b pf
  case pf' of 
    Refl _ -> whnf' b tm
    _ -> return (Subst tm pf' annot)    
            
-- all other terms are already in WHNF
whnf' b tm = return tm




