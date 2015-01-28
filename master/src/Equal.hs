{- PiForall language, OPLSS -}

{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | Compare two terms for equality
module Equal (whnf, equate, ensurePi, 
              {- SOLN EP -}ensureErasedPi, {- STUBWITH -}
              {- SOLN EQUAL -} ensureTyEq, {- STUBWITH -} 
              {-SOLN DATA -} ensureTCon {- STUBWITH -} ) where

import Syntax
import Environment

import Unbound.LocallyNameless hiding (Data, Refl)
{- SOLN DATA -}
import Control.Monad.Except (catchError, zipWithM, zipWithM_)
import Control.Applicative ((<$>))
{- STUBWITH -}

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
{- SOLN EQUAL -}      
    (TyEq a b, TyEq c d) -> do
      equate a c 
      equate b d      
    
    (Refl _,  Refl _) -> return ()
    
    (Subst at1 p1 _, Subst at2 p2 _) -> equate at1 at2 >> equate p1 p2
        
    (Contra a1 _, Contra a2 _) -> return ()
{- STUBWITH -}      
{- SOLN EP -}
    (ErasedLam bnd1, ErasedLam bnd2) -> do
      Just (x, b1, _, b2) <- unbind2 bnd1 bnd2
      equate b1 b2
    (ErasedApp a1 a2, ErasedApp b1 b2) -> do
      equate a1 b1 
      -- ignore erased arguments
    (ErasedPi bnd1, ErasedPi bnd2) -> do
      Just ((x, unembed -> tyA1), tyB1, 
            (_, unembed -> tyA2), tyB2) <- unbind2 bnd1 bnd2
      equate tyA1 tyA2                                             
      equate tyB1 tyB2
{- STUBWITH -}
{- SOLN DATA -}      
    (TCon c1 ts1, TCon c2 ts2) | c1 == c2 -> 
      zipWithM_ equate ts1 ts2
    (DCon d1 a1 _, DCon d2 a2 _) | d1 == d2 -> do
      equateArgs a1 a2
    (Case s1 brs1 ann1, Case s2 brs2 ann2) 
      | length brs1 == length brs2 -> do
      equate s1 s2
      -- require branches to be in the same order
      -- on both expressions
      let matchBr (Match bnd1) (Match bnd2) = do
            mpb <- unbind2 bnd1 bnd2
            case mpb of 
              Just (p1, a1, p2, a2) | p1 == p2 -> do
                equate a1 a2
              _ -> err [DS "Cannot match branches in",
                              DD n1, DS "and", DD n2]
      zipWithM_ matchBr brs1 brs2       
{- STUBWITH -}
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

{- SOLN DATA -}
-- | Note: ignores erased args during comparison
equateArgs :: [Arg] -> [Arg] -> TcMonad ()    
equateArgs (Arg Runtime t1:t1s) (Arg Runtime t2:t2s) = do
  equate t1 t2
  equateArgs t1s t2s
equateArgs (Arg Erased _:t1s) (Arg Erased _ :t2s) = 
  equateArgs t1s t2s
equateArgs [] [] = return ()
equateArgs a1 a2 = 
  err [DS "args don't match"]
{- STUBWITH -}  
  
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
{- SOLN EP -}
    (ErasedPi _) -> err [DS "Type error in application. Perhaps you forgot an erased argument?"]{- STUBWITH -}
    _ -> err [DS "Expected a function type, instead found", DD nf]
    
{- SOLN EP -}    
-- | Ensure that the given type 'ty' is an 'ErasedPi' type
-- (or could be normalized to be such) and return the components of 
-- the type.
-- Throws an error if this is not the case.
ensureErasedPi :: Term -> TcMonad (TName, Term, Term)
ensureErasedPi ty = do
  nf <- whnf ty
  case nf of 
    (ErasedPi bnd) -> do 
      ((x, unembed -> tyA), tyB) <- unbind bnd
      return (x, tyA, tyB)
    _ -> err [DS "Expected an erased function type, instead found", DD nf]
{- STUBWITH -}
    
{- SOLN EQUAL -}    
-- | Ensure that the given 'ty' is an equality type 
-- (or could be normalized to be such) and return     
-- the LHS and RHS of that equality
-- Throws an error if this is not the case.
ensureTyEq :: Term -> TcMonad (Term,Term)     
ensureTyEq ty = do 
  nf <- whnf ty
  case nf of 
    TyEq m n -> return (m, n)
    _ -> err [DS "Expected an equality type, instead found", DD nf]
{- STUBWITH -}    
    
{- SOLN DATA -}
-- | Ensure that the given type 'ty' is some tycon applied to 
--  params (or could be normalized to be such).
-- Throws an error if this is not the case.    
ensureTCon :: Term -> TcMonad (TCName, [Term])
ensureTCon aty = do
  nf <- whnf aty
  case nf of 
    (TCon n params) -> return (n, params)    
    _ -> err [DS "Expected a data type", 
              DS ", but found", DD nf]
{- STUBWITH -}
    

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
    {- SOLN DATA -}
    -- only unfold applications of recursive definitions
    -- if the argument is not a variable.
    (Var y) -> do
      nf2 <- whnf' b t2             
      maybeDef <- lookupRecDef y
      case maybeDef of 
        (Just d) -> whnf' False (App d nf2)
        _ -> return (App nf nf2)
    {- STUBWITH -}  
    _ -> do
      return (App nf t2)
      
{- SOLN EP -}      
whnf' b (ErasedApp t1 t2) = do
  nf <- whnf' b t1 
  case nf of 
    (ErasedLam bnd) -> do
      ((x,_),body) <- unbind bnd 
      whnf' b (subst x t2 body)
    -- unfold rec defs?
    (Var y) -> do
      nf2 <- whnf' b t2             
      maybeDef <- lookupRecDef y
      case maybeDef of 
        (Just d) -> whnf' False (ErasedApp d nf2)
        _ -> return (ErasedApp nf nf2)

    _ -> do
      return (ErasedApp nf t2)
{- STUBWITH -}
      
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
{- SOLN HW -}
whnf' b (Let bnd)  = do
  ((x,unembed->rhs),body) <- unbind bnd
  whnf' b (subst x rhs body)
{- STUBWITH -}  
{- SOLN EQUAL -}  
whnf' b (Subst tm pf annot) = do
  pf' <- whnf' b pf
  case pf' of 
    Refl _ -> whnf' b tm
    _ -> return (Subst tm pf' annot)
{- STUBWITH -}    
{- SOLN DATA -}      
whnf' b (Case scrut mtchs annot) = do
  nf <- whnf' b scrut        
  case nf of 
    (DCon d args _) -> f mtchs where
      f (Match bnd : alts) = (do
          (pat, br) <- unbind bnd
          ss <- patternMatches (Arg Runtime nf) pat 
          whnf' b (substs ss br)) 
            `catchError` \ _ -> f alts
      f [] = err $ [DS "Internal error: couldn't find a matching",
                    DS "branch for", DD nf, DS "in"] ++ (map DD mtchs)
    _ -> return (Case nf mtchs annot)
{- STUBWITH -}            


-- all other terms are already in WHNF
whnf' b tm = return tm


{- SOLN DATA -}
-- | Determine whether the pattern matches the argument
-- If so return the appropriate substitution
-- otherwise throws an error
patternMatches :: Arg -> Pattern -> TcMonad [(TName, Term)]
patternMatches (Arg _ t) (PatVar x) = return [(x, t)]
patternMatches (Arg Runtime t) pat@(PatCon d' pats) = do
  nf <- whnf t
  case nf of 
    (DCon d [] _)   | d == d' -> return []
    (DCon d args _) | d == d' -> 
       concat <$> zipWithM patternMatches args (map fst pats)
    _ -> err [DS "arg", DD nf, DS "doesn't match pattern", DD pat]
patternMatches (Arg Erased _) pat@(PatCon _ _) = do
  err [DS "Cannot match against irrelevant args"]
{- STUBWITH -}

