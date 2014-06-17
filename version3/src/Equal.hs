{- PiForall language, OPLSS -}

{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | Compare two terms for equality
module Equal (whnf,equate,ensureType,ensurePi, 
              
              ensureTyEq,  
              ensureTCon  ) where

import Syntax
import Environment

import Unbound.LocallyNameless hiding (Data, Refl)
import Control.Monad.Error (catchError, zipWithM, zipWithM_)
import Control.Applicative ((<$>))


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
                               
    (TyEq a b, TyEq c d) -> equate a c >> equate b d      
    
    (Refl _,  Refl _) -> return ()
    
    (Subst at1 p1 _, Subst at2 p2 _) -> equate at1 at2 >> equate p1 p2
        
    (Contra a1 _, Contra a2 _) -> return ()
      



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

    (_,_) -> do 
      gamma <- getLocalCtx
      err [DS "Expected", DD n2,
           DS "but found", DD n1,
           DS "in context:", DD gamma]

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
  
  
-------------------------------------------------------

-- | Ensure that the given type 'ty' is some 'Type i' for 
-- some i
ensureType :: Term -> TcMonad ()
ensureType ty = do
  nf <- whnf ty
  case nf of 
    Type-> return ()
    _  -> err [DS "Expected a Type, instead found", DD nf]

-- | Ensure that the given type 'ty' is a 'Pi' type
-- (or could be normalized to be such) and return the components of 
-- the type.
-- Throws an error if this is not the case.
ensurePi :: Term -> TcMonad (TName, Term, Term)
ensurePi ty = do
  nf <- whnf ty
  case nf of 
    (Pi bnd) -> do 
      ((x, unembed -> tyA), tyB) <- unbind bnd
      return (x, tyA, tyB)
    _ -> err [DS "Expected a function type, instead found", DD nf]
    

    
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
        -- only unfold applications of recursive definitions
    -- if the argument is a data constructor.
    (Var y) -> do
      maybeDef <- lookupRecDef y
      nf2 <- whnf t2 
      case (maybeDef,nf2) of 
        (Just d, DCon _ _ _) -> do
          whnf (App d nf2)
        _ -> return (App nf nf2)
      
    _ -> do
      return (App nf t2)
      

      
whnf (If t1 t2 t3 ann) = do
  nf <- whnf t1
  case nf of 
    (LitBool b) -> if b then whnf t2 else whnf t3
    _ -> return (If nf t2 t3 ann)

whnf (Pcase a bnd ann) = do
  nf <- whnf a 
  case nf of 
    Prod b c _ -> do
      ((x,y), body) <- unbind bnd
      whnf (subst x b (subst y c body))
    _ -> return (Pcase nf bnd ann)

whnf t@(Ann tm ty) = 
  err [DS "Unexpected arg to whnf:", DD t]
whnf t@(Paren x)   = 
  err [DS "Unexpected arg to whnf:", DD t]
whnf t@(Pos _ x)   = 
  err [DS "Unexpected position arg to whnf:", DD t]

whnf (Let bnd)  = do
  ((x,unembed->rhs),body) <- unbind bnd
  whnf (subst x rhs body)
  
  
whnf (Subst tm pf annot) = do
  pf' <- whnf pf
  case pf' of 
    Refl _ -> whnf tm
    _ -> return (Subst tm pf' annot)
    

whnf (Case scrut mtchs annot) = do
  nf <- whnf scrut        
  case nf of 
    (DCon d args _) -> f mtchs where
      f (Match bnd : alts) = (do
          (pat, br) <- unbind bnd
          ss <- patternMatches (Arg Runtime nf) pat 
          whnf (substs ss br)) 
            `catchError` \ _ -> f alts
      f [] = err $ [DS "Internal error: couldn't find a matching",
                    DS "branch for", DD nf, DS "in"] ++ (map DD mtchs)
    _ -> return (Case nf mtchs annot)
            


-- all other terms are already in WHNF
whnf tm = return tm


-- | Determine whether the pattern matches the argument
-- If so return the appropriate substitution
patternMatches :: Arg -> Pattern -> TcMonad [(TName, Term)]
patternMatches (Arg _ t) (PatVar x) = return [(x, t)]
patternMatches (Arg Runtime t) pat@(PatCon d' pats) = do
  nf <- whnf t
  case nf of 
    (DCon d [] _) -> return []
    (DCon d args _) | d == d' -> 
       concat <$> zipWithM patternMatches args (map fst pats)
    _ -> err [DS "arg", DD nf, DS "doesn't match pattern", DD pat]
patternMatches (Arg Constraint _) pat =   
  err [DS "Internal error"]
patternMatches (Arg Erased _) pat@(PatCon _ _) = do
  err [DS "Cannot match against irrelevant args"]


