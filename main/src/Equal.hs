{- PiForall language -}

-- | Compare two terms for equality
module Equal (whnf, equate, ensurePi, 
              {- SOLN EQUAL -} ensureTyEq, {- STUBWITH -} 
              {- SOLN DATA -} ensureTCon, WhnfTCon(..) {- STUBWITH -} ) where

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
      equateArgs [a2] [b2]
    (Pi bnd1, Pi bnd2) -> do
      ((_, {- SOLN EP -}ep1,{- STUBWITH -} Unbound.unembed -> tyA1), tyB1, 
       (_, {- SOLN EP -}ep2,{- STUBWITH -} Unbound.unembed -> tyA2), tyB2) <- Unbound.unbind2Plus bnd1 bnd2 
{- SOLN EP -}
      unless (ep1 == ep2) $
          tyErr n1 n2 {- STUBWITH -}
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
{- SOLN EQUAL -}      
    (TyEq a b, TyEq c d) -> do
      equate a c 
      equate b d      
    
    (Refl,  Refl) -> return ()
    
    (Subst at1 pf1, Subst at2 pf2) -> do
      equate at1 at2
      equate pf1 pf2
        
    (Contra a1, Contra a2) -> 
      equate a1 a2
{- STUBWITH -}      
{- SOLN DATA -}      
    (TCon c1 ts1, TCon c2 ts2) | c1 == c2 -> 
      zipWithM_ equateArgs [ts1] [ts2]
    (DCon d1 a1, DCon d2 a2) | d1 == d2 -> do
      equateArgs a1 a2
    (Case s1 brs1, Case s2 brs2) 
      | length brs1 == length brs2 -> do
      equate s1 s2
      -- require branches to be in the same order
      -- on both expressions
      let matchBr (Match bnd1) (Match bnd2) = do
            mpb <- Unbound.unbind2 bnd1 bnd2
            case mpb of 
              Just (p1, a1, p2, a2) | p1 == p2 -> do
                equate a1 a2
              _ -> Env.err [DS "Cannot match branches in",
                              DD n1, DS "and", DD n2]
      zipWithM_ matchBr brs1 brs2       
{- STUBWITH -}
    (_,_) -> tyErr n1 n2
 where tyErr n1 n2 = do 
          gamma <- Env.getLocalCtx
          Env.err [DS "Expected", DD n2,
               DS "but found", DD n1,
               DS "in context:", DD gamma]
       


-- | Match up args
-- TODO: add compile-time irrelevance here
equateArgs :: [Arg] -> [Arg] -> TcMonad ()    
equateArgs (a1:t1s) (a2:t2s) = do
  equate (unArg a1) (unArg a2)
  equateArgs t1s t2s
{- SOLN EP -}  
  unless (argEp a1 == argEp a2) $
     Env.err [DS "Arg stage mismatch",
              DS "Expected " , DD a2, 
              DS "Found ", DD a1]
{- STUBWITH -}
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
    _ -> Env.err [DS "Expected an equality type, instead found", DD nf]
{- STUBWITH -}    
    
{- SOLN DATA -}
data WhnfTCon = WhnfTCon TCName [Arg]

-- | Ensure that the given type 'ty' is some tycon applied to 
--  params (or could be normalized to be such)
-- Throws an error if this is not the case 
ensureTCon :: Term -> TcMonad WhnfTCon
ensureTCon aty = do
  nf <- whnf aty
  case nf of 
    TCon n params -> return (WhnfTCon n params)    
    _ -> Env.err [DS "Expected a data type but found", DD nf]
{- STUBWITH -}
    

-------------------------------------------------------
-- | Convert a term to its weak-head normal form.             
whnf :: Term -> TcMonad Term  
whnf (Var x) = do      
  maybeDef <- Env.lookupDef x
  case (maybeDef) of 
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
      ((x {- SOLN EP -},_{- STUBWITH -}), body) <- Unbound.unbind bnd 
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
whnf (Paren tm) = whnf tm
whnf (Pos _ tm) = whnf tm
 
{- SOLN HW -}
whnf (Let bnd)  = do
  ((x,Unbound.unembed->rhs),body) <- Unbound.unbind bnd
  whnf (Unbound.subst x rhs body){- STUBWITH -}  
{- SOLN EQUAL -}  
whnf (Subst tm pf) = do
  pf' <- whnf pf
  case pf' of 
    Refl -> whnf tm
    _ -> return (Subst tm pf'){- STUBWITH -}    
{- SOLN DATA -}      
whnf (Case scrut mtchs) = do
  nf <- whnf scrut        
  case nf of 
    (DCon d args) -> f mtchs where
      f (Match bnd : alts) = (do
          (pat, br) <- Unbound.unbind bnd
          ss <- patternMatches (Arg Runtime nf) pat 
          whnf (Unbound.substs ss br)) 
            `catchError` \ _ -> f alts
      f [] = Env.err $ [DS "Internal error: couldn't find a matching",
                    DS "branch for", DD nf, DS "in"] ++ (map DD mtchs)
    _ -> return (Case nf mtchs){- STUBWITH -}            
-- all other terms are already in WHNF
-- don't do anything special for them
whnf tm = return tm


{- SOLN DATA -}
-- | Determine whether the pattern matches the argument
-- If so return the appropriate substitution
-- otherwise throws an error
patternMatches :: Arg -> Pattern -> TcMonad [(TName, Term)]
patternMatches (Arg _ t) (PatVar x) = return [(x, t)]
patternMatches (Arg Runtime t) pat = do
  nf <- whnf t
  case (nf, pat) of 
    (DCon d [], PatCon d' pats)   | d == d' -> return []
    (DCon d args, PatCon d' pats) | d == d' -> 
       concat <$> zipWithM patternMatches args (map fst pats)
    _ -> Env.err [DS "arg", DD nf, DS "doesn't match pattern", DD pat]
patternMatches (Arg Erased _) pat = do
  Env.err [DS "Cannot match against irrelevant args"]
{- STUBWITH -}

