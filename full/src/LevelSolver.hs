module LevelSolver where

import Syntax

import Data.Char as Char
import qualified Text.Read as Read

import Data.SBV as SBV
import Data.SBV.Internals

import Data.SBV.Control
import Control.Monad
import qualified Data.Map as Map
import qualified Data.List as List

import Control.Monad.Writer
import qualified Unbound.Generics.LocallyNameless as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound

import Debug.Trace

fvs :: [LevelConstraint] -> [LName]
fvs cs = List.nub (concatMap fv cs) where
  fv :: LevelConstraint -> [LName]
  fv = Unbound.toListOf Unbound.fv


solveConstraints :: [LevelConstraint] -> IO [(LName, Level)]
solveConstraints cs = do
  let goal = makeGoal cs
  SatResult result <- sat goal
  if modelExists result then
    let ss1 = Map.toList (getModelDictionary result) in
    return (modelToSubst ss1)
  else do
    print "no model!"
    return []

{-
  ss <- case result of
    Unsatisfiable sc m_ss -> do
      print "Unsat"
      print m_ss
      return []
    Satisfiable sc sm -> do
      print "satisfiable"
      print sm
      return (modelToSubst sm)
    DeltaSat sc m_s sm -> do
      print "delta sat"
      return []
    SatExtField sc sm -> do
      print "satextfield"
      print sm
      return (modelToSubst sm)
    Unknown sc sru -> do
      print "unknown"
      return []
    ProofError sc ss m_sr -> do
      print "proof error"
      return []
  return $ filter relevant ss
-}

mkName :: String -> Maybe LName
mkName str = name where
  (letters, numbers) = span Char.isAlpha str
  name = case Read.readMaybe numbers of
            Just i -> Just $ Unbound.makeName letters (i :: Integer)
            Nothing ->
              if numbers == [] then
                  Just (Unbound.string2Name letters)
              else
                  Nothing

modelToSubst :: [(String, CV)] -> [(LName, Level)]
modelToSubst = concatMap f where
  f (str, CV _ (CInteger i)) = case mkName str of
      Just n -> [(n, LConst (fromInteger i))]
      Nothing -> []
  f (str, cv) = error $ "no integer solution" ++ show cv


makeGoal :: [LevelConstraint] -> Predicate
makeGoal cs = do
  let vs = fvs cs
  varmap <- mapM (\v -> do
                    x <- SBV.sInteger (show v)
                    constrain $ 0 .<= x
                    return (v,x)) vs
  mapM_ (`process` varmap) cs
  SBV.forSome [] sTrue
  -- minimize "goal" (sum (map snd vars))

type Vars = [(LName, SInteger)]

simplify :: Level -> Level
simplify (LConst x) = LConst x
simplify (LVar x) = LVar x
simplify (LAdd l1 l2) =
  case (simplify l1, simplify l2) of
    (LConst j, LConst k) -> LConst (j + k)
    (s1,s2) -> LAdd s1 s2

symLevel :: Level -> Vars -> Symbolic SInteger
symLevel (LConst x) = \vs -> 
  return (fromInteger (toInteger x))
symLevel (LVar x) = \vars ->
  return $ case lookup x vars of
              Just y -> y
              Nothing -> error "BUG" 
symLevel (LAdd l1 l2) = \vs -> do
  sl1 <- symLevel l1 vs
  sl2 <- symLevel l2 vs
  return $ sl1 + sl2

process :: LevelConstraint -> Vars -> Symbolic ()
process (Eq l1 l2) vars = do
  sl1 <- symLevel l1 vars
  sl2 <- symLevel l2 vars
  constrain $ sl1 .== sl2
process (Le l1 l2) vars =  do
  sl1 <- symLevel l1 vars
  sl2 <- symLevel l2 vars
  constrain $ sl1 .<= sl2
process (Lt l1 l2) vars =  do
  sl1 <- symLevel l1 vars
  sl2 <- symLevel l2 vars
  constrain $ sl1 .< sl2
