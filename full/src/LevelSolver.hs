module LevelSolver where

import Syntax

import Data.Char as Char
import qualified Text.Read as Read

import Data.SBV
import Data.SBV.Internals

import Data.SBV.Control
import Control.Monad

import Control.Monad.Writer
import qualified Unbound.Generics.LocallyNameless as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound

solveConstraints :: [LevelConstraint] -> IO [(LName, Level)]
solveConstraints cs = do
  let goal = makeGoal cs
  let fv :: LevelConstraint -> [LName]
      fv = Unbound.toListOf Unbound.fv
  let vars = concatMap fv cs
  let relevant (x,_) = x `elem` vars
  LexicographicResult result <- optimize Lexicographic goal
  ss <- case result of
    Unsatisfiable sc m_ss -> do
      print "Unsat"
      print m_ss
      return []
    Satisfiable sc sm -> do
      print "satisfiable"
      return (modelToSubst sm)
    DeltaSat sc m_s sm -> do
      print "delta sat"
      return []
    SatExtField sc sm -> do
      print "satextfield"
      return (modelToSubst sm)
    Unknown sc sru -> do
      print "unknown"
      return []
    ProofError sc ss m_sr -> do
      print "proof error"
      return []
  return $ filter relevant ss

mkName :: String -> LName
mkName str = name where
  (letters, numbers) = span Char.isAlpha str
  name = case Read.readMaybe numbers of
            Just i -> Unbound.makeName letters (i :: Integer)
            Nothing -> Unbound.string2Name letters

modelToSubst :: SMTModel -> [(LName, Level)]
modelToSubst model = map f (modelAssocs model) where
  f (str, CV _ (CInteger i)) =
    (mkName str, LConst (fromInteger i))
  f (str, cv) = error $ "no integer solution" ++ show cv


makeGoal :: [LevelConstraint] -> Goal
makeGoal cs = do
  ((), vars) <- runWriterT (mapM_ process cs)
  minimize "goal" (sum (map snd vars))

type Vars = [(LName, SInteger)]

symLevel :: Level -> WriterT Vars Symbolic SInteger
symLevel (LConst x) = return (fromInteger (toInteger x))
symLevel (LVar x) = do
  sv <- lift $ sInteger (show x)
  lift $ constrain $ 0 .<= sv
  tell [(x,sv)]
  return sv
symLevel (LAdd l1 l2) = do
  sl1 <- symLevel l1
  sl2 <- symLevel l2
  return $ sl1 + sl2

process :: LevelConstraint -> WriterT Vars Symbolic ()
process (Eq l1 l2) = do
  sl1 <- symLevel l1
  sl2 <- symLevel l2
  lift $ constrain $ sl1 .== sl2
process (Le l1 l2) =  do
  sl1 <- symLevel l1
  sl2 <- symLevel l2
  lift $ constrain $ sl1 .<= sl2
process (Lt l1 l2) =  do
  sl1 <- symLevel l1
  sl2 <- symLevel l2
  lift $ constrain $ sl1 .< sl2
