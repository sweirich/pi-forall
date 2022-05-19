module Main where

import Test.QuickCheck
import Test.HUnit
import Environment
import PrettyPrint
import TypeCheck
import Syntax
import Control.Monad.Except
import Modules
import Text.PrettyPrint.HughesPJ (render)
import Text.ParserCombinators.Parsec.Error 


main :: IO ()
main = do
   _ <- runTestTT $ TestList [
                testFile "Lec1.pi"
            , testFile "Hw1.pi"  
            , testFile "Lec2.pi"
            , testFile "Hw2.pi"  
            , testFile "Lec3.pi"
            , testFile "Fin1.pi"
            , testFile "Lec4.pi"
                
            , testFile "Logic.pi"  
            , testFile "Equality.pi"  
            , testFile "Product.pi"  
            , testFile "Nat.pi"  
            , testFile "Fin.pi"  
            , testFile "Vec.pi"  
            
            , testFile "Lambda0.pi"
            , testFile "Lambda1.pi"
            , testFile "Lambda2.pi"
            ]
   return ()


exitWith :: Either a b -> (a -> IO b) -> IO b
exitWith (Left a) f = f a
exitWith (Right b) f = return b

-- | Type check the given file    
testFile :: String -> Test  
testFile name = name ~: TestCase $ do
  v <- runExceptT (getModules ["pi"] name)
  val <- v `exitWith` (\b -> assertFailure $ "Parse error: " ++ render (disp b))
  d <- runTcMonad emptyEnv (tcModules val)
  defs <- d `exitWith` (\s -> assertFailure $ "Type error:" ++ render (disp s))
  putStrLn $ render $ disp (last defs)