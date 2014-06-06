{- PiForall language, OPLSS -}

{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

-- | The command line interface to the pi type checker. 
-- Also provides functions for type checking individual terms
-- and files.
module Main(goFilename,go,main, test) where

import Modules (getModules)
import PrettyPrint
import Environment
import TypeCheck
import Parser

import Text.PrettyPrint.HughesPJ (render)
import Text.ParserCombinators.Parsec.Error 

import Control.Monad.Error

import System.Environment(getArgs)
import System.Exit (exitFailure,exitSuccess)
import System.FilePath (splitFileName)

exitWith :: Either a b -> (a -> IO ()) -> IO b
exitWith res f = 
  case res of 
    Left x -> f x >> exitFailure 
    Right y -> return y
    
-- | Type check the given string in the empty environment
go :: String -> IO ()
go str = do
  case parseExpr str of
    Left parseError -> putParseError parseError
    Right term -> do 
      putStrLn "parsed as"
      putStrLn $ render $ disp term
      res <- runTcMonad emptyEnv (inferType term)
      case res of 
        Left typeError -> putTypeError typeError
        Right (aterm, ty) -> do
          putStrLn $ render $ disp aterm
          putStrLn "typed with type"
          putStrLn $ render $ disp ty
  
-- | Display a parse error to the user  
putParseError :: ParseError -> IO ()  
putParseError parseError = do
  putStrLn $ render $ disp $ errorPos parseError
  putStrLn $ show parseError
  
-- | Display a type error to the user  
putTypeError :: Disp d => d -> IO ()  
putTypeError typeError = do 
  putStrLn "Type Error:"
  putStrLn $ render $ disp typeError
      
-- | Type check the given file    
goFilename :: String -> IO ()  
goFilename pathToMainFile = do
  let prefixes = currentDir : mainFilePrefix : []
      (mainFilePrefix, name) = splitFileName pathToMainFile
      currentDir = "" 
  putStrLn $ "processing " ++ name ++ "..."
  v <- runErrorT (getModules prefixes name)
  val <- v `exitWith` putParseError
  putStrLn "type checking..."
  d <- runTcMonad emptyEnv (tcModules val)
  defs <- d `exitWith` putTypeError
  putStrLn $ render $ disp (last defs)


test :: IO ()
test = do
  goFilename "../test/Lec1.pi"
  goFilename "../test/Hw1.pi"  
  goFilename "../test/Lec2.pi"
  goFilename "../test/Hw2.pi"  
  goFilename "../test/Lec3.pi"
  goFilename "../test/Fin1.pi"
  goFilename "../test/Lec4.pi"
      
  goFilename "../test/Logic.pi"  
  goFilename "../test/Equality.pi"  
  goFilename "../test/Product.pi"  
  goFilename "../test/Nat.pi"  
  goFilename "../test/Fin.pi"  
  goFilename "../test/Vec.pi"  
        
  

-- | 'pi <filename>' invokes the type checker on the given 
-- file and either prints the types of all definitions in the module
-- or prints an error message.
main :: IO ()
main = do
  [pathToMainFile] <- getArgs
  goFilename pathToMainFile
  exitSuccess
  
