module Compile where

import qualified Syntax as Pi
import TypeCheck
import Language.Haskell.Syntax

noLoc :: SrcLoc
noLoc = undefined

newtype C a = C a 
  deriving (Monad)

compileModule :: Pi.Module -> TcMonad HsModule
compileModule mod = do
  let name = Module (Pi.moduleName mod)
  imports <- mapM compileImport (Pi.moduleImports mod)
  decls   <- mapM compileDecl   (Pi.moduleEntries mod)
  return (HsModule noLoc name Nothing imports decls)

compileImport :: Pi.ModuleImport -> TcMonad HsImportDecl        
compileImport = undefined

compileDecl :: Pi.Decl -> TcMonad HsDecl 
compileDecl (Sig name Type)  = undefined
compileDecl (Sig name term)  = undefined
compileDecl (Def name term)  = undefined
compileDecl (Data name tele constr) = undefined

-- try to produce a Haskell type that corresponds to the 
-- given Pi type. If this is impossible, produce ()
compileType :: Pi.Type -> TcMonad HsType
compileType _ = Nothing

compileTName :: Pi.TName -> HsName
compileTName name = (HsIdent (name2string name))
               
compileTerm :: Pi.Term -> TcMonad HsExp
compileTerm Type = err ["Not an expression"]
compileTerm (Var name) = HsVar (UnQual (compileTName name)
compileTerm (Lam bnd) = do
  ((name, _), body) <- unbind bnd
  exp <- compileTerm body
  HsLambda noLoc [HsPVar (compileTName name)] exp
compileTerm (App e1 e2) = do
  