{- PiForall language, OPLSS -}

{-# LANGUAGE TemplateHaskell, 
             FlexibleInstances, 
             MultiParamTypeClasses, 
             FlexibleContexts, 
             UndecidableInstances, 
             ViewPatterns, 
             EmptyDataDecls #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-orphans #-}

-- | The abstract syntax of the simple dependently typed language
-- See comment at the top of 'Parser' for the concrete syntax

module Syntax where

import Generics.RepLib hiding (Data,Refl)
import Unbound.LocallyNameless hiding (Data,Refl)   
import Text.ParserCombinators.Parsec.Pos       
import Data.Maybe (fromMaybe)

-----------------------------------------
-- * Variable names
-----------------------------------------

-- | term names, use unbound library to 
-- automatically generate fv, subst, alpha-eq
type TName = Name Term

-- | module names
type MName  = String

-- | type constructor names
type TCName = String

-- | data constructor names
type DCName = String

-----------------------------------------
-- * Core language
-----------------------------------------


-- Type abbreviation for documentation
type Type = Term

data Term = 
   -- basic language
     Type                               -- ^ type of types
   | Var TName                          -- ^ variables      
   | Lam (Bind (TName, Embed Annot) Term)             
                                        -- ^ abstraction    
   | App Term Term                      -- ^ application    
   | Pi (Bind (TName, Embed Term) Term) -- ^ function type

   -- practical matters for surface language
   | Ann Term Term            -- ^ Annotated terms `( x : A )`   
   | Paren Term               -- ^ parenthesized term, useful for printing
   | Pos SourcePos Term       -- ^ marked source position, for error messages
     
   -- conveniences  
   | TrustMe Annot            -- ^ an axiom 'TRUSTME', inhabits all types 
   
   -- unit  
   | TyUnit                   -- ^ The type with a single inhabitant `One`
   | LitUnit                  -- ^ The inhabitant, written `tt`
     
   -- homework: boolean expressions
   | TyBool                   -- ^ The type with two inhabitants
   | LitBool Bool             -- ^ True and False
   | If Term Term Term Annot  -- ^ If expression for eliminating booleans

   -- homework sigma types 
   | Sigma (Bind (TName, Embed Term) Term)
     -- ^ sigma type `{ x : A | B }` 
   | Prod Term Term Annot
     -- ^ introduction for sigmas `( a , b )`
   | Pcase Term (Bind (TName, TName) Term) Annot
     -- ^ elimination form  `pcase p of (x,y) -> p`

   -- homework let expression
   | Let (Bind (TName, Embed Term) Term)
     -- ^ let expression, introduces a new (potentially recursive) 
     -- definition in the ctx
     


     
     
                 deriving (Show)
               
-- | An 'Annot' is optional type information               
newtype Annot = Annot (Maybe Term) deriving Show            



-----------------------------------------
-- * Modules and declarations
-----------------------------------------

-- | A Module has a name, a list of imports, a list of declarations,
--   and a set of constructor names (which affect parsing).     
data Module = Module { moduleName         :: MName,
                       moduleImports      :: [ModuleImport],
                       moduleEntries      :: [Decl]
                       
                     }
              
  deriving (Show)

newtype ModuleImport = ModuleImport MName
  deriving (Show,Eq)



-- | Declarations are the components of modules
data Decl = Sig     TName  Term
           -- ^ Declaration for the type of a term
          | Def     TName  Term
            -- ^ The definition of a particular name, must 
            -- already have a type declaration in scope
          | RecDef TName Term 
            
  deriving (Show)



-------------
-- * Auxiliary functions on syntax
-------------




-- | Default name for '_' occurring in patterns
wildcardName :: TName
wildcardName = string2Name "_"

-- | empty Annotation
noAnn :: Annot   
noAnn = Annot Nothing

-- | Partial inverse of Pos
unPos :: Term -> Maybe SourcePos
unPos (Pos p _) = Just p
unPos _         = Nothing

-- | Tries to find a Pos anywhere inside a term
unPosDeep :: Term -> Maybe SourcePos
unPosDeep = something (mkQ Nothing unPos)

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Term -> SourcePos
unPosFlaky t = fromMaybe (newPos "unknown location" 0 0) (unPosDeep t)



        
                          
-----------------
-- * Alpha equivalence, free variables and substitution.
------------------

{- We use the unbound library to mark the binding occurrences of
   variables in the syntax. That allows us to automatically derive
   functions for alpha-equivalence, free variables and substitution
   using the template haskell directives and default class instances 
   below. 
-}

-- Defining SourcePos abstractly means that they get ignored 
-- when comparing terms.
derive_abstract [''SourcePos]
instance Alpha SourcePos
instance Subst b SourcePos

derive [''Term, 
        ''Module, ''Decl, 
        ''ModuleImport, 
        ''Annot]

-- Among other things, the Alpha class enables the following
-- functions:
--    aeq :: Alpha a => a -> a -> Bool
--    fv  :: Alpha a => a -> [Name a]

instance Alpha Term

instance Alpha Annot where
    -- override default behavior so that type annotations are ignored
    -- when comparing for alpha-equivalence
    aeq' _ _ _ = True

-- The subst class derives capture-avoiding substitution
-- It has two parameters because the sort of thing we are substiting
-- for may not be the same as what we are substituting into:

-- class Subst b a where
--    subst  :: Name b -> b -> a -> a       -- single substitution
--    substs :: [(Name b, b)] -> a -> a     -- multiple substitution

instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing


instance Subst Term Annot

