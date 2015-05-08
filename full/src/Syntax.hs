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
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import Text.ParserCombinators.Parsec.Pos       
import Data.Set (Set)
import qualified Data.Set as S
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
     

   -- propositional equality
   | TyEq Term Term     -- ^ Equality type  `a = b`
   | Refl Annot         -- ^ Proof of equality
   | Subst Term Term Annot
                        -- ^ equality elimination
   | Contra Term Annot  -- ^ witness to an equality contradiction

   -- erasure
   | ErasedLam (Bind (TName, Embed Annot) Term)  -- ^ abstraction       
   | ErasedPi  (Bind (TName, Embed Term) Term)   -- ^ function type
   | ErasedApp Term Term                         -- ^ application
     
   -- datatypes
   | TCon String [Term]             -- ^ type constructors (fully applied)
   | DCon String [Arg] Annot        -- ^ term constructors 
      --- (fully applied, erased arguments first)
   | Case Term [Match] Annot        -- ^ case analysis
     
                 deriving (Show)
               
-- | An 'Annot' is optional type information               
newtype Annot = Annot (Maybe Term) deriving Show            

-- | A 'Match' represents a case alternative
data Match = Match (Bind Pattern Term) deriving (Show)

-- | The patterns of case expressions bind all variables 
-- in their respective branches.
data Pattern = PatCon DCName [(Pattern, Epsilon)]
             | PatVar TName deriving (Show, Eq)



-----------------------------------------
-- * Modules and declarations
-----------------------------------------

-- | A Module has a name, a list of imports, a list of declarations,
--   and a set of constructor names (which affect parsing).     
data Module = Module { moduleName         :: MName,
                       moduleImports      :: [ModuleImport],
                       moduleEntries      :: [Decl]
                     , moduleConstructors :: ConstructorNames
                       
                     }
              
  deriving (Show)

newtype ModuleImport = ModuleImport MName
  deriving (Show,Eq)

data ConstructorNames = ConstructorNames {
                          tconNames :: Set String,
                          dconNames :: Set String
                        }
  deriving (Show, Eq)


-- | Declarations are the components of modules
data Decl = Sig     TName  Term
           -- ^ Declaration for the type of a term
            
          | Def     TName  Term
            -- ^ The definition of a particular name, must 
            -- already have a type declaration in scope
            
          | RecDef TName Term 
            -- ^ A potentially (recursive) definition of 
            -- a particular name, must be declared 

          | Data    TCName Telescope [ConstructorDef]
            -- ^ Declaration for a datatype including all of 
            -- its data constructors
          | DataSig TCName Telescope 
            -- ^ An abstract view of a datatype. Does 
            -- not include any information about its data 
            -- constructors
            
  deriving (Show)

-- | A Data constructor has a name and a telescope of arguments
data ConstructorDef = ConstructorDef SourcePos DCName Telescope
  deriving (Show)
           
-------------
-- * Telescopes
-------------
-- | A telescope is like a first class context. It binds each name 
-- in the rest of the telescope.  For example   
--     Delta = x:* , y:x, y = w, empty
data Telescope = Empty
    | Cons   Epsilon TName Term Telescope
    | Constraint Term Term Telescope
  deriving (Show)
           
-- | Epsilon annotates the sort of a data constructor argument
data Epsilon = 
    Runtime 
  | Erased
     deriving (Eq,Show,Read,Bounded,Ord)

-- | An argument is tagged with whether it should be erased
data Arg  = Arg Epsilon Term deriving (Show)           


-------------
-- * Auxiliary functions on syntax
-------------

-- | empty set of constructor names
emptyConstructorNames :: ConstructorNames 
emptyConstructorNames = ConstructorNames S.empty S.empty

-- | Extract the term from an Arg
unArg :: Arg -> Term
unArg (Arg _ t) = t



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

-- | Is this the syntax of a literal (natural) number
isNumeral :: Term -> Maybe Int
isNumeral (Pos _ t) = isNumeral t
isNumeral (Paren t) = isNumeral t
isNumeral (DCon c [] _) | c== "Zero" = Just 0
isNumeral (DCon c [Arg _ t] _) | c==  "Succ" =
  do n <- isNumeral t ; return (n+1)
isNumeral _ = Nothing

-- | Is this pattern a variable
isPatVar :: Pattern -> Bool
isPatVar (PatVar _) = True
isPatVar _          = False


---------------------
-- * Erasure
---------------------   
   
class Erase a where        
  -- | erase all computationally irrelevant parts of an expression
  -- these include all typing annotations  
  -- irrelevant arguments are replaced by unit
  erase :: a -> a
        
instance Erase Term where
  erase (Var x)         = Var x
  erase (Lam bnd)    = Lam (bind (x, embed noAnn) (erase body))
    where ((x,unembed -> _), body) = unsafeUnbind bnd
  erase (App a1 a2)     = App (erase a1) (erase a2)
  erase (Type)          = Type 
  erase (Pi bnd)        = Pi (bind (x, embed (erase tyA)) (erase tyB))
    where ((x,unembed -> tyA), tyB) = unsafeUnbind bnd
  erase (Ann t1 t2)     = erase t1   
  erase (Paren t1)      = erase t1
  erase (Pos sp t)      = erase t
  erase (TrustMe _)     = TrustMe noAnn
  erase (TyUnit)        = TyUnit
  erase (LitUnit)       = LitUnit
  erase (TyBool)        = TyBool
  erase (LitBool b)     = LitBool b
  erase (If a b c _)    = If (erase a) (erase b) (erase c) noAnn
  erase (Let bnd)       = Let (bind (x,embed (erase rhs)) (erase body))
    where ((x,unembed -> rhs),body) = unsafeUnbind bnd
        
  erase (TyEq a b)       = TyEq (erase a) (erase b)
  erase (Refl _)         = Refl noAnn
  erase (Subst tm pf _)  = Subst (erase tm) (erase pf) noAnn
  erase (Contra tm _)    = Contra (erase tm) noAnn
                          
  erase (ErasedLam bnd) = ErasedLam (bind (x, embed noAnn) (erase body))
    where ((x,unembed -> _), body) = unsafeUnbind bnd
  erase (ErasedApp tm1 tm2) = ErasedApp (erase tm1) LitUnit
  erase (ErasedPi  bnd) = ErasedPi (bind (x, embed (erase tyA)) (erase tyB))
    where ((x,unembed -> tyA), tyB) = unsafeUnbind bnd
          
  erase (TCon n tms)    = TCon n (map erase tms)
  erase (DCon n args _) = DCon n (map erase args) noAnn
  erase (Case tm ms _)  = Case (erase tm) (map erase ms) noAnn
      
  erase (Sigma bnd)     = Sigma (bind (x, embed (erase tyA)) (erase tyB)) 
    where ((x,unembed->tyA),tyB) = unsafeUnbind bnd
  erase (Prod a b _)    = Prod (erase a) (erase b) noAnn
  erase (Pcase a bnd _) = 
    Pcase (erase a) (bind (x,y) (erase body)) noAnn where
       ((x,y),body) = unsafeUnbind bnd

instance Erase Match where
  erase (Match bnd) = Match (bind p (erase t)) where
    (p,t) = unsafeUnbind bnd 
    
instance Erase Arg where    
  erase (Arg Runtime t) = Arg Runtime (erase t)
  erase (Arg Erased t)  = Arg Erased  LitUnit
        
                          
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

derive [''Term, ''Match, ''Pattern, ''Telescope, ''Epsilon, 
        ''ConstructorDef, ''ConstructorNames, ''Arg, 
        ''Module, ''Decl, 
        ''ModuleImport, 
        ''Annot]

-- Among other things, the Alpha class enables the following
-- functions:
--    aeq :: Alpha a => a -> a -> Bool
--    fv  :: Alpha a => a -> [Name a]

instance Alpha Term where
  
instance Alpha Match
instance Alpha Pattern
instance Alpha Epsilon
instance Alpha Telescope
instance Alpha Arg
instance Alpha ConstructorDef

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

instance Subst Term Epsilon
instance Subst Term Match
instance Subst Term Pattern
instance Subst Term Telescope
instance Subst Term Arg
instance Subst Term ConstructorDef

instance Subst Term Annot

