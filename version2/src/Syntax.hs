{- PiForall language, OPLSS -}
{-# LANGUAGE TemplateHaskell #-}

-- | The abstract syntax of the simple dependently typed language
-- See comment at the top of 'Parser' for the concrete syntax of this language
module Syntax where

import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Text.ParserCombinators.Parsec.Pos (SourcePos, newPos)
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.TH (makeClosedAlpha)

-- We use a small bit of Template Haskell to derive the instance
-- of the Alpha class for source positions.
-- TODO: this does not equate the source positions, we still need
-- to ignore them
makeClosedAlpha ''SourcePos

-- We want to ignore source positions during comparison, so the definition
-- above is equivalent to the following:
{-
instance Unbound.Alpha SourcePos where
   aeq' _ _ _ = True
   fvAny' _ _ = pure
   open _ _ = id
   close _ _ = id
   isPat _ = mempty
   isTerm _ = mempty
   nthPatFind _ = undefined
   namePatFind _ = undefined
   swaps' _ _ = id
   freshen' _ x = return (x, mempty)
   lfreshen' _ x cont = cont x mempty
-}

-- Substitutions also ignore source positions
instance Unbound.Subst b SourcePos where subst _ _ = id; substs _ = id



-----------------------------------------

-- * Names

-----------------------------------------

-- | For variable names, we use the Unbound library to
-- automatically generate free variable, substitution,
-- and alpha-equality function.
type TName = Unbound.Name Term

-- | module names
type MName = String

-- | type constructor names
type TCName = String

-- | data constructor names
type DCName = String

-----------------------------------------

-- * Core language

-----------------------------------------

-- | Combined syntax for types and terms 
-- (type synonym for documentation)
type Type = Term

-- | basic language
data Term
  = -- | type of types
    Type
  | -- | variables
    Var TName
  | -- | abstraction
    Lam (Unbound.Bind (TName , Unbound.Embed Annot) Term)
  | -- | application
    App Term Arg
  | -- | function type
    Pi (Unbound.Bind (TName , Unbound.Embed Term) Term)
  | -- | Annotated terms `( x : A )`
    Ann Term Term
  | -- | parenthesized term, useful for printing
    Paren Term
  | -- | marked source position, for error messages
    Pos SourcePos Term
  | -- | an axiom 'TRUSTME', inhabits all types
    TrustMe Annot
  | -- | The type with a single inhabitant `One`
    TyUnit
  | -- | The inhabitant, written `tt`
    LitUnit
  | -- | The type with two inhabitants (homework)
    TyBool
  | -- | True and False
    LitBool Bool
  | -- | If expression for eliminating booleans
    If Term Term Term Annot
  | -- | sigma type `{ x : A | B }`   -- homework
    Sigma (Unbound.Bind (TName, Unbound.Embed Term) Term)
  | -- | introduction for sigmas `( a , b )`
    Prod Term Term Annot
  | -- | elimination form  `pcase p of (x,y) -> p`
    Pcase Term (Unbound.Bind (TName, TName) Term) Annot
  | -- | let expression, introduces a new (potentially recursive) -- homwork
    -- definition in the ctx
    Let (Unbound.Bind (TName, Unbound.Embed Term) Term )
  
    | -- | Equality type  `a = b`
    TyEq Term Term
  | -- | Proof of equality
    Refl Annot
  | -- | equality elimination
    Subst Term Term Annot
  | -- | witness to an equality contradiction
    Contra Term Annot 
   
    
  
  deriving (Show, Generic, Typeable, Unbound.Alpha)


-- | An argument to a function.
data Arg = Arg { unArg :: Term}
  deriving (Show, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)


-- | An 'Annot' is optional type information
newtype Annot = Annot (Maybe Term) 
  deriving (Show, Generic, Typeable) 
  deriving anyclass (Unbound.Subst Term)





-----------------------------------------

-- * Modules and declarations

-----------------------------------------

-- | A Module has a name, a list of imports, a list of declarations,
--   and a set of constructor names (which affect parsing).
data Module = Module
  { moduleName :: MName,
    moduleImports :: [ModuleImport],
    moduleEntries :: [Decl] 
  }
  deriving (Show, Generic, Typeable)

newtype ModuleImport = ModuleImport MName
  deriving (Show, Eq, Generic, Typeable)

data Sig = S {sigName :: TName,  sigType :: Type }
  deriving (Show, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)

mkSig :: TName -> Type -> Sig
mkSig n t = S n  t

-- | Declarations are the components of modules
data Decl
  = -- | Declaration for the type of a term
    Sig Sig
  | -- | The definition of a particular name, must
    -- already have a type declaration in scope
    Def TName Term
  | -- | A potentially (recursive) definition of
    -- a particular name, must be declared
    RecDef TName Term 
  deriving (Show, Generic, Typeable)



-- * Auxiliary functions on syntax




-- | Default name for '_' occurring in patterns
wildcardName :: TName
wildcardName = Unbound.string2Name "_"

-- | empty Annotation
noAnn :: Annot
noAnn = Annot Nothing

-- | Partial inverse of Pos
unPos :: Term -> Maybe SourcePos
unPos (Pos p _) = Just p
unPos _ = Nothing

-- | Tries to find a Pos anywhere inside a term
unPosDeep :: Term -> Maybe SourcePos
unPosDeep = unPos -- something (mkQ Nothing unPos) -- TODO: Generic version of this

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Term -> SourcePos
unPosFlaky t = fromMaybe (newPos "unknown location" 0 0) (unPosDeep t)



-----------------

-- * Alpha equivalence and free variables

{- We use the unbound library to mark the binding occurrences of
   variables in the syntax. That allows us to automatically derive
   functions for alpha-equivalence, free variables and substitution
   using the default class instances below.
-}

-- Among other things, the Alpha class enables the following
-- functions:
--    aeq :: Alpha a => a -> a -> Bool
--    fv  :: Alpha a => a -> [Unbound.Name a]

------------------

instance Unbound.Alpha Annot where
  -- override default behavior so that type annotations are ignored
  -- when comparing for alpha-equivalence
  aeq' _ _ _ = True

-----------------

-- * Substitution

-- The Subst class derives capture-avoiding substitution
-- It has two parameters because the sort of thing we are substituting
-- for may not be the same as what we are substituting into.

-- class Subst b a where
--    subst  :: Name b -> b -> a -> a       -- single substitution
--    substs :: [(Name b, b)] -> a -> a     -- multiple substitution

------------------

instance Unbound.Subst Term Term where
  isvar (Var x) = Just (Unbound.SubstName x)
  isvar _ = Nothing



