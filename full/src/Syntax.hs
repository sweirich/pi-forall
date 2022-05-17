{- PiForall language, OPLSS -}

-- | The abstract syntax of the simple dependently typed language
-- See comment at the top of 'Parser' for the concrete syntax of this language
module Syntax where

import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Text.ParserCombinators.Parsec.Pos (SourcePos, initialPos, newPos)
import Unbound.Generics.LocallyNameless qualified as Unbound

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
  = -- | type of types  `Type`
    Type
  | -- | variables  `x`
    Var TName
  | -- | abstraction  `\x. a`
    Lam (Unbound.Bind (TName {- SOLN EP -}, Epsilon {- STUBWITH -}, Unbound.Embed Annot) Term)
  | -- | application `a b`
    App Term Arg
  | -- | function type   `(x : A) -> B`
    Pi (Unbound.Bind (TName {- SOLN EP -}, Epsilon {- STUBWITH -}, Unbound.Embed Term) Term)
  | -- | Annotated terms `( x : A )`
    Ann Term Term
  | -- | parenthesized term, useful for printing
    Paren Term
  | -- | marked source position, for error messages
    Pos SourcePos Term
  | -- | an axiom 'TRUSTME', inhabits all types
    TrustMe Annot
  | -- | a directive to the type checker to print out the current context (like a typed hole)
    PrintMe Annot
  | -- | let expression, introduces a new (potentially recursive) definition in the ctx
    -- | `let x = a in b`
    Let (Unbound.Bind (TName, Unbound.Embed Term) Term)
  | -- | The type with a single inhabitant `Unit`
    TyUnit
  | -- | The inhabitant, written `()`
    LitUnit
  | -- | The type with two inhabitants (homework) `Bool`
    TyBool
  | -- | True and False
    LitBool Bool
  | -- | If expression for eliminating booleans
    If Term Term Term Annot
  | -- | sigma type `{ x : A | B }`   -- homework
    Sigma (Unbound.Bind (TName, Unbound.Embed Term) Term)
  | -- | introduction for sigmas `( a , b )`
    Prod Term Term Annot
  | -- | elimination form  `let (x,y) = a in b`
    LetPair Term (Unbound.Bind (TName, TName) Term) Annot

     | -- | Equality type  `a = b`
    TyEq Term Term
  | -- | Proof of equality `refl`
    Refl Annot
  | -- | equality elimination  `subst a by pf`
    Subst Term Term Annot
  | -- | witness to an equality contradiction
    Contra Term Annot
   

     | -- | type constructors (fully applied)
    TCon TCName [Arg]
  | -- | term constructors (fully applied)
    DCon DCName [Arg] Annot
  | -- | case analysis  `case a of matches`
    Case Term [Match] Annot
  
  deriving (Show, Generic, Typeable, Unbound.Alpha)

-- | An argument to a function
data Arg = Arg {argEp :: Epsilon,  unArg :: Term}
  deriving (Show, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)

-- | An 'Annot' is optional type information
newtype Annot = Annot (Maybe Term)
  deriving (Show, Generic, Typeable)
  deriving anyclass (Unbound.Subst Term)

-- | Epsilon annotates the stage of a variable
data Epsilon
  = Runtime
  | Erased
  deriving
    ( Eq,
      Show,
      Read,
      Bounded,
      Ord,
      Generic,
      Typeable,
      Unbound.Alpha,
      Unbound.Subst Term
    )



-- | A 'Match' represents a case alternative
data Match = Match (Unbound.Bind Pattern Term)
  deriving (Show, Generic, Typeable, Unbound.Alpha)
  deriving anyclass (Unbound.Subst Term)

-- | The patterns of case expressions bind all variables
-- in their respective branches.
data Pattern
  = PatCon DCName [(Pattern, Epsilon)]
  | PatVar TName
  | PatBool Bool -- True / False
  | PatUnit -- unit
  deriving (Show, Eq, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)



-----------------------------------------

-- * Modules and declarations

-----------------------------------------

-- | A Module has a name, a list of imports, a list of declarations,
--   and a set of constructor names (which affect parsing).
data Module = Module
  { moduleName :: MName,
    moduleImports :: [ModuleImport],
    moduleEntries :: [Decl] {- SOLN DATA -},
    moduleConstructors :: ConstructorNames {- STUBWITH -}
  }
  deriving (Show, Generic, Typeable)

newtype ModuleImport = ModuleImport MName
  deriving (Show, Eq, Generic, Typeable)

data Sig = S {sigName :: TName {- SOLN EP -}, sigEp :: Epsilon {- STUBWITH -}, sigType :: Type}
  deriving (Show, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)

mkSig :: TName -> Type -> Sig
mkSig n t = S n Runtime  t

-- | Declarations are the components of modules
data Decl
  = -- | Declaration for the type of a term
    Sig Sig
  | -- | The definition of a particular name, must
    -- already have a type declaration in scope
    Def TName Term
  | -- | A potentially (recursive) definition of
    -- a particular name, must be declared
    RecDef TName Term   | -- | Declaration for a datatype including all of
    -- its data constructors
    Data TCName Telescope [ConstructorDef]
  | -- | An abstract view of a datatype. Does
    -- not include any information about its data
    -- constructors
    DataSig TCName Telescope
  
  deriving (Show, Generic, Typeable)

-- | The names of type/data constructors used in the module
data ConstructorNames = ConstructorNames
  { tconNames :: Set String,
    dconNames :: Set String
  }
  deriving (Show, Eq, Ord, Generic, Typeable)

-- | A Data constructor has a name and a telescope of arguments
data ConstructorDef = ConstructorDef SourcePos DCName Telescope
  deriving (Show, Generic, Typeable)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

-- * Telescopes

data Assn
  = AssnSig Sig
  | AssnProp Prop
  deriving (Show, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)

isAssnSig :: Assn -> Bool
isAssnSig (AssnSig _) = True
isAssnSig _ = False

data Prop = Eq Term Term
  deriving (Show, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)

-- | A telescope is like a first class context. It binds each name
-- in the rest of the telescope.  For example
--     Delta = x:* , y:x, y = w, empty
newtype Telescope = Telescope [Assn]
  deriving (Show, Generic, Typeable)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)



-- * Auxiliary functions on syntax

-- | empty set of constructor names
emptyConstructorNames :: ConstructorNames
emptyConstructorNames = ConstructorNames Set.empty Set.empty 

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

-- | Is this the syntax of a literal (natural) number
isNumeral :: Term -> Maybe Int
isNumeral (Pos _ t) = isNumeral t
isNumeral (Paren t) = isNumeral t
isNumeral (DCon c [] _) | c == "Zero" = Just 0
isNumeral (DCon c [Arg _ t] _) | c == "Succ" =
  do n <- isNumeral t; return (n + 1)
isNumeral _ = Nothing

-- | Is this pattern a variable
isPatVar :: Pattern -> Bool
isPatVar (PatVar _) = True
isPatVar _ = False



-----------------

-- We use the unbound-generics library to mark the binding occurrences of
-- variables in the syntax. That allows us to automatically derive
-- functions for alpha-equivalence, free variables and substitution
-- using generic programming. 


-- * Substitution

-- The Subst class derives capture-avoiding substitution
-- It has two parameters because the sort of thing we are substituting
-- for may not be the same as what we are substituting into.

-- class Subst b a where
--    subst  :: Name b -> b -> a -> a       -- single substitution
--    substs :: [(Name b, b)] -> a -> a     -- multiple substitution

instance Unbound.Subst Term Term where
  isvar (Var x) = Just (Unbound.SubstName x)
  isvar _ = Nothing

------------------

-- * Alpha equivalence and free variables

-- Among other things, the Alpha class enables the following
-- functions:
--    -- Compare terms for alpha equivalence
--    aeq :: Alpha a => a -> a -> Bool
--    -- Calculate the free variables of a term
--    fv  :: Alpha a => a -> [Unbound.Name a]

------------------

instance Unbound.Alpha Annot where
  -- override default behavior so that type annotations are ignored
  -- when comparing for alpha-equivalence
  aeq' _ _ _ = True
  fvAny' _ _ = pure
  open _ _ = id
  close _ _ = id
  isPat _ = mempty
  isTerm _ = mempty
  nthPatFind _ = mempty
  namePatFind _ = mempty
  swaps' _ _ = id
  freshen' _ x = return (x, mempty)
  lfreshen' _ x cont = cont x mempty
  acompare' _ _ _ = EQ

-----------------

-- * Source Positions

-- We want to ignore source positions during comparison
instance Unbound.Alpha SourcePos where
  aeq' _ _ _ = True
  fvAny' _ _ = pure
  open _ _ = id
  close _ _ = id
  isPat _ = mempty
  isTerm _ = mempty
  nthPatFind _ = mempty
  namePatFind _ = mempty
  swaps' _ _ = id
  freshen' _ x = return (x, mempty)
  lfreshen' _ x cont = cont x mempty
  acompare' _ _ _ = EQ

-- Substitutions ignore source positions
instance Unbound.Subst b SourcePos where subst _ _ = id; substs _ = id

-- Internally generated source positions
internalPos :: SourcePos
internalPos = initialPos "internal"