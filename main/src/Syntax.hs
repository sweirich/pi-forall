{- PiForall language, OPLSS -}

-- | The abstract syntax of the simple dependently typed language
-- See comment at the top of 'Parser' for the concrete syntax of this language
module Syntax where

import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Typeable (Typeable)
import GHC.Generics (Generic,from)
import Text.ParserCombinators.Parsec.Pos (SourcePos, initialPos, newPos)
import Unbound.Generics.LocallyNameless qualified as Unbound
import Data.Function (on)

-----------------------------------------

-- * Names

-----------------------------------------

-- | For variable names, we use the Unbound library to
-- automatically generate free variable, substitution,
-- and alpha-equality function.
type TName = Unbound.Name Term

-- | module names
type MName = String

{- SOLN DATA -}

-- | type constructor names
type TCName = String

-- | data constructor names
type DCName = String

{- STUBWITH -}

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
    Lam (Unbound.Bind (TName {- SOLN EP -}, Epsilon {- STUBWITH -}) Term)
  | -- | application `a b`
    App Term Arg
  | -- | function type   `(x : A) -> B`
    Pi (Unbound.Bind (TName {- SOLN EP -}, Epsilon {- STUBWITH -}, Unbound.Embed Type) Type)
  | -- | Annotated terms `( a : A )`
    Ann Term Type
  | -- | marked source position, for error messages
    Pos SourcePos Term
  | -- | an axiom 'TRUSTME', inhabits all types
    TrustMe
  | -- | a directive to the type checker to print out the current context
    PrintMe
  | -- | let expression, introduces a new (recursive) definition in the ctx
    -- | `let x = a in b`
    Let (Unbound.Bind (TName, Unbound.Embed Term) Term)
  | -- | The type with a single inhabitant, called `Unit`
    TyUnit
  | -- | The inhabitant of `Unit`, written `()`
    LitUnit
  | -- | The type with two inhabitants (homework) `Bool`
    TyBool
  | -- | `True` and `False`
    LitBool Bool
  | -- | `if a then b1 else b2` expression for eliminating booleans
    If Term Term Term
  | -- | sigma type (homework), written `{ x : A | B }`  
    Sigma (Unbound.Bind (TName, Unbound.Embed Term) Term)
  | -- | introduction for sigmas `( a , b )`
    Prod Term Term
  | -- | elimination form  `let (x,y) = a in b`
    LetPair Term (Unbound.Bind (TName, TName) Term) 

   {- SOLN EQUAL -}
  | -- | Equality type  `a = b`
    TyEq Term Term
  | -- | Proof of equality `Refl`
    Refl 
  | -- | equality elimination  `subst a by pf`
    Subst Term Term 
  | -- | witness to an equality contradiction
    Contra Term
   {- STUBWITH -}

   {- SOLN DATA -}
  | -- | type constructors (fully applied)
    TCon TCName [Arg]
  | -- | term constructors (fully applied)
    DCon DCName [Arg] 
  | -- | case analysis  `case a of matches`
    Case Term [Match]
  {- STUBWITH -}
  deriving (Show, Generic)

-- | An argument to a function
data Arg = Arg {{- SOLN EP -} argEp :: Epsilon, {- STUBWITH -} unArg :: Term}
  deriving (Show, Generic, Unbound.Alpha, Unbound.Subst Term)

{- SOLN EP -}

-- | Epsilon annotates the stage of a variable
data Epsilon
  = Rel
  | Irr
  deriving
    ( Eq,
      Show,
      Read,
      Bounded,
      Enum,
      Ord,
      Generic,
      Unbound.Alpha,
      Unbound.Subst Term
    )

{- STUBWITH -}

{- SOLN DATA -}

-- | A 'Match' represents a case alternative
newtype Match = Match (Unbound.Bind Pattern Term)
  deriving (Show, Generic, Typeable)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

-- | The patterns of case expressions bind all variables
-- in their respective branches.
data Pattern
  = PatCon DCName [(Pattern, Epsilon)]
  | PatVar TName
  deriving (Show, Eq, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)

{- STUBWITH -}

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

data Sig = Sig {sigName :: TName {- SOLN EP -}, sigEp :: Epsilon {- STUBWITH -}, sigType :: Type}
  deriving (Show, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)

mkSig :: TName -> Type -> Sig
mkSig n = Sig n {- SOLN EP -} Rel {- STUBWITH -}

-- | Declarations are the components of modules
data Decl
  = -- | Declaration for the type of a term
    TypeSig Sig
  | -- | The definition of a particular name, must
    -- already have a type declaration in scope
    Def TName Term
  | -- | A potentially (recursive) definition of
    -- a particular name, must be declared
    RecDef TName Term {- SOLN EP -}
    -- | Adjust the context for relevance checking
  | Demote Epsilon {- STUBWITH -} {- SOLN DATA -}
  | -- | Declaration for a datatype including all of
    -- its data constructors
    Data TCName Telescope [ConstructorDef]
  | -- | An abstract view of a datatype. Does
    -- not include any information about its data
    -- constructors
    DataSig TCName Telescope
  {- STUBWITH -}
  deriving (Show, Generic, Typeable)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)
{- SOLN DATA -}


-- | The names of type/data constructors used in the module
data ConstructorNames = ConstructorNames
  { tconNames :: Set String,
    dconNames :: Set String
  }
  deriving (Show, Eq, Ord, Generic, Typeable)

-- | A Data constructor has a name and a telescope of arguments
data ConstructorDef = ConstructorDef SourcePos DCName Telescope
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

-- * Telescopes

-- | A telescope is like a first class context. It is a list of 
-- assumptions, binding each variable in terms that appear
-- later in the list. 
-- For example
--     Delta = [ x:Type , y:x, y = w ]
newtype Telescope = Telescope [Decl]
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

{- STUBWITH -}

-- * Auxiliary functions on syntax

{- SOLN DATA -}

-- | empty set of constructor names
emptyConstructorNames :: ConstructorNames
emptyConstructorNames = ConstructorNames initialTCNames initialDCNames {- STUBWITH -}

-- | Default name for '_' occurring in patterns
wildcardName :: TName
wildcardName = Unbound.string2Name "_"

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

{- SOLN DATA -}

-- | Is this the syntax of a literal (natural) number
isNumeral :: Term -> Maybe Int
isNumeral (Pos _ t) = isNumeral t
isNumeral (DCon c []) | c == "Zero" = Just 0
isNumeral (DCon c [Arg _ t]) | c == "Succ" =
  do n <- isNumeral t; return (n + 1)
isNumeral _ = Nothing

-- | Is this pattern a variable
isPatVar :: Pattern -> Bool
isPatVar (PatVar _) = True
isPatVar _ = False

xname :: Unbound.Name Term
xname = Unbound.string2Name "x"
yname :: Unbound.Name Term
yname = Unbound.string2Name "y"
aname :: Unbound.Name Term
aname = Unbound.string2Name "a"
bname :: Unbound.Name Term
bname = Unbound.string2Name "b"

preludeDataDecls :: [Decl]
preludeDataDecls = 
  [ Data sigmaName  sigmaTele      [prodConstructorDef]
  , Data tyUnitName (Telescope []) [unitConstructorDef]
  , Data boolName   (Telescope []) [falseConstructorDef, trueConstructorDef]
  ]  where
        trueConstructorDef = ConstructorDef internalPos trueName (Telescope [])
        falseConstructorDef = ConstructorDef internalPos falseName (Telescope [])

        unitConstructorDef = ConstructorDef internalPos litUnitName (Telescope []) 

        sigmaTele = Telescope [TypeSig sigA, TypeSig sigB]
        prodConstructorDef = ConstructorDef internalPos prodName (Telescope [TypeSig sigX, TypeSig sigY])
        sigA = Sig aname Rel Type
        sigB = Sig bname Rel (Pi (Unbound.bind (xname, Rel, Unbound.embed (Var aname)) Type))
        sigX = Sig xname Rel (Var aname)
        sigY = Sig yname Rel (App (Var bname) (Arg Rel (Var xname)))

-- prelude names
sigmaName :: TCName
sigmaName = "Sigma"
prodName :: DCName
prodName = "Product"
boolName :: TCName
boolName = "Bool"
trueName :: DCName
trueName = "True"
falseName :: DCName
falseName = "False"
tyUnitName :: TCName
tyUnitName = "Unit"
litUnitName :: DCName
litUnitName = "()"

initialTCNames :: Set TCName
initialTCNames = Set.fromList [sigmaName, boolName, tyUnitName]
initialDCNames :: Set DCName
initialDCNames = Set.fromList [prodName, trueName, falseName, litUnitName]

{- STUBWITH -}

-----------------

-- We use the unbound-generics library to mark the binding occurrences of
-- variables in the syntax. That allows us to automatically derive
-- functions for alpha-equivalence, free variables and substitution
-- using generic programming. 

------------------

-- * Alpha equivalence and free variables

-- Among other things, the Alpha class enables the following
-- functions:
--    -- Compare terms for alpha equivalence
--    aeq :: Alpha a => a -> a -> Bool
--    -- Calculate the free variables of a term
--    fv  :: Alpha a => a -> [Unbound.Name a]

-- For Terms, we'd like Alpha equivalence to ignore 
-- source positions and type annotations in terms.
-- We can add these special cases to the definition of `aeq'` 
-- and then defer all other cases to the generic version of 
-- the function.

instance Unbound.Alpha Term where
  aeq' ctx (Ann a _) b = Unbound.aeq' ctx a b
  aeq' ctx a (Ann b _) = Unbound.aeq' ctx a b
  aeq' ctx (Pos _ a) b = Unbound.aeq' ctx a b
  aeq' ctx a (Pos _ b) = Unbound.aeq' ctx a b
  aeq' ctx a b = (Unbound.gaeq ctx `on` from) a b

-- For example, all occurrences of annotations, source positions, and internal 
-- parenthesis are ignored by this definition.

-- >>> Unbound.aeq (Pos internalPos (Ann TyBool Type)) (Paren (Paren TyBool))
-- True

-- At the same time, the generic operation equates terms that differ only 
-- in the names of bound variables.

x0 :: TName
x0 = Unbound.string2Name "x"

y0 :: TName
y0 = Unbound.string2Name "y"

idx :: Term
idx = Lam (Unbound.bind (x0 {- SOLN EP -}, Rel {- STUBWITH -}) (Var x0))

idy :: Term
idy = Lam (Unbound.bind (y0 {- SOLN EP -}, Rel {- STUBWITH -}) (Var y0))

-- >>> Unbound.aeq idx idy
-- True


---------------

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



pi1 :: Term 
pi1 = Pi (Unbound.bind (x0, {- SOLN EP -} Rel, {- STUBWITH -} Unbound.embed (Var x0)) (Var x0))

-- '(y : Bool) -> y'
pi2 :: Term 
pi2 = Pi (Unbound.bind (y0, {- SOLN EP -} Rel, {- STUBWITH -} Unbound.embed TyBool) (Var y0))

-- >>> Unbound.aeq (Unbound.subst x0 TyBool pi1) pi2
-- True



-----------------

-- * Source Positions

-- SourcePositions do not have an instance of the Generic class available
-- so we cannot automatically define their Alpha and Subst instances. Instead
-- we do by hand here. This also gives us a chance to ignore source 
-- positions during comparisons.
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
