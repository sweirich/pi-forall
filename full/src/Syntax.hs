{- pi-forall language -}

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
import Unbound.Generics.LocallyNameless.Unsafe qualified as Unbound
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

-- | type constructor names
type TCName = String

-- | data constructor names
type DCName = String


-- | level names
type LName = Unbound.Name Level

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
    Lam Rho (Unbound.Bind TName Term)
  | -- | application `a b`
    App Term Arg
  | -- | function type   `(x : A) -> B`
    Pi Epsilon Type (Unbound.Bind TName Type)
  | -- | annotated terms `( a : A )`
    Ann Term Type
  | -- | marked source position, for error messages
    Pos SourcePos Term
  | -- | an axiom 'TRUSTME', inhabits all types
    TrustMe
  | -- | a directive to the type checker to print out the current context
    PrintMe
  | -- | let expression, introduces a new (non-recursive) definition in the ctx
    -- | `let x = a in b`
    Let Term (Unbound.Bind TName Term)
  | -- | the type with a single inhabitant, called `Unit`
    TyUnit
  | -- | the inhabitant of `Unit`, written `()`
    LitUnit
  | -- | the type with two inhabitants (homework) `Bool`
    TyBool
  | -- | `True` and `False`
    LitBool Bool
  | -- | `if a then b1 else b2` expression for eliminating booleans
    If Term Term Term
  | -- | Sigma-type (homework), written `{ x : A | B }`  
    Sigma Term Level (Unbound.Bind TName Term)
  | -- | introduction form for Sigma-types `( a , b )`
    Prod Term Term
  | -- | elimination form for Sigma-types `let (x,y) = a in b`
    LetPair Term (Unbound.Bind (TName, TName) Term)
  | -- | Equality type  `a = b`
    TyEq Term Term
  | -- | Proof of equality `Refl`
    Refl
  | -- | equality type elimination  `subst a by pf`
    Subst Term Term
  | -- | witness to an equality contradiction
    Contra Term

  | -- | type constructors (fully applied)
    TCon TCName [Arg]
  | -- | term constructors (fully applied)
    DCon DCName [Arg]
  | -- | case analysis  `case a of matches`
    Case Term [Match]
    -- | displace a value found in the environment
  | Displace Term Level

  deriving (Show, Generic, Unbound.Subst Level)

-- | An argument to a function
data Arg = Arg {argEp :: Rho, unArg :: Term}
  deriving (Show, Generic, Unbound.Alpha, Unbound.Subst Term, Unbound.Subst Level)

data Epsilon =
    Mode { rho :: Rho, level :: Maybe Level }
      deriving (Show, Eq, Ord, Generic, Unbound.Alpha, Unbound.Subst Term, Unbound.Subst Level)

data Level =
    LConst Int
  | LVar   LName
  | LAdd   Level Level
  deriving (Show, Eq, Ord, Generic, Unbound.Alpha, Unbound.Subst Term)

instance Semigroup Level where
  (<>) = levelAdd
instance Monoid Level where
  mempty = LConst 0

levelAdd :: Level -> Level -> Level
levelAdd (LConst 0) l = l
levelAdd l (LConst 0) = l
levelAdd (LConst k) (LConst l) = LConst (k + l)
levelAdd l1 l2 = LAdd l1 l2

data LevelConstraint =
    Lt Level Level
  | Le Level Level
  | Eq Level Level
  deriving (Show, Eq, Ord, Generic, Unbound.Alpha, Unbound.Subst Term, Unbound.Subst Level)

-- | Rho annotates the stage of a variable
data Rho
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
      Unbound.Subst Term,
      Unbound.Subst Level
    )

-- | A 'Match' represents a case alternative
newtype Match = Match (Unbound.Bind Pattern Term)
  deriving (Show, Generic, Typeable)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term, Unbound.Subst Level)

-- | The patterns of case expressions bind all variables
-- in their respective branches.
data Pattern
  = PatCon DCName [(Pattern, Rho)]
  | PatVar TName
  deriving (Show, Eq, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term, Unbound.Subst Level)

-----------------------------------------

-- * Modules and declarations

-----------------------------------------

-- | A Module has a name, a list of imports, a list of declarations,
--   and a set of constructor names (which affect parsing).
data Module = Module
  { moduleName :: MName,
    moduleImports :: [ModuleImport],
    moduleEntries :: [Decl] ,
    moduleConstructors :: ConstructorNames
  }
  deriving (Show, Generic, Typeable)

-- | References to other modules (brings declarations and definitions into scope)
newtype ModuleImport = ModuleImport MName
  deriving (Show, Eq, Generic, Typeable)


-- | A type declaration (or type signature)
-- If this a toplevel signature the level *must* be defined
-- nondependent local signatures may omit the level
-- we could use a GADT to enforce this invariant, but then the 
-- generic programming would be more awkward
data Sig where
   Sig :: {sigName :: TName , sigRho :: Rho , sigLevel :: Maybe Level , sigType :: Type} -> Sig
  deriving (Show, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term, Unbound.Subst Level)

-- | Declare the type of a term
mkSig :: TName -> Type -> Level -> Decl
mkSig n ty l = TypeSig (Sig n Rel (Just l) ty)


-- | Declarations are the components of modules
data Decl
  = -- | Declaration for the type of a term
    TypeSig Sig
  | -- | The definition of a particular name, must
    -- already have a type declaration in scope
    Def TName Term
  | -- | A potentially (recursive) definition of
    -- a particular name, must be declared
    RecDef TName Term
    -- | Adjust the context for relevance checking
  | Demote Rho
  | -- | Declaration for a datatype including all of
    -- its data constructors. Must be toplevel
    Data TCName Telescope [ConstructorDef] Level
  | -- | An abstract view of a datatype. Does
    -- not include any information about its data
    -- constructors. Must be toplevel
    DataSig TCName Telescope Level

  deriving (Show, Generic, Typeable)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term, Unbound.Subst Level)
-- | The names of type/data constructors used in the module
data ConstructorNames = ConstructorNames
  { tconNames :: Set String,
    dconNames :: Set String
  }
  deriving (Show, Eq, Ord, Generic, Typeable)

-- | A Data constructor has a name and a telescope of arguments
data ConstructorDef = ConstructorDef SourcePos DCName Telescope
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term, Unbound.Subst Level)

-- * Telescopes

-- | A telescope is like a first class context. It is a list of 
-- assumptions, binding each variable in terms that appear
-- later in the list. 
-- For example
--     Delta = [ x:Type , y:x, y = w ]
newtype Telescope = Telescope [Decl]
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term, Unbound.Subst Level)


-- * Auxiliary functions on syntax

-- | empty set of constructor names
emptyConstructorNames :: ConstructorNames
emptyConstructorNames = ConstructorNames initialTCNames initialDCNames

-- | Default name for '_' occurring in patterns
wildcardName :: TName
wildcardName = Unbound.string2Name "_"

-- | Partial inverse of Pos
unPos :: Term -> Maybe SourcePos
unPos (Pos p _) = Just p
unPos _ = Nothing

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Term -> SourcePos
unPosFlaky t = fromMaybe (newPos "unknown location" 0 0) (unPos t)

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

-------------------------------------------------------------------
-- Prelude declarations for datatypes


-- | prelude names for built-in datatypes
sigmaName :: TCName
sigmaName = "Sigma"
prodName :: DCName
prodName = "Prod"
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

preludeDataDecls :: [Decl]
preludeDataDecls =
  [ Data sigmaName  sigmaTele      [prodConstructorDef] (LConst 1)
  , Data tyUnitName (Telescope []) [unitConstructorDef] (LConst 0)
  , Data boolName   (Telescope []) [falseConstructorDef, trueConstructorDef] (LConst 0)
  ]  where
        -- boolean
        trueConstructorDef = ConstructorDef internalPos trueName (Telescope [])
        falseConstructorDef = ConstructorDef internalPos falseName (Telescope [])

        -- unit
        unitConstructorDef = ConstructorDef internalPos litUnitName (Telescope [])

        -- Sigma-type
        -- Sigma (A :: Type) (B :: Pi x:A. Type)
        -- prod :: (x :: A) (y :: B x) -> Sigma A B
        sigmaTele = Telescope [TypeSig sigA, TypeSig sigB]
        prodConstructorDef = ConstructorDef internalPos prodName (Telescope [TypeSig sigX, TypeSig sigY])
        sigA = Sig aName Rel (Just (LConst 0)) Type
        sigB = Sig bName Rel Nothing (Pi (Mode Rel Nothing) (Var aName) (Unbound.bind xName Type))
        sigX = Sig xName Rel (Just (LConst 0)) (Var aName)
        sigY = Sig yName Rel Nothing (App (Var bName) (Arg Rel (Var xName)))

        aName = Unbound.string2Name "a"
        bName = Unbound.string2Name "b"

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
--    -- Destruct a binding, generating fresh names for the bound variables
--    unbind :: (Alpha p, Alpha t, Fresh m) => Bind p t -> m (p, t)

-- For Terms, we'd like Alpha equivalence to ignore 
-- source positions and type annotations.
-- We can add these special cases to the definition of `aeq'` 
-- and then defer all other cases to the generic version of 
-- the function (Unbound.gaeq).

instance Unbound.Alpha Term where
  aeq' ctx (Ann a _) b = Unbound.aeq' ctx a b
  aeq' ctx a (Ann b _) = Unbound.aeq' ctx a b
  aeq' ctx (Pos _ a) b = Unbound.aeq' ctx a b
  aeq' ctx a (Pos _ b) = Unbound.aeq' ctx a b
  aeq' ctx a b = (Unbound.gaeq ctx `on` from) a b

-- For example, all occurrences of annotations and source positions
-- are ignored by this definition.

-- >>> Unbound.aeq (Pos internalPos (Ann TyBool Type)) TyBool
-- True

-- At the same time, the generic operation equates terms that differ only 
-- in the names of bound variables.

-- 'x'
xName :: TName
xName = Unbound.string2Name "x"

-- 'y'
yName :: TName
yName = Unbound.string2Name "y"

-- '\x -> x`
idx :: Term
idx = Lam Rel (Unbound.bind xName (Var xName))

-- '\y -> y`
idy :: Term
idy = Lam Rel (Unbound.bind yName (Var yName))

-- >>> Unbound.aeq idx idy
-- True


---------------

-- * Substitution

-- The Subst class derives capture-avoiding substitution
-- It has two parameters because the sort of thing we are substituting
-- for may not be the same as what we are substituting into.

-- class Subst b a where
--    subst  :: Name b -> b -> a -> a       -- single substitution

instance Unbound.Subst Term Term where
  isvar (Var x) = Just (Unbound.SubstName x)
  isvar _ = Nothing

instance Unbound.Subst Level Level where
  isvar (LVar x) = Just (Unbound.SubstName x)
  isvar _ = Nothing


-- '(y : x) -> y'
pi1 :: Term
pi1 = Pi (Mode Rel (Just (LConst 0))) (Var xName) (Unbound.bind yName (Var yName))

-- '(y : Bool) -> y'
pi2 :: Term
pi2 = Pi (Mode Rel (Just (LConst 0))) TyBool (Unbound.bind yName (Var yName))

-- >>> Unbound.aeq (Unbound.subst xName TyBool pi1) pi2
-- True
-- 



-----------------

-- * Source Positions

-- SourcePositions do not have an instance of the Generic class available
-- so we cannot automatically define their Alpha and Subst instances. Instead
-- we do so by hand here. 
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
instance Unbound.Subst b SourcePos where
  subst _ _ = id; substs _ = id; substBvs _ _ = id


-- Internally generated source positions
internalPos :: SourcePos
internalPos = initialPos "internal"

getFreelyDisplaceable :: Decl -> Maybe TName
getFreelyDisplaceable (Def na te) 
  | isFreelyDisplaceable te = Just na 
getFreelyDisplaceable (RecDef na te) 
  | isFreelyDisplaceable te = Just na
getFreelyDisplaceable _ = Nothing

isFreelyDisplaceable :: Term -> Bool
isFreelyDisplaceable = go where
  goArg :: Arg -> Bool
  goArg (Arg r a) = go a

  go :: Term -> Bool
  go Type = True
  go (Var na) = True
  go (Lam rho bnd) = let (_,a) = Unbound.unsafeUnbind bnd in go a
  go (App te arg) = go te && goArg arg
  go (Pi (Mode _ Nothing) te bnd) = go te && let (_,a) = Unbound.unsafeUnbind bnd in go a
  go (Pi (Mode _ (Just k)) _ _) = False
  go (Ann te te') = go te && go te'
  go (Pos sp te) = go te
  go TrustMe = True
  go PrintMe = True
  go (Let te bnd) = go te && let (_,a) = Unbound.unsafeUnbind bnd in go a
  go TyUnit = True
  go LitUnit = True
  go TyBool = True
  go (LitBool b) = True
  go (If te te' te2) = go te && go te' && go te2
  go (Sigma te le bi) = error "BUG"
  go (Prod te te') = error "BUG"
  go (LetPair te bi) = error "BUG"
  go (TyEq te te') = go te && go te'
  go Refl = True
  go (Subst te te') = go te && go te'
  go (Contra te) = go te
  go (TCon s args) = all goArg args
  go (DCon s args) = all goArg args
  go (Case te mas) = go te && all goMatch mas
  go (Displace te le) = False

  goMatch :: Match -> Bool
  goMatch (Match bi) = go a 
    where 
      (_,a) = Unbound.unsafeUnbind bi

