
-- | The abstract syntax of the simple dependently typed language
-- See the comment at the top of 'Parser' for the concrete syntax of this language
module Syntax where

import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Typeable (Typeable)
import GHC.Generics (Generic,from)
import GHC.Base (MonadPlus)
import Text.ParserCombinators.Parsec.Pos (SourcePos, initialPos, newPos)
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound

import Data.Function (on)

-----------------------------------------

-- * Names

-----------------------------------------

-- | For variable names, we use the `Unbound` library to
-- automatically generate free variable, substitution,
-- and alpha-equality function. The abstract type `Name` from 
-- this library is indexed by the AST type that this variable 
-- is a name for. 

type TName = Unbound.Name Term

-----------------------------------------

-- * Core language of pi-forall (Combined syntax for types and terms)

-----------------------------------------

-- | Because types and terms use the same AST, we define the following
-- type synonym so that we can hint whether a piece of syntax is being used
-- as a type or as a term.
type Type = Term

-- | basic language
data Term
  = -- | type of types, concretely `Type`
    TyType
  | -- | variable `x`
    Var TName
  | -- | abstraction  `\x. a`
    Lam {- SOLN EP -} Epsilon{- STUBWITH -} (Unbound.Bind TName Term)
  | -- | application `a b`
    App Term {- SOLN EP -} Arg{- STUBWITH Term -}
  | -- | function type   `(x : A) -> B`
    TyPi {- SOLN EP -} Epsilon{- STUBWITH -} Type (Unbound.Bind TName Type)
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
    TySigma Term (Unbound.Bind TName Term)
  | -- | introduction form for Sigma-types `( a , b )`
    Prod Term Term
  | -- | elimination form for Sigma-types `let (x,y) = a in b`
    LetPair Term (Unbound.Bind (TName, TName) Term) 
{- SOLN EQUAL -}
  | -- | Equality type  `a = b`
    TyEq Term Term
  | -- | Proof of equality `Refl`
    Refl 
  | -- | equality type elimination  `subst a by pf`
    Subst Term Term 
  | -- | witness to an equality contradiction
    Contra Term
    {- STUBWITH -}
{- SOLN DATA -}
  | -- | type constructors (fully applied)
    TyCon TyConName [Arg]
  | -- | term constructors (fully applied)
    DataCon DataConName [Arg] 
  | -- | case analysis  `case a of matches`
    Case Term [Match]
  {- STUBWITH -}
  deriving (Show, Generic)

{- SOLN EP -}
-- | An argument to a function
data Arg = Arg {argEp :: Epsilon, unArg :: Term}
  deriving (Show, Generic, Unbound.Alpha, Unbound.Subst Term)

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
  = PatCon DataConName [(Pattern, Epsilon)]
  | PatVar TName
  deriving (Show, Eq, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)
{- STUBWITH -}

-----------------------------------------

-- * Modules and declarations

-----------------------------------------

-- | module names
type ModuleName = String

-- | A Module has a name, a list of imports, a list of declarations,
--   and a set of constructor names (which affect parsing).
data Module = Module
  { moduleName :: ModuleName,
    moduleImports :: [ModuleImport],
    moduleEntries :: [Entry] {- SOLN DATA -} ,
    moduleConstructors :: ConstructorNames {- STUBWITH -}
  }
  deriving (Show, Generic, Typeable, Unbound.Alpha)

-- | References to other modules (brings declarations and definitions into scope)
newtype ModuleImport = ModuleImport ModuleName
  deriving (Show, Eq, Generic, Typeable)
  deriving anyclass (Unbound.Alpha)

-- | A type declaration 
data TypeDecl = TypeDecl {declName :: TName {- SOLN EP -} , declEp :: Epsilon {- STUBWITH -} , declType :: Type}
  deriving (Show, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)

-- | Declare the type of a term
mkDecl :: TName -> Type -> Entry
mkDecl n ty = Decl (TypeDecl n {- SOLN EP -} Rel {- STUBWITH -} ty)

-- | Entries are the components of modules
data Entry
  = -- | Declaration for the type of a term  'x : A'
    Decl TypeDecl
  | -- | The definition of a particular name, must  'x = a'
    -- already have a type declaration in scope
    Def TName Term
{- SOLN EP -}
    -- | Adjust the context for relevance checking
  | Demote Epsilon {- STUBWITH -} 
{- SOLN DATA -}
  | -- | Datatype definition (must be at the module level)
    Data TyConName Telescope [ConstructorDef]
  {- STUBWITH -}
  deriving (Show, Generic, Typeable)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

{- SOLN DATA -}
-----------------------------------------

-- * Datatypes

-----------------------------------------
-- | type constructor names
type TyConName = String

-- | data constructor names
type DataConName = String

-- | The names of type/data constructors used in the module
data ConstructorNames = ConstructorNames
  { tconNames :: Set String,
    dconNames :: Set String
  }
  deriving (Show, Eq, Ord, Generic, Typeable)

-- | A Data constructor has a name and a telescope of arguments
data ConstructorDef = ConstructorDef SourcePos DataConName Telescope
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

-- ** Telescopes

-- | A telescope is like a first class context. It is a list of 
-- assumptions, binding each variable in terms that appear
-- later in the list. 
-- For example
--     Delta = [ x:Type , y:x, y = w ]
newtype Telescope = Telescope [Entry]
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

-----------------------------------------
-- Definitions related to datatypes

-- | Is this the syntax of a literal (natural) number
isNumeral :: Term -> Maybe Int
isNumeral (Pos _ t) = isNumeral t
isNumeral (DataCon c []) | c == "Zero" = Just 0
isNumeral (DataCon c [Arg _ t]) | c == "Succ" =
  do n <- isNumeral t; return (n + 1)
isNumeral _ = Nothing

-- | Is this pattern a variable
isPatVar :: Pattern -> Bool
isPatVar (PatVar _) = True
isPatVar _ = False

-- | built-in set of constructor names
initialConstructorNames :: ConstructorNames
initialConstructorNames = ConstructorNames initialTCNames initialDCNames

-- | prelude names for built-in datatypes
sigmaName :: TyConName
sigmaName = "Sigma"
prodName :: DataConName
prodName = "Prod"
boolName :: TyConName
boolName = "Bool"
trueName :: DataConName
trueName = "True"
falseName :: DataConName
falseName = "False"
tyUnitName :: TyConName
tyUnitName = "Unit"
litUnitName :: DataConName
litUnitName = "()"

initialTCNames :: Set TyConName
initialTCNames = Set.fromList [sigmaName, boolName, tyUnitName]
initialDCNames :: Set DataConName
initialDCNames = Set.fromList [prodName, trueName, falseName, litUnitName]


preludeDataDecls :: [Entry]
preludeDataDecls = 
  [ Data sigmaName  sigmaTele      [prodConstructorDef]
  , Data tyUnitName (Telescope []) [unitConstructorDef]
  , Data boolName   (Telescope []) [falseConstructorDef, trueConstructorDef]
  ]  where
        -- boolean
        trueConstructorDef = ConstructorDef internalPos trueName (Telescope [])
        falseConstructorDef = ConstructorDef internalPos falseName (Telescope [])

        -- unit
        unitConstructorDef = ConstructorDef internalPos litUnitName (Telescope []) 

        -- Sigma-type
        sigmaTele = Telescope [declA, declB]
        prodConstructorDef = ConstructorDef internalPos prodName (Telescope [declX, declY])
        declA = mkDecl aName TyType
        declB = mkDecl bName (TyPi Rel (Var aName) (Unbound.bind xName TyType))
        declX = mkDecl xName (Var aName)
        declY = mkDecl yName (App (Var bName) (Arg Rel (Var xName)))
        aName = Unbound.string2Name "a"
        bName = Unbound.string2Name "b"

        internalPos :: SourcePos
        internalPos = initialPos "prelude"
{- STUBWITH -}


-----------------------------------------
-- * Auxiliary functions on syntax
-----------------------------------------


-- | Remove source positions and type annotations from the top level of a term
strip :: Term -> Term
strip (Pos _ tm) = strip tm
strip (Ann tm _) = strip tm
strip tm = tm

-- | Partial inverse of Pos
unPos :: Term -> Maybe SourcePos
unPos (Pos p _) = Just p
unPos _ = Nothing

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Term -> SourcePos
unPosFlaky t = fromMaybe (newPos "unknown location" 0 0) (unPos t)



-----------------------------------------
-- * Unbound library
-----------------------------------------

-- We use the unbound-generics library to mark the binding occurrences of
-- variables in the syntax. That allows us to automatically derive
-- functions for alpha-equivalence, free variables and substitution
-- using generic programming. 

-- The definitions below specialize the generic operations from the libary
-- to some of the common uses that we need in pi-forall

-- | Determine when two terms are alpha-equivalent (see below)
aeq :: Term -> Term -> Bool
aeq = Unbound.aeq

-- | Calculate the free variables of a term 
fv :: Term -> [Unbound.Name Term]
fv = Unbound.toListOf Unbound.fv

-- | `subst x b a` means to replace `x` with `b` in `a`
-- i.e.  a [ b / x ]
subst :: TName -> Term -> Term -> Term
subst = Unbound.subst

-- | in a binder `x.a` replace `x` with `b` 
instantiate :: Unbound.Bind TName Term -> Term -> Term
instantiate bnd a = Unbound.instantiate bnd [a]

-- | in a binder `x.a` replace `x` with a fresh name
unbind :: (Unbound.Fresh m) => Unbound.Bind TName Term -> m (TName, Term)
unbind = Unbound.unbind

-- | in binders `x.a1` and `x.a2` replace `x` with a fresh name in both terms
unbind2 :: (Unbound.Fresh m) => Unbound.Bind TName Term -> Unbound.Bind TName Term -> m (TName, Term, Term)
unbind2 b1 b2 = do 
  o <- Unbound.unbind2 b1 b2
  case o of 
      Just (x,t,_,u) -> return (x,t,u)
      Nothing -> error "impossible" 
------------------

-- * `Alpha` class instances

-- The Unbound library's `Alpha` class enables the `aeq`, `fv`,
-- `instantiate` and `unbind` functions, and also allows some 
-- specialization of their generic behavior.

-- For `Term`, we'd like Alpha equivalence to ignore 
-- source positions and type annotations. So we make sure to 
-- remove them before calling the generic operation.

instance Unbound.Alpha Term where
  aeq' :: Unbound.AlphaCtx -> Term -> Term -> Bool
  aeq' ctx a b = (Unbound.gaeq ctx `on` from) (strip a) (strip b)


-- For example, all occurrences of annotations and source positions
-- are ignored by this definition.

-- '(Bool : Type)' is alpha-equivalent to 'Bool'
-- >>> aeq (Ann TyBool TyType) TyBool

-- '(Bool, Bool:Type)' is alpha-equivalent to (Bool, Bool)
-- >>> aeq (Prod TyBool (Ann TyBool TyType)) (Prod TyBool TyBool)


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
idx = Lam {- SOLN EP -} Rel {- STUBWITH -}(Unbound.bind xName (Var xName))

-- '\y -> y`
idy :: Term
idy = Lam {- SOLN EP -} Rel {- STUBWITH -}(Unbound.bind yName (Var yName))

-- >>> aeq idx idy
-- True


---------------

-- * Substitution

-- The Subst class derives capture-avoiding substitution.
-- It has two parameters because the type of thing we are substituting
-- for may not be the same as what we are substituting into.

-- The `isvar` function identifies the variables in the term that 
-- should be substituted for.
instance Unbound.Subst Term Term where
  isvar (Var x) = Just (Unbound.SubstName x)
  isvar _ = Nothing


-- '(y : x) -> y'
pi1 :: Term 
pi1 = TyPi {- SOLN EP -} Rel {- STUBWITH -}(Var xName) (Unbound.bind yName (Var yName))

-- '(y : Bool) -> y'
pi2 :: Term 
pi2 = TyPi {- SOLN EP -} Rel {- STUBWITH -}TyBool (Unbound.bind yName (Var yName))

-- >>> Unbound.aeq (Unbound.subst xName TyBool pi1) pi2

-----------------

-- * Source Positions

-- SourcePositions do not have an instance of the Generic class available
-- so we cannot automatically define their `Alpha` and `Subst` instances. 
-- Instead we provide a trivial implementation here. 
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
    subst _ _ = id
    substs _ = id
    substBvs _ _ = id



{- SOLN DATA -}

-- * Constructor Names

-- ConstructorNames are sets, so they also do not have an instance of the 
-- Generic class available so we cannot automatically define their 
-- Alpha and Subst instances.
instance Unbound.Alpha ConstructorNames where
  aeq' _ a1 a2 = a1 == a2
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
{- STUBWITH -}
