# Putting it all together in a Haskell implementation

Last time, we defined a bidirectional type system for a small core 
language. Today we'll start talking about what the implementation of this 
language might look like in Haskell. 

First, an overview of the main files of the implementation.

     Syntax.hs      - specification of the abstract syntax of the language
	  Parser.hs      - turn strings into AST
     PrettyPrint.hs - displays AST in a (somewhat) readable form
	  Main.hs        - top-level routines (repl)
	  
     Environment.hs - defines the type checking monad		  
	  TypeCheck.hs   - implementation of the bidirectional type checker
	  	  
### Variable binding using the unbound library [Syntax.hs]

One difficulty with implementing the lambda calculus is the treatment of
variable binding. Lambdas and Pis *bind* variables in the body. In the
implementation of our type checker, we'll need to be able to determine whether
two terms are *alpha-equivalent*, calculate the *free variables* of a term,
and perform *capture-avoiding substitution.* When we work with a lambda
expression, we will want to be sure that the binding variable is *fresh*, that
is, distinct from all other variables in the program.

In today's code, we'll use the unbound library to get all of these operations
for free.  This library defines a type for variable names, called `Name`. 

    -- | term variable names, use unbound library to 
    -- automatically generate fv, subst, alpha-eq
    type TName = Name Term

This type is indexed by the type of AST that this is a name for. That way 
unbound can make sure that substitutions make sense. 
    
	 class Subst b a where
        subst  :: Name b -> b -> a -> a       
	 
The `subst` function in this class ensures that when we see `subst x a b`,
which means "substitute a for x in b" (also written b{a/x} above) that `a` is
the right sort of thing to stick in for `x`.  The Unbound library can
automatically generate instances of the `Subst` class. Furthermore, although
it seems like we only need to substitute within terms, we'll actually need to
have substitution available at many types.

With names, we can define the syntax of that corresponds to our language
above, using the following datatype.

    data Term = 
         Type                               -- ^ universe 
       | Var TName                          -- ^ variables      
       | Lam (Bind TName, Embed Annot) Term)             
                                            -- ^ abstraction    
       | App Term Term                      -- ^ application    
       | Pi (Bind (TName, Embed Term) Term) -- ^ function type

As you can see, variables are represented by names.  The `Bind` type
constructor declares the scope of the bound variables. Both `Lam` and `Pi`
bind a single variable in a `Term`.  The `Annot` type is an optional
type annotation:

     newtype Annot = Annot (Maybe Type) deriving Show 

and, because the syntax is all shared, a `Type` is just another name for a
`Term`.  We'll use this name just for documentation.
	  
	  type Type = Term

The fact that this annotation is optional means that we'll be able to use a
single datatype for both the versions of the language (the one where lambdas
are annotated and the one where they aren't). We'll start with an expression
that has no annotations on lambdas, and elaborate it to one that does. 

The bottom of the Syntax file contains instructions for unbound. The line 

    derive [''Term]
	 
instructs unbound to derive a representation of the structure of the `Term`
AST. This is all that is necessary to create an instance of the `Alpha` type
class for this type.
	 
    instance Alpha Term
	 
Among other things, the Alpha class enables functions for alpha equivalence
and free variable calculation. Because unbound creates these instances for us,
we don't have to worry about defining them.

    aeq :: Alpha a => a -> a -> Bool
    fv  :: Alpha a => a -> [Name a]	 
	 
Creating an instance of the `Subst` type class requires telling unbound where the variables are (and no more):

    instance Subst Term Term where
      isvar (Var x) = Just (SubstName x)
      isvar _ = Nothing	 

We also need to be able to substitute terms through annotations, but
annotations don't contain free variables directly, they only have them within
the terms inside them.
	 
	 instance Subst Term Annot
	 
For more information about unbound, see
[The Unbound Tutorial](https://code.google.com/p/replib/source/browse/trunk/Unbound/tutorial/Tutorial.lhs)
and the
[unbound hackage page](http://hackage.haskell.org/package/unbound-0.4.3.1).
	 
### A TypeChecking monad [Environment.hs]

Recall that our plan is to write two mutually recursive functions for type
checking of the following types:

    inferType :: Term -> Ctx -> Maybe (Term,Type)
	 
	 checkType :: Term -> Type -> Ctx -> Maybe Term
	 
The inference function should take a term and a context and if it type checks,
produce its type and its elaboration (where all annotations have been filled
in). The checking function should take a term and a context and a type, and if
that term has that type produce an elaborated version (where all of the
annotations have been filled in.)

Well actually, we'll do something a bit different. We'll define a *type
checking monad*, called `TcMonad` that will handle the plumbing for the typing
context, and allow us to return more information than `Nothing` when a program
doesn't type check.

    inferType :: Term -> TcMonad (Term,Type)
	 
	 checkType :: Term -> Type -> TcMonad Term

Those of you who have worked with Haskell before may be familiar with the
[MonadReader](https://hackage.haskell.org/package/mtl-2.1.2/docs/Control-Monad-Reader.html),
and the
[MonadError](https://hackage.haskell.org/package/mtl-2.1.2/docs/Control-Monad-Error.html),
which our type checking monad will be instances of.

    lookupTy :: TName -> TcMonad Term
	 extendCtx :: Decl -> TcMonad Term -> TcMonad Term
     
	  
	 err  :: (Disp a) => a -> TcMonad b
	 warn :: (Disp a) => a -> TcMonad b

We'll also need this monad to be a freshness monad, to support working with
binding structure, and throw in MonadIO for good measure.

### Implementing the TypeChecking Algorithm [Typecheck.hs]

Now that we have the type checking monad available, we can start our
implementation. For flexibility `inferType` and `checkType` will *both* be
implemented by the same function:

    inferType :: Term -> TcMonad (Term,Type)
	 inferType t = tcTerm t Nothing
	 
	 checkType :: Term -> Type -> TcMonad (Term, Type)
	 checkType tm ty = tcTerm tm (Just ty)


The `tcTerm` function checks a term, producing an elaborated term where all of
the type annotations have been filled in, and its type.  The second argument
is 'Nothing' in inference mode and an expected type in checking mode.

    tcTerm :: Term -> Maybe Type -> TcMonad (Term,Type)

The general structure of this function starts with a pattern match 
for the various syntactic forms in inference mode:

    tcTerm (Var x) Nothing = ... 
	 
	 tcTerm Type Nothing = ...
  
    tcTerm (Pi bnd) Nothing = ...
	 
	 tcTerm (Lam bnd) Nothing = ... -- must have annotation
	 
	 tcTerm (App t1 t2) Nothing = ...
	 
Mixed in here, we also have a pattern for lambda expressions in checking mode:	 
	 
    tcTerm (Lam bnd) (Just (Pi bnd2)) = ... 
	 
	 tcTerm (Lam _) (Just nf) =  -- checking mode wrong type
       err [DS "Lambda expression has a function type, not", DD nf]

There are also several cases for practical reasons (annotations, source code
positions, parentheses, TRUSTME) and a few cases for homework.
		 
Finally, the last case covers all other forms of checking mode, by 
calling inference mode and making sure that the inferred type is 
equal to the checked type.
		 
	 tcTerm tm (Just ty) = do
      (atm, ty') <- inferType tm 
		unless (aeq ty' ty) $ err [DS "Types don't match", DD ty, DS "and", DD ty']
      return (atm, ty)	 

The function `aeq` merely ensures that the two types are
alpha-equivalent. If they are, then it returns `()` to the monad, otherwise it
throws an error.

### Example 

The file [Lec1.pi](version1/test/Lec1.pi) contains the examples that we worked
out in lecture last time. Let's try to type check it, after filling in 
the missing code in `TypeCheck.hs`.

### Exercise (Type Theory & Haskell) - Add Booleans and Sigma types

Some fairly standard typing rules for booleans assert that Bool is a valid type:

    ---------------- Bool
    G |- Bool : Type

    ---------------- true
    G |- true : Bool
	
	 ---------------- false
 	 G |- false : Bool
	 	 
	 G |- a : Bool 
	 G |- b : A
	 G |- c : A
	 ---------------------------- if
	 G |- if a then b else c : A

Likewise, we can also extend the language with Sigma types. 

    G |- A : Type     G, x:A |- B : Type
    ------------------------------------- sigma
    G |- { x : A | B } : Type

A sigma type is a product where the type of the second component of the
product can depend on the first component.

    G |- a : A      G |- b : B { a / x }
	 ------------------------------------ pair
	 G |- (a,b) : { x : A | B }
	 
We destruct sigmas using pattern matching. A simple rule for pattern matching
introduces variables into the context when pattern matching the sigma
type. These variables are not allowed to appear free in the result type of the
pattern match.

    G |- a : { x : A | B }
	 G, x:A, y:B |- b : C
	 G |- C : Type
    ------------------------------ weak-pcase
    G |- pcase a of (x,y) -> b : C

This part of the homework has two parts:

1. First: rewrite the rules above in bidirectional style. Which rules should
  be inference rules? Which ones should be checking rules? If you are familiar
  with other systems, how do these rules compare?
 
2. In Haskell, later: The code in `version1/` includes abstract and concrete
  syntax for booleans and sigma types. The pi-forall file
  `version1/test/Hw1.pi` contains examples of using these new forms. However,
  to get this file to compile, you'll need to fill in the missing cases in
  `version1/src/TypeCheck.hs`.


