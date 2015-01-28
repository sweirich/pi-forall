# Notes for Compose conference

These notes are an abridged form of the OPLSS notes 1-4, and were used for a
technical keynote at the Compose conference, Friday January 30, 2015.  They
are for the *second* part of the talk: the first part included an extended
example of dependently-typed programming in pi-forall.

Because of the time limitation, these notes do not cover the implementation of
datatypes and erased arguments in pi-forall.

## The pi-forall implementation 


First, an overview of the main files of the implementation.

     Syntax.hs      - specification of the abstract syntax of the language
     Parser.hs      - turn strings into AST
     PrettyPrint.hs - displays AST in a (somewhat) readable form
     Main.hs        - top-level routines (repl)
	  
     Environment.hs - defines the type checking monad		  
     TypeCheck.hs   - implementation of the bidirectional type checker
     Equal.hs       - decides when two terms are equal, converts terms to whnf

### The (abridged) syntax of pi-forall

We'll focus our discussion of the pi-forall implementation on the following
five forms:

     a,A ::= x       - variables 
         \x. a       - lambda expressions (anonymous functions)
         a b         - function applications
         (x:A) -> B  - dependent function type, aka Pi
         Type        - the 'type' of types

Note that we are using the *same* syntax for expressions and types. For
clarity, I'll used lowercase letters `a` for expressions and uppercase letters
for their types `A`

Note that lambda and pi above are *binding forms*. They bind the variable 
`x` in `a` and `B` respectively
	  	  
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

With names, we can define the syntax that corresponds to our language
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

For more information about unbound, see
[The Unbound Tutorial](https://code.google.com/p/replib/source/browse/trunk/Unbound/tutorial/Tutorial.lhs)
and the
[unbound hackage page](http://hackage.haskell.org/package/unbound-0.4.3.1).

### Bidirectional Typechecking in pi-forall

The pi-forall typechecker is defined by a *bidirectional* type system. This
means that it is defined by two mutually recursive functions:

    inferType :: Term -> Ctx -> Maybe (Term,Type)
	 
    checkType :: Term -> Type -> Ctx -> Maybe Term

The inference function should take a term and a context (which records the
types of variables) and if it type checks, produce its type and its
elaboration (where all annotations have been filled in). The checking function
should take a term and a context and a type, and if that term has that type
produce an elaborated version (where all of the annotations have been filled
in.)

The nice thing about a bidirectional system is that it reduces the number of
annotations that are necessary in programs that we want to write. For example, 
if we have a top-level type annotation, then we don't need to also annotate the 
argument types of functions. t

id : (a:Type) -> a -> a
id = \a x. x

This works because we will be able to *check* the type of the definition, so
we can pull out the argument type from the expected type.  Checking mode is
even more important as we add more terms to the language (such as datatypes).

### Typechecking monad

Well actually, we'll do something a bit different from the two functions
listed above. We'll define a *type checking monad*, called `TcMonad` that will
handle the plumbing for the typing context, and allow us to return more
information than `Nothing` when a program doesn't type check.

    inferType :: Term -> TcMonad (Term,Type)
	 
    checkType :: Term -> Type -> TcMonad Term

This typechecking monad:
  - keeps track of the types of free variables
  - records the definitions of variables (like a delayed substitution)
  - allows us to generate compiler errors and warnings 
  - generates "fresh" variables for unbound


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
is `Nothing` in inference mode and an expected type in checking mode.

    tcTerm :: Term -> Maybe Type -> TcMonad (Term,Type)

The general structure of this function starts with a pattern match 
for the various syntactic forms in inference mode:

    tcTerm (Var x) Nothing = ... 
	 
    tcTerm Type Nothing = ...
  
    tcTerm (Pi bnd) Nothing = ...
	 
    tcTerm (Lam bnd) Nothing = ... -- must have annotation on variables
	 
    tcTerm (App t1 t2) Nothing = ...
	 
Mixed in here, we also have a pattern for lambda expressions in checking mode:	 
	 
    tcTerm (Lam bnd) (Just (Pi bnd2)) = ... 
	 
    tcTerm (Lam _) (Just nf) =  -- checking mode with the wrong type
       err [DS "Lambda expression has a function type, not", DD nf]

There are also several cases for practical reasons (annotations, source code
positions, parentheses, TRUSTME) and a few cases for homework.
		 
Finally, the last case covers all other forms of checking mode, by 
calling inference mode and making sure that the inferred type is 
equal to the checked type.
		 
    tcTerm tm (Just ty) = do
     (atm, ty') <- inferType tm 
	  equate ty' ty
     return (atm, ty)	 

