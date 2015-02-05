# Pi-Forall: How to use and implement a dependently-typed language

These notes are an abridged form of the OPLSS notes, and were used for a
technical keynote at the Compose conference, Friday January 30, 2015. 

The Compose organizers have posted a
[video](https://www.youtube.com/watch?v=6klfKLBnz9k) of the entire talk. The
slides for the [first part of the talk](compose15.pdf) are available here. That
first part considered an extended example of the use of dependent types:

 * [Lambda0.pi](master/test/Lambda0.pi) - The starting point. A simple, environment 
 based interpreter for the lambda calculus with function and natural numbers. This
 interpreter could fail in two ways: the lambda term to interpret 
 could have unbound variables or it could have a dynamic type error. 
 * [Lambda1.pi](master/test/Lambda1.pi) - Using the indexed types `Fin` and `Vec`, 
 this version shows how to eliminate the first sort of failure. The expression
 datatype now tracks the number of free variables in the term and the interpreter
 must be called with an environment that has values for that many free variables. 
 * [Lambda2.pi](master/test/Lambda2.pi) - Not covered in the talk, but the 
 end of the story. How to also get rid of the run-time type errors by only 
 representing well-typed expressions.

The bulk of these notes are for the *second* part of the talk---the
implementation of a type checker for a dependently-typed language.  Because of
the time limitation, these notes do not cover the implementation of datatypes
or erased arguments in pi-forall. Therefore they are based on `version2` of
the the [pi-forall implementation](version2/src/), which does not include
these features.

We break the discussion into three main parts:

  * How do we represent the syntax of pi-forall (including binding structure)?
  * What is the general structure of the typechecker?
  * How do we decide when two different pi-forall terms are equal?

## The pi-forall implementation 

But, before we do that, we start with an overview of the main files of the
implementation.

     Syntax.hs      - specification of the abstract syntax of the language
     Parser.hs      - turn strings into AST
     PrettyPrint.hs - displays AST in a (somewhat) readable form
     Main.hs        - top-level routines 
	  
     Environment.hs - defines the type checking monad		  
     TypeCheck.hs   - implementation of the bidirectional type checker
     Equal.hs       - decides when two terms are equal, converts terms to whnf

## The (abridged) syntax of pi-forall

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
	  	  
### Variable binding using the unbound library - [Syntax.hs](version2/src/Syntax.hs)

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

The fact that this annotation is optional means that we'll be able to omit
type annotations in certain parts of the language that programmers type in
(such as the types of variables in lambdas). The type checker will take an
expression that has no annotations on lambdas and elaborate it to one that
does.

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

## Bidirectional Typechecking in pi-forall - [Typechecker.hs](version2/src/TypeCheck.hs)

The pi-forall typechecker is defined by a *bidirectional* type system. This
means that it is defined by two mutually recursive functions, which we 
can think of as having the following types:

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
argument types of functions. 

id : (a:Type) -> a -> a
id = \a x. x

This works because we will be able to *check* the type of the definition;
we can pull out the argument type from the expected type.  Checking mode is
even more important as we add more forms to the language (such as datatypes).

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
  - allows us to generate errors and warnings 
  - generates "fresh" variables for unbound


### Implementing the TypeChecking Algorithm 

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
positions, parentheses, TRUSTME).
		 
Finally, the last case covers all other forms of checking mode by 
calling inference mode and making sure that the inferred type is 
equal to the checked type.
		 
    tcTerm tm (Just ty) = do
     (atm, ty') <- inferType tm 
	  equate ty' ty
     return (atm, ty)	 

## Definitional Equality in Dependently-Typed Languages - [Equal.hs](version2/src/Equal.hs)

Just what is the equate function? 

### Motivating Example - Type level reduction

In full dependently-typed languages (and in full pi-forall) we can see the
need for definitional equality. We want to equate types that are not just
*syntactically* equal, so that more expressions type check. 

In the full language, we might have a type of length indexed
vectors, where vectors containing values of type `A` with length `n` can be
given the type `Vec A n`.  In this language we may have a safe head operation,
that allows us to access the first element of the vector, as long as it is
nonzero.

    head : (A : Nat) -> (n : Nat) -> Vec A (succ n) -> Vec A n
    head = ...
	 
However, to call this function, we need to be able to show that the length of
the argument vector is equal to `succ n` for some n.  This is ok if we know
the length of the vector outright

    v1 : Vec Bool (succ 0)
	 v1 = VCons True VNil
	 
So the application `head Bool 0 v1` will type check. (Note that pi-forall
cannot infer the types `A` and `n`.)
	 
However, if we construct the vector, its length may not be a literal natural number:
	 
    append : (n : Nat) -> (m : Nat) -> Vec A m -> Vec A n -> Vec A (plus m n)
	 append = ...

In that case, to get `head Bool 1 (append v1 v1)` to type check, we need to
show that the type `Vec Bool (succ 1)` is equal to the type `Vec Bool (plus 1
1)`.  If our definition of type equality is *alpha-equivalence*, then this
equality will not hold. We need to enrich our definition of equality so that
it equates more terms.

### Defining definitional equality

The main idea is that we will: 

 - establish a new judgement to define when types are equal

        G |- A = B

 - Define a type equality *algorithm* (equate) that computes when types are
   equal.
	 

What is a good definition of equality?  We can start with a very simple one:
alpha-equivalence. But we can do better:

We'd like to make sure that our relation *contains beta-equivalence*:

    -------------------------- beta
    G |- (\x.a)b = a {b / x}
	 
(with similar rules for if/sigmas if we have them.)

Is an *equivalence relation*:

    ----------  refl
    G |- A = A
	 
	 G |- A = B
	 -----------  sym
	 G |- B = A
	 
	 G |- A = B    G |- B = C
	 ------------------------- trans
	 G |- A = C

and a *congruence relation* (i.e. if subterms are equal, then larger terms are equal):

    G |- A1 = A2       G,x:A1 |- B1 = B2
	 ------------------------------------ pi
	 G |- (x:A1) -> B1 = (x:A2) -> B2

    G |- a1 = a2    G |- b1 b2 
	 -------------------------- app
	 G |- a1 b1 = a2 b2

    [similar rules for other terms]


### Using definitional equality in the algorithm

We would like to consider our type system as having the following rule:

    G |- a : A    G |- A = B
	 ------------------------ conv
	 G |- a : B

But that rule is not syntax directed. Where do we need to add equality
preconditions in our bidirectional system?  It turns out that there are only a
few places.

- Where we switch from checking mode to inference mode in the algorithm. Here 
  we need to ensure that the type that we infer is the same as the type that 
  is passed to the checker  (cf. last case of tcTerm above).

- In the rule for application, when we infer the type of the function we need
to make sure that the function actually has a function type. But we don't really 
know what the domain and co-domain of the function should be. We'd like our 
algorithm for type equality to be able to figure this out for us.
  
     tcTerm (App t1 t2) Nothing = do  
        (at1, ty1)    <- inferType t1  
        (x, tyA, tyB) <- ensurePi ty1        -- make sure ty1 is a function type
        (at2, ty2)    <- checkType t2 tyA
        let result = (App at1 at2, subst x at2 tyB)
        return result

Above, the function

    ensurePi :: Type -> TcMonad (TName, Type, Type)

checks the given type to see if it is equal to some pi type of the form
`(x:A1) -> A2`, and if so returns `x`, `A1` and `A2`.  

- When we are checking types, we need to make sure that if the expected type is equivalent
a function type for example, it has the form of a function type. 

    checkType :: Term -> Type -> TcMonad (Term, Type)
    checkType tm expectedTy = do
        nf <- whnf expectedTy               -- determine the 'head-form' of the type
        tcTerm tm (Just nf)

The function 

    whnf :: Term -> TcMonad Term
	 
that reduces a type to its *weak-head normal form*.  Such terms have done all
of the reductions to the outermost lambda abstraction (or pi) but do not
reduce subterms. In other words:

     (\x.x) (\x.x)  
	  
is not in whnf, because there is more reduction to go to get to the head. On
the other hand, even though there are still internal reductions possible:
	  
	  \y. (\x.x) (\x.x)   

and

     (y:Type) -> (\x.x)Bool 

are in weak head normal form. Likewise, the term `x y` is also in weak head
normal form (if we don't have a definition available for `x`) because, even
though we don't know what the head form is, we cannot reduce the term any
more.

## Implementing definitional equality

There are several ways for implementing definitional equality, as stated via
the rules above. The easiest one to explain is based on reduction---for
`equate` to reduce the two arguments to some normal form and then compare
those normal forms for equivalence.

One way to do this is with the following algorithm:

     equate t1 t2 = do 
	    nf1 <- reduce t1   -- reduce the term as much as possible
       nf2 <- reduce t2
		 aeq nf1 nf2
		 
However, we can do better. Sometimes we can equate the terms without
completely reducing them. For example we can already show that `(plus 1 2)`
equals `(plus 1 2)` without doing the addition. When checking for equality
we'd like to only reduce as much as necessary.

     equate t1 t2 = if (aeq t1 t1) then return () else do
		  nf1 <- whnf t1  -- reduce only to 'weak head normal form'
		  nf2 <- whnf t2
        -- compare the head forms, call equate recursively 
		  case (nf1,nf2) of 
		    (App a1 a2, App b1 b2) -> 
			    -- make sure subterms are equal
			    equate a1 b1 >> equate a2 b2
   	    (Lam bnd1, Lam bnd2) -> do
			    -- ignore variable name and typing annot (if present)
			    (_, b1, _, b2) <- unbind2Plus bnd1 bnd2
				 equate b1 b2
			 (_,_) -> err ...

Therefore, we reuse our mechanism for reducing terms to weak-head normal form.

Why weak-head reduction vs. full reduction?

- We can implement deferred substitutions for variables. Note that when
  comparing terms we need to have the definitions available. That way we can
  compute that `(plus 3 1)` weak-head normalizes to 4, by looking up the
  definition of `plus` when needed. However, we don't want to substitute all
  variables through eagerly---not only does this make extra work, but error
  messages can be extremely long.
  
- Furthermore, we allow recursive definitions in pi-forall, so normalization
  may just fail completely. However, this definition based on wnhf only
  unfolds recursive definitions when they are needed, so
  avoids some infinite loops in the type checker.
  
  Note that we don't have a complete treatment of equality though. There will
  always be terms that can cause `equate` to loop forever. On the other hand,
  there will always be terms that are not equated because of conservativity in
  unfolding recursive definitions.
