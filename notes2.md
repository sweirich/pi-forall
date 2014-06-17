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


# Equality in Dependently-Typed Languages

You may have noticed in the previous lecture that there was something
missing. Most of the examples that we did could have also been written in
System F (or something similar)!

Today we are going to think about how type equality can make our language more
expressive.  We will do this in two steps: adding both definitional and
propositional equality to the language.

## Definitional equality

### Motivating Example - Type level reduction

In full dependently-typed languages (and in full pi-forall) we can see the
need for definitional equality. We want to equate types that are not just
*syntactically* equal, so that more expressions type check. 

For example, in the full language, we might have a type of length indexed
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
	 
In our simple language, that doesn't include arbitrary datatypes like
vector, it's more difficult to observe this omission. But here is an example
of some code that requires *beta-equivalence* to check. (This code is for a 
language with a unit type `One` and booleans.)

    T : Bool -> Type
    T = \b. if b then One else Bool

    z1 : T True
    z1 = tt

    z2 : T False
    z2 = True

### Defining definitional equality

The main idea is that we will: 

 - establish a new judgement to define when types are equal

     G |- A = B

 - add the following rule to our type system so that it works "up-to" our
   defined notion of type equivalence

      G |- a : A    G |- A = B
	   ------------------------- conv
	   G |- a : B
	 
 - Figure out how to revise the *algorithmic* version of our type system so
  that it supports the above rule.

What is a good definition of equality?  We started with a very simple one:
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


    G,x:A1 |- b1 = b2
	 ------------------- lam
	 G |- \x.b1 = \x.b2


    G |- a1 = a2    G |- b1 b2 
	 -------------------------- app
	 G |- a1 b1 = a2 b2

    [similar rules for if and sigmas]

that has "functionality" (i.e. we can lift equalities over `b`):

    G, x : A |- b : B    G |- a1 == a2     
    ----------------------------------
    G |- b{a1 / x} = b{a2 / x}


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
  is passed to the checker.

      G |- a => A    G |- A = B
	   -------------------------- :: infer
	   G |- a <= B

- In the rule for application, when we infer the type of the function we need
to make sure that the function actually has a function type. But we don't really 
know what the domain and co-domain of the function should be. We'd like our 
algorithm for type equality to be able to figure this out for us.
  
     G |- a => A    A ?=> (x:A1) -> A2
	  G |- b <= A1
	  ---------------------------------- app
	  G |- a b => A2 { b / x }

### Implementing definitional equality (see `Equal.hs`)

The rules above *specify* when terms should be equal, but they are not an
algorithm. We actually need two different functions:

    equate :: Term -> Term -> TcMonad ()

that ensures that the two provided types are equal, or throws a type error 
if they are not. And

    ensurePi :: Type -> TcMonad (TName, Type, Type)

that checks the given type to see if it is equal to some pi type of the form
`(x:A1) -> A2`, and if so returns `x`, `A1` and `A2`.

There are several ways for implementing definitional equality, as stated via
the rules above. The easiest one to explain is based on reduction---for
`equate` to reduce the two arguments to some normal form and then compare
those normal forms for equivalence.

One way to do this is with the following algorithm:

     equate t1 t2 = do 
	    nf1 <- reduce t1
       nf2 <- reduce t2
		 aeq nf1 nf2
		 
However, we can do better. We'd like to only reduce as much as
necessary. Sometimes we can equate the terms without completely 
reducing them.

     equate t1 t2 = do
  	     when (aeq t1 t1) $ return ()
		  nf1 <- whnf t1  -- reduce only to 'weak head normal form'
		  nf2 <- whnf t2
		  case (nf1,nf2) of 
		    (App a1 a2, App b1 b2) -> 
			    -- make sure subterms are equal
			    equate a1 b1 >> equate a2 b2
   	    (Lam bnd1, Lam bnd2) -> do
			    -- ignore variable name and typing annot (if present)
			    (_, b1, _, b2) <- unbind2Plus bnd1 bnd2
				 equate b1 b2
			 (_,_) -> err ...


Therefore, we need a mechanism for reducing terms to 'weak-head normal form'. 
Such terms have done all of the reductions to the outermost lambda abstraction
(or pi) but, do not reduce subterms. In other words:

     (\x.x) (\x.x)  
	  
is not in whnf, because there is more reduction to go to get to the head. On
the other hand, even though there are still internal reductions possible:
	  
	  \y. (\x.x) (\x.x)   

and

     (y:Type) -> (\x.x)Bool 

are in weak head normal form. Likewise, the term `x y` is also in weak head
normal form because, even though we don't know what the head form is, we
cannot reduce the term any more.

In (Equal.hs)[version2/src/Equal.hs], the function 

     whnf :: Term -> TcMonad Term
	  
does this reduction. We can use this reduction also to implement the `checkPi`
function.

Why weak-head reduction vs. full reduction?

- We can implement deferred substitutions for variables. Note that when
  comparing terms we need to have the definitions available. That way we can
  compute that `(plus 3 1)` weak-head normalizes to 4, by looking up the
  definition of `plus` when needed. However, we don't want to substitute all
  variables through eagerly---not only does this make extra work, but error
  messages can be extremely long.
  
- Furthermore, we allow recursive definitions in pi-forall, so normalization
  may just fail completely. However, this definition based on wnhf only
  unfolds recursive definitions when they are needed, so avoids some infinite
  loops in the type checker.
  
  Note that we don't have a complete treatment of equality though. There will
  always be terms that can cause `equate` to loop forever. On the other hand,
  there will always be terms that are not equated because of conservativity in
  unfolding recursive definitions.

### Discussion of bi-directional rules for booleans and sigma types

    ---------------- Bool
    G |- Bool <=> Type

    ---------------- true
    G |- true <=> Bool
	
	 ------------------- false
    G |- false <=> Bool
	 	 
	 G |- a <= Bool 
	 G |- b <=> A
	 G |- c <=> A
	 ---------------------------- if
	 G |- if a then b else c <=> A
	 
    G |- A <= Type     G, x:A |- B <= Type
    ------------------------------------- sigma
    G |- { x : A | B } <=> Type

    G |- a <= A      G |- b <= B { a / x }
	 ------------------------------------ pair
	 G |- (a,b) <= { x : A | B }
	 
    G |- a => { x : A | B }
	 G, x:A, y:B |- b <=> C
	 G |- C <= Type
    ---------------------------------- weak-pcase
    G |- pcase a of (x,y) -> b <=> C


### Alternative rules for if and pcase

Consider our elimination rules for if:

	 G |- a : Bool 
	 G |- b : A
	 G |- c : A
	 ---------------------------- if
	 G |- if a then b else c : A
	 
We can do better by making the type `A` depend on whether the scrutinee is true
or false.

	 G |- a : Bool 
	 G |- b : A { true/x }
	 G |- c : A { false/x }
	 ---------------------------- if
	 G |- if a then b else c : A{a/x}
	 
It turns out that this rule is difficult to implement (without annotating the
expression with `x` and `A`). Given `A{true/x}`, `A{false/x}`, and `A{a/x}`
(or anything that they are definitionally equal to!) how can we figure out
whether they correspond?

So, we'll not be so ambitious. We'll only allow this refinement when 
the scrutinee is a variable.

	 G |- x : Bool 
	 G |- b : A { true / x }
	 G |- c : A { false / x }
	 ---------------------------- if
	 G |- if x then b else c : A 

And, in going to our bidirectional system, we'll only allow refinement
when we are in checking mode.

	 G |- x => Bool 
	 G |- b <= A { true / x }
	 G |- c <= A { false / x }
	 ------------------------------ if
	 G |- if x then b else c <= A


Then, we only have to remember that x is true / false when checking the
individual branches of the if expression.

Why is this rule useful? 

    bar : (b : Bool) -> T b
    bar = \b .if b then tt else True

    barnot : (b : Bool) -> T (not b) 
    barnot = \b. if b then False else tt

We can modify the rule for sigma types similarly. 

    G |- z => { x : A | B }
	 G, x:A, y:B |- b <= C { (x,y) / z }
	 G |- C <= Type
    ---------------------------------- pcase
    G |- pcase z of (x,y) -> b <= C

This modification changes our definition of Sigma types from weak-Sigmas to
strong-Sigmas. With either typing rule, we can define the first projection

    fst : (A:Type) -> (B : A -> Type) -> (p : { x2 : A | B x2 }) -> A
	 fst = \A B p. pcase p of (x,y) -> x


But, weak-Sigmas cannot define the second projection using pcase. The following 
code only type checks using the above rule.

    snd : (A:Type) -> (B : A -> Type) -> (p : { x2 : A | B x2 }) -> B (fst A B p)
    snd = \A B p. pcase p of (x1,y) -> y

## Propositional equality

You started proving things right away in Coq with an equality proposition. For
example, in Coq, when you say

    Theorem plus_O_n : forall n : nat, 0 + n  = n
	 
You are using a built in type, `a = b` that represents the proposition that
two terms are equal.

As a step towards more general indexed datatypes, we'll start by adding just
this type to pi-forall.

The main idea of the equality type is that it converts a *judgement* that two
types are equal into a *type* that is inhabited only when two types are equal.
In other words, we can write the intro rule for this form as:

     G |- a = b
    ------------------- refl
    G |- refl : a = b
	 
Sometimes, you might see the rule written as follows:

    ------------------- refl'
    G |- refl : a = a
	 
However, this rule will turn out to be equivalent to the above version.

This *type* is well-formed when both sides have the same type. In other words,
when it implements *homogeneous* equality.

    G |- a : A    G |- b : A
    ------------------------- eq
    G |- a = b : Type
	 
The elimination rule for propositional equality allows us to convert the type of 
on expression to another. 
    
	 G |- a : A { a1 / x}   G |- b : a1 = a2  
    --------------------------------- subst
    G |- subst	a by b : A { a2 / x }

How can we implement this rule? For simplicity, we'll play the same trick that
we did with booleans, requiring that one of the sides of the equality be a
variable.

    G |- a <= A { a1 / x }    G |- b => x = a1
	 ------------------------------------------- subst-left
	 G |- subst a by b => A 

    G |- a <= A { a1 / x }    G |- b => a1 = x
	 ------------------------------------------- subst-right
	 G |- subst a by b => A 


Note that our elimination form for equality is still fairly powerful. We can
use it to show that propositional equality is symmetric and transitive.

    sym : (A:Type) -> (x:A) -> (y:A) -> (x = y) -> y = x
    trans : (A:Type) -> (x:A) -> (y:A) -> (z:A) -> (x = z) -> (z = y) -> (x = y)

    
Furthermore, we can extend this once more, when the proof `b` is also a
variable.

    G |- a <= A { a1 / x } { refl / y }    G |- y => x = a1
	 -------------------------------------------------------- subst-left
	 G |- subst a by y => A 

One last addition: `contra`. If we can somehow prove a false, then we should be
able to prove anything. A contradiction is a proposition between two terms
that have different head forms. For now, we'll use:

     G |- p : True = False
    --------------------- contra
     G |- contra p : A

### Homework (pi-forall: more church encodings) 

The file `version2/test/NatChurch.pi` is a start at a Church encoding of
natural numbers.  Replace the TRUSTMEs in this file so that it compiles.

### Homework (pi-forall: equality)

Complete the file [Hw2.pi](version2/test/Hw2.pi). This file gives you practice
with working with equality propositions in pi-forall.

## References

- HoTT book, Sections 1.1 and 1.12 (http://homotopytypetheory.org/book/)
