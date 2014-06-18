
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

We saw yesterday an example where we wanted a definition of equality that was
more expressive than alpha-equivalence. Recall our encoding for the logical
`and` proposition:

    and : Type -> Type -> Type
    and = \p. \q. (c: Type) -> (p -> q -> c) -> c

Unfortunately, our definition of `conj` still doesn't type check:

    conj : (p:Type) -> (q:Type) -> p -> q -> and p q
    conj = \p.\q. \x.\y. \c. \f. f x y

Running this example with `version1` of the type checker produces the
following error:

    Checking module "Lec1"
    Type Error:
    ../test/Lec1.pi:34:22:
        Function a should have a function type. Instead has type and p q
        When checking the term 
           \p . \q . \a . a p ((\x . \y . x))
        against the signature
           (p : Type) -> (q : Type) -> (and p q) -> p
        In the expression
           a p ((\x . \y . x))

The problem is that even though we want `and p q` to be equal to the type 
`(c: Type) -> (p -> q -> c) -> c` the typechecker does not treat these types as
equal. 

Note that the type checker already records in the environment that `and` is
defined as `\p.\q. (c: Type) -> (p -> q -> c) -> c`. We'd like the type
checker to look up this definition when it sees the variable `and` and
beta-reduce th this application.

### Another example needing more expressive equality

As another example, in the full language, we might have a type of length indexed
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
	  

## Using definitional equality

The rules above *specify* when terms should be equal, but they are not an
algorithm. We actually need several different functions. First,

    equate :: Term -> Term -> TcMonad ()

ensures that the two provided types are equal, or throws a type error 
if they are not. This function corresponds directly to our definition of 
type equality.

Second, we also need to be able to determine whether a given type is equal to
some "head" form, without knowing exactly what that form is. For example, when
*checking* lambda expressions, we need to know that the provided type is of
the form of a pi type (`(x:A) -> B`). Likewise, when inferring the type of an
application, we need to know that the type inferred for the function is actually 
a pi type.  

We can determine this in two ways. Most directly, the function

    ensurePi :: Type -> TcMonad (TName, Type, Type)

checks the given type to see if it is equal to some pi type of the form
`(x:A1) -> A2`, and if so returns `x`, `A1` and `A2`.  
This function is defined in terms of a helper function:

    whnf :: Term -> TcMonad Term
	 
that reduces a type to its *weak-head normal form*. 	 

In `version2` of the the [implementation](version2/src/TypeCheck.hs), these 
functions are called in a few places: 
  - `equate` is called at the end of `tcTerm`
  - `ensurePi` is called in the `App` case of `tcTerm`
  - `whnf` is called in `checkType`, before the call to `tcTerm` to make sure that 
  we are using the head form in checking mode.


## Implementing definitional equality (see `Equal.hs`)

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


Therefore, we need a mechanism for reducing terms to weak-head normal form.
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
