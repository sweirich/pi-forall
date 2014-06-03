# Equality 

You may have noticed in the previous lecture that there was something
missing. Most of the examples that we did could have also been written in
System F (or something similar)!

# Definitional equality

## Motivating Example - Type level reduction

TODO: find a better example?

    bool' : Bool -> Type
    bool' = \b . (B : (b : bool) -> Type) -> B true -> B false -> B b

    true' : bool' true
    true' = \A x y . x

    false' : bool' false
    false' = \ A x y. y

## Defining definitional equality

We need to know when terms/types are equal to eachother:

    G |- A = B

What is a good definition of equality?  We started with a very simple one:
alpha-equivalence. But we can do better:

Contains beta

    -------------------------- beta
    G |- (\x.a)b = a {b / x}
	 
	 ------------------------------- iftrue
	 G |- if true then a else b = a

	 ------------------------------- iftrue
	 G |- if false then a else b = a

	 -------------------------------------------------- prod
	 G |- pcase (a1,a2) of (x,y) -> b = b {a1/x}{a2/y}


Equivalence relation

    ----------  refl
    G |- A = A
	 
	 G |- A = B
	 -----------  sym
	 G |- B = A
	 
	 G |- A = B    G |- B = C
	 ------------------------- trans
	 G |- A = C

A congruence relation

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

That has functionality (i.e. we can lift equalities over b)

    G, x : A |- b : B    G |- a1 == a2     
    ----------------------------------
    G |- b{a1 / x} = b{a2 / x}

## Implementing definitional equality

Delayed substitutions 

Whnf

## Using definitional equality

We would like to consider our type system as having the following rule:

    G |- a : A    G |- A = B
	 ------------------------ conv
	 G |- a : B

But that rule is not syntax directed. Where do we need to add equality predonditions in our bidirectional system?

## Really using definitional equality

Consider our elimination rules for if:

	 G |- a : Bool 
	 G |- b : A
	 G |- c : A
	 ---------------------------- if
	 G |- if a then b else c : A
	 
We can do better by making the type A depend on whether the scrutinee is true
or false.

	 G |- a : Bool 
	 G |- b : A true   
	 G |- c : A false
	 ---------------------------- if
	 G |- if a then b else c : A a
	 
It turns out that this rule is difficult to implement (without annotating the
expression with A). Given A true, A false, and A a (or anything that they are
definitionally equal to!) how can we figure out whether they correspond?

So, we'll not be so ambitious. We'll only allow this refinement when 
the scrutinee is a variable

	 G |- x : Bool 
	 G |- b : A { true / x }
	 G |- c : A { false / x }
	 ---------------------------- if
	 G |- if x then b else c : A 

Then, we only have to remember that x is true / false when checking 
the individual branches of the if expression.

TODO: motivating example

# Propositional equality

You will have noticed that Coq includes an equality type. As a step towards
more general indexed datatypes, we'll start by adding just this type here.

The main idea of the equality type is that it converts a judgement that two
types are equal into a type that is inhabited only when two types are equal.

     G |- a = b
    ------------------- refl
    G |- refl : a = b
	 

    G |- a : A    G |- b : A
    ------------------------- eq
    G |- a = b : Type
