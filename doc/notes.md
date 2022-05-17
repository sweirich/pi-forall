# GOALS and What to Expect

Over the next four lectures, I will describe a small dependently-typed language
called "pi-forall" and walk through the implementation of its type checker.

What do I want you to get out of these lectures?

1. An understanding of how to translate mathematical specifications of type
   systems and logics into implementations, i.e. how to represent the syntax
   and implement a type checker. More generally, how to turn a declarative
   specification of a system of judgments into an algorithm.
   
2. Exposure to the issues in implmenting dependently-typed languages. Because
   there are only four lectures, my goal is breadth not depth. As a result, I
   will provide you with *simple* solutions to some of the problems you might
   face and sidestep other problems entirely. Overally, the solutions you see 
   here will not be the best solution, but I will give you pointers if you 
   want to go deeper.
   
3. Exposure to the Haskell programming language. I think Haskell is an awesome
   tool for this sort of work and, if there is an advanced feature that
   exactly addresses our design goal (e.g. monads, generic programming,
   laziness) I want to show you how that can work.
   
4. A tool that you can use as a basis for experimentation. How do you know what 
   programs you can and cannot express in your new type system? Having 
   an implementation around lets you work out (smallish) examples and will 
   help to convince you (and your reviewers) that you are developing something
   useful.

Questions should you be thinking about during these sessions:

- How to represent the abstract syntax of the language, including variable binding?
- How much information do we need to include in terms to make type checking
  algorithmic?
- How can we include less?
- How to decide when types (and terms) are equal?
- How to decide what parts of the term are irrelevant during computation? Can
  be ignored when checking for equality?


## A Simple Core language with Type in Type

Let's consider a simple dependently-typed lambda calculus. What should it
contain? At the bare minimum we can start with the following five forms:

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

### When do expressions in this language type check?

We define the type system for this language using an inductively defined
relation. This relation is between an expression, its type, and a typing
context.

     G |- a : A

The typing context is an ordered list of assumptions about the types of
variables. 

 
     G ::= . | G, x : A

### An initial set of typing rules - Variables and Functions

If we know a variable's type because it is in the typing context, then that is
its type:

       x : A in G
      ----------- var 
      G |- x : A

Variables are introduced into the context when we type check 
abstractions. 

        G, x:A |- a : B
	 ---------------------------------    lambda
     G |- \x.a : (x:A) -> B

### Example: Polymorphic identity functions

Note that the variable `x` is allowed to appear in `B`. Why is this useful? Well
it gives us *parametric polymorphism* right off the bat.  In Haskell, we 
write the identity function as follows:

       id :: a -> a
       id x = x

and Haskell automatically generalizes it to work for *all* types. 
We can do that here, except that we need to explicitly use lambda 
to make this function polymorphic. Instead of Haskell's 

       forall a. a -> a
		 
we will write the type of the polymorphic identity function as

       (x:Type) -> (y : x) -> x
		 
The fact that the type of `x` is `Type` means that `x` is a type variable. Again,
in this language we don't have a syntactic distinction between types and
terms (or expressions). Types are anything of type `Type`.  Expressions are 
things of type `A` where `A` has type `Type`.

          --------------------- var
           x:Type, y:x |- y : x
        ----------------------------- lambda
         x:Type |- \y. y : (y : x) -> x
     ------------------------------------------ lambda
      |- \x. \y. y : (x:Type) -> (y : x) -> x

In pi-forall, we should eventually be able to write

     id : (x:Type) -> (y : x) -> x
     id = \x. \y. y

or even (with some help from the parser)

     id : (x:Type) -> x -> x
     id = \x y . y 

### More typing rules - Types

Actually, I lied.  The real typing rule that we want for lambda 
has an additional precondition. We need to make sure that when we 
add assumptions to the context, those assumptions really are types. 
Otherwise, the rules would allow us to derive this type for the 
polymorphic lambda calculus:

     |- \x.\y. y : (x: 3) -> (y:x) -> x

So the real rule has an extra precondition that checks to make sure that 
`A` is actually a type. 

       G, x:A |- a : B       G |- A : Type
	 ----------------------------------------    lambda
     G |- \x.a : (x:A) -> B

This precondition means that we need some rules that conclude that 
types are actually types. For example, the type of a function is a 
type, so we will declare it with this rule (which also ensures that the
domain and range of the function are also types).

    G |- A : Type     G, x:A |- B : Type
    -------------------------------------- pi
     G |- (x:A) -> B : Type
	  
	  
Likewise, for polymorphism we need this, rather perplexing rule:	  
	  
	  ----------------  type
	  G |- Type : Type

Because the type of the polymorphic identity function starts with 
`(x:Type) -> ...` the `pi` rule means that `Type` must be a type for this pi
type to make sense. We declare this by fiat using the type : type rule. 

Note that, sadly, this rule make our language inconsistent as a
logic. cf. Girard's paradox.

### More typing rules - Application

Application requires that the type of the argument matches the domain type of
the function. However, note that because the type `B` could have `x` free in it,
we need to substitute the argument for `x` in the result.

      G |- a : (x:A) -> B 
	  G |- b : A
    ---------------------------  app
	  G |- a b : B { b / x }

### Example: applying the polymorphic identity function

In pi-forall we should be able to apply the polymorphic identity function to
itself. When we do this, we need to first provide the type of `id`, then we can
apply `id` to `id`.

    idid : (x:Type) -> (y : x) -> x 
    idid = id ((x:Type) -> (y : x) -> x) id

### Example: Church booleans

Because we have (impredicative) polymorphism, we can *encode* familiar types,
such as booleans. The idea behind this encoding is to represent terms by their
eliminators. In other words, what is important about the value true? The fact
that when you get two choices, you pick the first one.  Likewise, false
"means" that with the same two choices, you should pick the second one.
With parametric polymorphism, we can give the two terms the same type, which
we'll call bool. 

    bool : Type
    bool = (x : Type) -> x -> x -> x

    true : bool
    true = \x . \y. \z. y
	 
    false : bool
    false = \x. \y. \z. z

Thus, a conditional expression just takes a boolean and returns it.

    cond : bool -> (x:Type) -> x -> x -> x
    cond = \ b . b 

### Example: logical and  (i.e. product types)

During lecture 1, instead of encoding booleans, we encoded a logical "and"
data structure.

    and : Type -> Type -> Type
    and = \p. \q. (c: Type) -> (p -> q -> c) -> c

    conj : (p:Type) -> (q:Type) -> p -> q -> and p q
    conj = \p.\q. \x.\y. \c. \f. f x y

    proj1 : (p:Type) -> (q:Type) -> and p q -> p
    proj1  = \p. \q. \a. a p (\x.\y.x)

    proj2 : (p:Type) -> (q:Type) -> and p q -> q
    proj2  = \p. \q. \a. a q (\x.\y.y)

    and_commutes : (p:Type) -> (q:Type) -> and p q -> and q p
    and_commutes = \p. \q. \a. conj q p (proj2 p q a) (proj1 p q a)

# From typing rules to a typing algorithm

So the rules that we have developed so far are great for saying *what* terms
should type check, but they don't say *how*.  In particular, we've developed
these rules without thinking about how we would implement them.

A type system is called *syntax-directed* if it is readily apparent how to
turn the typing rules into code. In otherwords, we would like to implement the 
following function (in Haskell), that when given a term and a typing context 
produces the type of the term (if it exists).

    inferType :: Term -> Ctx -> Maybe Type

Let's look at our rules. Is this straightforward? For example, for the
variable rule as long as we can lookup the type of a variable in the context, 
we can produce its type. 

    inferType (Var x) ctx = Just ty when
	      ty = lookupTy ctx x
			
Likewise typing for Type is pretty straightforward.

    inferType Type ctx = Just Type

The only stumbling block for the algorithm is the lambda rule. The type
`A` comes out of thin air. What could it be?

There's actually an easy fix to turn our current system into an algorithmic
one. We just annotate lambdas with the types of the abstracted variables. 
But perhaps this is not what we want to do. 

Look at our example code: the only types that we wrote were the types of
definitions. It's good style to do that, and maybe if we change our point of
view we can get away without those argument types. 

# A Bidirectional type system

Let's redefine the system using two judgments: the standard judgement that we
wrote above, called type inference, but make it depend on a checking
judgement, that let's us take advantage of known type information.

    G |- a => A    inferType     in context G, infer that a has type A
	 
    G |- a <= A    checkType     in context G, check that a has type A


We'll go back to some of our existing rules. For variables, we can just change
the colon to an inference arrow. The context tells us the type to infer.

       x : A in G
      ----------- var 
      G |- x => A
		
On the other hand, we should check lambda expressions against a known type. If that 
type is provided, we can propagate it to the body of the lambda expression. We also 
know that we want A to be a type.		

     G, x:A |- a <= B       G |- A <= Type
	 ----------------------------------------    lambda
     G |- \x.a <= (x:A) -> B
	  
Applications can be in inference mode (in fact, checking mode doesn't help.)
Here we must infer the type of the function, but once we have that type, we
may to use it to check the type of the argument.
	  
      G |- a => (x:A) -> B 
      G |- b <= A
    ---------------------------  app
	  G |- a b => B { b / x }	  

For types, it is apparant what their type is, so we will just continue to infer that.

    G |- A <= Type     G, x:A |- B <= Type
    -------------------------------------- pi
    G |- (x:A) -> B => Type

	  ----------------  type
	  G |- Type => Type
	  
Notice that this system is fairly incomplete. There are inference rules for
every form of expression except for lambda. On the other hand, only lambda
expressions can be checked against types.  We can make checking more
applicable by the following rule:

       G |- a => A
       -------------  (a does not have a checking rule)
       G |- a <= A 

which allows us to use inference whenever checking doesn't apply.

Let's think about the reverse problem a bit. There are programs that the checking
system won't admit but would have been acceptable by our first system. What do
they look like?

Well, they involve applications of explicit lambda terms:

       |- \x.x : bool -> bool     |- true : bool
      ------------------------------------------  app
       |- (\x.x) true : bool

This term doesn't type check in the bidirectional system because application
requires the function to have an inferable type, but lambdas don't.

However, there is not that much need to write such terms in programs. We can
always replace them with something equivalent by doing the beta-reduction (in
this case, just true).

In fact, the bidirectional type system has the property that it only checks
terms in *normal* form, i.e. those that do not contain any reductions. If we
would like to add non-normal forms to our language, we can add annotations:

        G |- a <= A 
	  ------------------ annot
	  G |- (a : A) => A

The nice thing about the bidirectional system is that it reduces the number of
annotations that are necessary in programs that we want to write. As we will see, 
checking mode will be even more important as we add more terms to the language.

A not so desirable property is that the bidirectional system is not closed
under substitution. The types of variables are always inferred.  This is
particularly annoying for the application rule when we replace a variable
(inference mode) with another term that is correct only in checking mode.  One
solution to this problem is to work with *hereditary substitutions*,
i.e. substitutions that preserve normal forms.

Alternatively, we can solve the problem through *elaboration*, the output 
of a type checker will be a term that works purely in inference mode.


### References 

* Cardelli, [A polymorphic lambda calculus with Type:Type](http://www.hpl.hp.com/techreports/Compaq-DEC/SRC-RR-10.pdf)
* Augustsson, [Cayenne -- a Language With Dependent Types](http://dl.acm.org/citation.cfm?id=289451)
* A. Löh, C. McBride, W. Swierstra, [A tutorial implementation of a dependently typed lambda calculus](http://www.andres-loeh.de/LambdaPi/)
* Andrej Bauer, [How to implement dependent type theory](http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/)
* Dunfield and Krishnaswami, [Bidirectional Typing](https://www.cl.cam.ac.uk/~nk480/bidir-survey.pdf)
    
* Friedman and Christiansen, The Little Typer.

* Christiansen, Tutorial on Bidirectional Typing.
https://www.davidchristiansen.dk/tutorials/bidirectional.pdf
* Peyton Jones, Vytiniotis, Weirich, Shields. [Practical type inference for arbitrary-rank types](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/putting.pdf)


* Coquand, Kinoshita, Nordstrom, Takeyama.  A simple type-theoretic language: Mini-TT
https://www.cse.chalmers.se/~bengt/papers/GKminiTT.pdf
* Daniel Gratzer, NBE for MLTT
https://github.com/jozefg/nbe-for-mltt
* Andras Kovacs, Elaboration Zoo
https://github.com/AndrasKovacs/elaboration-zoo/ 