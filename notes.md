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
`x` in `b` and `B` respectively

### When do expressions in this language type check?

We define the type system for this language using an inductively defined
relation. This relation is between an expression, its type, and a typing
context.

     G |- a : A

The typing context is an ordered list of assumptions about the types of
variables. 

### An initial set of typing rules - Variables and Functions

If we know a variable's type because it is in the typing context, then that is
its type:

       x : A in G
      ----------- var 
      G |- x : A

Functions get function types

        G, x:A |- a : B     
	 ---------------------------------    lambda
     G |- \x.a : (x:A) -> B

### Example: Polymorphic identity functions

Note that the variable x is allowed to appear in `B`. Why is this useful? Well
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
         x:Type |- y : (y : x) -> x
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
A is actually a type. 

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
logic. Girard's paradox

### More typing rules - Application

Application requires that the type of the argument matches the domain type of
the function. However, not that because the type B could have x free in it, we
need to substitute the argument for x in the result.

      G |- a : (x:A) -> B 
		G |- b : A
    ---------------------------  app
	   G |- a b : B { b / x }

### Example: applying the polymorphic identity function

In pi-forall we should be able to apply the polymorphic identity function to
itself. When we do this, we need to first provide the type of id, then we can
apply id to id.

    idid : ((x:Type) -> (y : x) -> x) 
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

For types, it is apparent what their type is, so we will just continue to infer that.

    G |- A => Type     G, x:A |- B => Type
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
particularly annoying for the application rule when replace a variable
(inference mode) with another term that is correct only in checking mode.  One
solution to this problem is to work with *hereditary substitutions*,
i.e. substitutions that preserve normal forms.

Alternatively, we can solve the problem through *elaboration*, the output 
of a type checker will be a term that works purely in inference mode.

# Putting it all together in a Haskell implementation

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

### Homework (Type Theory & Haskell) - Add Booleans and Sigma types

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
    ------------------------------ pcase
    G |- pcase a of (x,y) -> b : C

This part of the homework has two parts:

1. On paper: rewrite the rules above in bidirectional style. Which rules
  should be inference rules? Which ones should be checking rules? If you are 
  familiar with other systems, how do these rules compare?
 
2. In Haskell: The code in `version1/` includes abstract and concrete syntax 
  for booleans and sigma types. The pi-forall file `version1/test/Hw1.pi` contains 
  examples of using these new forms. However, to get this file
  to compile, you'll need to fill in the missing cases in `version1/src/TypeCheck.hs`.

### Homework (pi-forall) 

If Haskell is unfamiliar to you, an alternative assignment is to learn more
about this language by writing code in pi-forall. For this part, you should 
use `version2` of pi-forall.

One thing this language can do is Church encoding. The file
`version2/test/NatChurch.pi` is a start at a Church encoding of natural
numbers.  Replace the TRUSTMEs in this file so that it compiles.

### References 

* Cardelli, [A polymorphic lambda calculus with Type:Type](http://www.hpl.hp.com/techreports/Compaq-DEC/SRC-RR-10.pdf)
* Augustsson, [Cayenne -- a Language With Dependent Types](http://dl.acm.org/citation.cfm?id=289451)
* A. Löh, C. McBride, W. Swierstra, [A tutorial implementation of a dependently typed lambda calculus](http://www.andres-loeh.de/LambdaPi/)
* Andrej Bauer, [How to implement dependent type theory](http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/)

    

