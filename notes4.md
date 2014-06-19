# Datatypes and Indexed Datatypes

Today we'd like to add datatypes and erasable arguments to pi-forall. The code to 
look at is the "complete" implementation in [soln](soln/).

Unfortunately, datatypes are both:

* Really important (you see them *everywhere* when working 
  with languages like Coq, Agda, Idris, etc.)
* Really complicated (there are a *lot* of details.)

Unlike the prior two lectures, where we could walk through all of the details
of the specification of the type system, not to mention its implementation, we
won't be able to do that here. There is just too much! My goal is to give you
enough information so that you can pick up the Haskell code and understand
what is going on. 

Even then, realize that the implementation that I'm giving you is not the
complete story! Recall that we're not considering termination. That means that
we can think about eliminating datatypes merely by writing recursive
functions; without having to reason about whether those functions
terminate. Coq, Agda and Idris include a lot of machinery for this
termination analysis, and we won't cover any of it.

We'll work up the general specification of datatypes piece-by-piece,
generalizing from features that we already know to more difficult cases.
We'll start with "simple" datatypes, and then extend them with both parameters
and indices.

## "Dirt simple" datatypes 

Our first goal is simple. What do we need to get the simplest examples of
non-recursive and recursive datatypes working? By this I mean datatypes that
you might see in OCaml or ML, such as `Bool`, `Void` and `Nat`.

### Booleans

For example, one homework assignment was to implement 
booleans. Once we have booleans then we can 

      data Bool : Type where
         True 
         False
        
In the homework assignment, we used `if` as the elimination form 
for boolean values.
        
     not : Bool -> Bool
     not = \ b . if b then False else True
        
For uniformity, we'll have a common elimination form for all datatypes, called
`case` that has branches for all cases. (We'll steal Haskell syntax for case
expressions, including layout.) For example, we might rewrite `not` with case
like this:
        
     not : Bool -> Bool
     not = \ b . 
        case b of 
           True -> False
           False -> True

### Void

The simplest datatype of all is one that has no constructors! 

    data Void : Type where {}
     
Because there are no constructors, the elimination form for values of this
type doesn't need any cases!
     
    false_elim : (A:Type) -> Void -> A
    false_elim = \ A v . case v of {} 
	 
Void brings up the issue of *exhaustiveness* in case analysis. Can we tell
whether there are enough patterns so that all of the cases are covered? 

### Nat

Natural numbers include a data constructor with an argument. For simplicity in
the parser, those parens must be there.

    data Nat : Type where
       Zero
       Succ of (Nat)

In case analysis, we can give a name to that argument in the pattern.

    is_zero : Nat -> Bool
    is_zero = \ x . case x of 
       Zero -> True
       Succ n -> False
       
### Dependently-typed data constructor args

Now, I lied. Even in our "dirt simple" system, we'll be able to encode some
new structures, beyond what is available in functional programming languages
like Haskell and ML. These structures won't be all that useful yet, but as we
add parameters and indices to our datatypes, they will be. For example, here's
an example of a datatype declaration where the data constructors have
dependent types.

    data SillyBool : Type where      
       ImTrue  of (b : Bool) (_ : b = True)
       ImFalse of (b: Bool)  (_ : b = False)
       
## Specifying the type system with basic datatypes

Datatype declarations, such as `data Bool`, `data Void` or `data Nat` extend
the context with new type constants (aka type constructors) and new data
constructors. It is as if we had added a bunch of new typing rules to the type
system, such as:

       ---------------
       G |- Nat : Type

       ----------------
       G |- Void : Type
       
      -----------------
       G |- Zero : Nat
       
         G |- n : Nat
       -----------------
       G |- Succ n : Nat

       G |- a1 : Bool    G |- a2 : a1 = True
      ---------------------------------------
       G |- ImTrue a1 a2 : SillyBool
       
In the general form, a *simple* data type declaration includes a name and a
list of data constructors.

       data T : Type where
          K1        -- no arguments
          K2 of (A)    -- single arg of type A
          K3 of (x:A)  -- also single arg of type A, called x for fun
          K4 of (x:A)(y:B) -- two args, the type of B can mention A.

In fact, each data constructor takes a special sort of list of arguments that
we'll call a 'telescope'.  (The word 'telescope' for this structure was coined
by de Bruijn to describe the scoping behavior of this structure. The scope of
each variable overlaps all of the subsequent ones, nesting like an expandable
telescope.)

We can represent this structure in our implementation by adding a new form of
declaration (some parts have been elided compared to `soln`, we're
building up to that version.)

     -- | type constructor names
     type TCName = String

     -- | data constructor names
     type DCName = String

     data Decl = ...
       | Data    TCName [ConstructorDef]

     -- | A Data constructor has a name and a telescope of arguments
     data ConstructorDef = ConstructorDef DCName Telescope
           deriving (Show)

     data Telescope = Empty
                    | Cons TName Term Telescope
                         deriving (Show)
								 
For example, a declaration for the `Bool` type would be 
   
	   boolDecl :: Decl 
      boolDecl = Data "Bool" [ConstructorDef "False" Empty, 
		                        ConstructorDef "True" Empty]
										
## Checking (simple) data constructor applications

When we have a datatype declaration, that means that new data type `T` of type
`Type` will be added to the context. Furthermore, the context should record
all of the type constructors for that type, `Ki`, as well as the telescope,
written `Di` for that data constructor.  This information will be used to
check terms that are the applications of data constructors. For simplicity,
we'll assume that data constructors must be applied to all of their arguments.

So our typing rule looks a little like this. We have `as` as representing the 
list of arguments for the data constructor `Ki`.

      Ki : Di -> T  in G
      G |- as : Di
		------------------------ simpl-constr
		G |- Ki as : T
		
We need to check that list against the telescope for the constructor. Each
argument must have the right type. Furthermore, because of dependency, we
substitute that argument for the variable in the rest of the telescope.
		
		G |- a : A       G |- as : D { a / x }
		--------------------------------------- tele-arg
		G |- a as : (x:A) D
		
When we get to the end of the list (i.e. there are no more arguments) we should 
also get to the end of the telescope.		
		
		----------- tele-empty
		G |-  : 

In `TypeCheck.hs`, the function `tcArgTele` essentially implements this
judgement.  (For reasons that we explain below, we have a special type `Arg`
for the arguments to the data constructor.)

     tcArgTele :: [Arg] -> Telescope -> TcMonad [Arg]
	  
This function relies on the following substitution function for telescopes:

     doSubst :: [(TName,Term)] -> Telescope -> TcMonad Telescope

      
## Eliminating dirt simple datatypes

In your homework assignment, we used if to eliminate boolean types. Here, we'd
like to be more general, and have a `case` expression that works with any form
of datatype. What should the typing rule for that sort of expression look
like?  Well, the pattern for each branch should match up the telescope for the
corresponding data constructor.


     G |- a : T
	  Ki : Di -> T  in G       
	  G, Di |- ai : A
	  G |- A : Type
	  branches exhaustive
     ------------------------------------- case-simple
     G |- case a of { Ki xsi -> ai } : A

Note that this version of case doesn't witness the equality between the
scrutinee `a` and each of the patterns in the branches. To allow that, we 
can add a substiution to the result type of the case:

     G |- a : T
	  Ki : Di -> T  in G       dom(Di) = xsi
	  G, Di |- ai : A { Ki xsi / x }
	  G |- A : T -> Type
	  branches exhaustive
     -------------------------------------------- case
     G |- case a of { Ki xsi -> ai } : A { a / x}

How do we implement this rule in our language? The general for type checking a
case expression `Case scrut alts` of type `ty` is as follows:

1. Infer type of the scrutinee `scrut`
2. Make sure that the inferred type is some type constructor (`ensureTCon`)
3. Make sure that the patterns in the case alts are 
   exhaustive (`exhausivityCheck`)
3. For each case alternative:
  - Create the declarations for the variables in 
   the pattern (`declarePat`)
  - Create defs that follow from equating the scrutinee `a` with the 
   pattern (`equateWithPat`)
  - Check the body of the case in the extended context against 
   the expected type
	
## Datatypes with parameters 

The first extension of the above scheme is for *parameterized datatypes*. 
For example, in pi-forall we can define the `Maybe` type with the following
declaration. The type parameter for this datatype  `A` can be referred to in 
any of the telescopes for the data constructors.

    data Maybe (A : Type) : Type where
	    Nothing 
		 Just of (A)
		 
Because this is a dependently-typed language, the variables in the telescope
can be referred to later in the telescope. For example, with parameters, we can 
implement Sigma types as a datatype, instead of making them primitive:

    data Sigma (A: Type) (B : A -> Type) : Type
	    Prod of (x:A) (B)

The general form of datatype declaration with parameters includes a telescope
for the type constructor, as well as a telescope for each of the data
constructors.

    data T D : Type where
       Ki of Di 

That means that when we check an occurrence of a type constructor, we need to
make sure that its actual arguments match up the parameters in the
telescope. For this, we can use the argument checking judgement above.

      T : D -> Type in G
		G |- as : D
      --------------------   tcon
      G |- T as : Type

We modify the typing rule for data constructors by marking the telescope
for type constructor in the typing rule, and then substituting the actual
arguments from the expected type:

      Ki : D . Di -> T  in G
      G |- as : Di { bs / D }
		------------------------ param-constr
		G |- Ki as : T bs
		
For example, if we are trying to check the expression `Just True`, with
expected type `Maybe Bool`, we'll first see that `Maybe` requires the
telescope `(A : Type)`.  That means we need to substitute `Bool` for `A` in
`(_ : A)`, the telescope for `Just`. That produces the telescope `(_ : Bool)`,
which we'll use to check the argument `True`.

In `TypeCheck.hs`, the function  

    substTele :: Telescope -> [ Term ] -> Telescope -> TcMonad Telescope
	 
implements this operation of substituting the actual data type arguments for
the parameters.

Note that by checking the type of data constructor applications (instead of
inferring them) we don't need to explicitly provide the parameters to the data
constructor. The type system can figure them out from the provided type. 

Also note that checking mode also enables *data constructor overloading*. In
other words, we can have multiple datatypes that use the same data
constructor. Having the type available allows us to disambiguate.

For added flexibility we can also add code to *infer* the types of data
constructors when they are not actually parameterized (and when there is no
ambiguity due to overloading).

## Datatypes with indices	

The final step is to index our datatypes with constraints on the
parameters. Indexed types let us express inductively defined relations, such
as `beautiful` from Software Foundations.

    Inductive beautiful : nat → Prop :=
      b_0 : beautiful 0
    | b_3 : beautiful 3
    | b_5 : beautiful 5
    | b_sum : ∀n m, beautiful n → beautiful m → beautiful (n+m).

Even though `beautiful` has type `nat -> Prop`, we call `nat` this argument an
index instead of a parameter because it is determined by each data
constructor. It is not used uniformly in each case.

In pi-forall, we'll implement indices by explictly *constraining*
parameters. These constraints will just be expressed as equalities written in 
square brackets. In otherwords, we'll define `beautiful` this way:

    data Beautiful (n : Nat) : Type where
	    B0 of [n = 0]
		 B3 of [n = 3]
		 B5 of [n = 5]
		 Bsum of (m1:Nat)(m2:Nat)(Beautiful m1)(Beautiful m2)[m = m1+m2]
		 
Constraints can appear anywhere in the telescope of a data
constructor. However, they are not arbitrary equality constraints---we want to
consider them as deferred substitutions. So therefore, the term on the left
must always be a variable.

These constraints interact with the type checker in a few places:

- When we use data constructors we need to be sure that the constraints are
  satisfied, by appealing to definitional equality when we are checking
  arguments against a telescope (in `tcArgTele`).

		G |- x = b      G |- as : D
		--------------------------------------- tele-constraint
		G |- as : (x = b) D		

- When we substitute through telescopes (in `doSubst`), we may need to rewrite
  a constraint `x = b` if we substitute for `x`.

- When we add the pattern variables to the context in each alternative of a
  case expression, we need to also add the constraints as definitions.
  (see `declarePats`).

For example, if we check an occurrence of `B3`, i.e. 

    threeIsBeautiful : Beautiful 3
    threeIsBeautiful = B3
	 
this requires substituting `3` for `n` in the telescope `[n = 3]`.  That
produces an empty telescope.

### Homework: Parameterized datatypes and proofs: logic

Translate the definitions and proofs 
in [Logic chapter of Software Foundations](http://www.cis.upenn.edu/~bcpierce/sf/current/Logic.html) 
to pi-forall. See [Logic.pi](soln/test/Logic.pi) for a start.

### Homework: Indexed datatypes: finite numbers in `Fin1.pi`

The module `Fin1.pi` declares the type of numbers that are drawn from some
bounded set. For example, the type `Fin 1` only includes 1 number (called
Zero), `Fin 2` includes 2 numbers, etc.  More generally, `Fin n` is the type
of all natural numbers smaller than `n`, i.e. of all valid indices for lists
of size `n`.
  
In [Agda](http://www.cse.chalmers.se/~nad/repos/lib/src/Data/Fin.agda), 
we might declare these numbers as: 

    data Fin : ℕ → Set where
       zero : {n : ℕ} → Fin (suc n)
       suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

In pi-forall, this corresponding definition makes the constraints explicit:

    data Fin (n : Nat) : Type where
       Zero of (m:Nat)[n = Succ m] 
       Succ of (m:Nat)[n = Succ m] (Fin m)
		 
The file [Fin1.pi](soln/test/Fin1.pi) includes a number of definitions
that use these types. However, there are some `TRUSTME`s. Replace these with
the actual definitions.

## References

- Coq pattern matching: [Coq User manual](http://coq.inria.fr/refman/Reference-Manual006.html#Cic-inductive-definitions)
- Agda pattern matching: [Ulf Norell's dissertation](http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf)
- Haskell GADTs: [Dimitrios Vytiniotis, Simon Peyton Jones, Tom Schrijvers, and Martin Sulzmann, OutsideIn(X): Modular type inference with local assumptions](http://research.microsoft.com/apps/pubs/default.aspx?id=162516)


# Erasure (aka forall types)
=============================

Last thing, let's talk about erasure. In dependently typed languages, some
arguments are "specificational" and only there for proofs. For efficient
compilation, we don't want to have to "run" these arguments, nor do we want
them taking up space in data structures.

Functional languages do this all the time: they erase *type annotations* and
*type* arguments before running the code. This erasure makes sense because of
parametric polymorphic functions are not allowed to depend on types. The
behavior of map must be the same no matter whether it is operating on a list
of integers or a list of booleans. 

In a dependently-typed language we'd like to erase types too. And proofs that
are only there to make things type check.  Coq does this by making a
distinction between `Prop` and `Set`. Everything in `Set` stays around until
runtime, and is guaranteed not to depend on `Prop`. 

We'll take another approach.

In pi-forall we have new kind of quantification, called "forall" that marks
erasable arguments.  We mark forall quantified arguments with brackets. For example, 
we can mark the type argument of the polymorphic identity function as erasable.

    id : [x:Type] -> (y : x) -> x
    id = \[x] y. y

When we apply such functions, we'll put the argument in brackets too, so we
remember that `id` is not really using that type.

    t = id [Bool] True

However, we need to make sure that erasable arguments really are eraseable. We
wouldn't want to allow this definition:

    id' : [x:Type] -> [y:x] -> x
    id' = \[x][y]. y
	 
Here `id'` claims that its second argument is erasable, but it is not.	 
 
## How do we rule this out? 

We need to make sure that x is not "used" in the body.

    G |- A : Type
    G, x:A |- a : B
	 << x is not used in a >>
    ---------------------------- erased-lam
    G |- \[x].a : [x:A] -> B

What is a use? Does a type annotation count? Does it change the runtime 
behavior of the program?

    m : [x:Type] -> (y:x) -> x
    m = \[x] y . (y : x)

What about putting it in data structures? We should be able to define
datatypes with "specificational arguments". For example, 
see [Vec.pi](soln/test/Vec.pi).

Note: we can only erase *data* constructor arguments, not types that appear as
arguments to *type* constructors. (Parameters to type constructors must always
be relevant, they determine the actual type.)  On the other hand, datatype
parameters are never relevant to data constructors---we don't even represent
them in the abstract syntax.  

### Homework: Erasure and Indexed datatypes: finite numbers in `Fin1.pi`

Now take your code in `Fin1.pi` and see if you can mark some of the components
of the `Fin` datatype as eraseable. 

## ERASURE and equality
------------------------

We've been alluding to this the whole time, but now we'll come down to it.  We're
actually *defining* equality over "erased" terms instead of the terms
themselves.  Note how the definition of equate ignores 'eraseable' elements
like type annotations, erasable arguments, etc.

Why is this important?
  - faster comparison: don't have to look at the whole term when comparing for 
    equality. Coq / Adga look at type annotations
  - more expressive: don't have to *prove* that those parts are equal 
    (proof irrelevance!)
  - this gets really crazy with heterogeneous equality
  - and it is sound: see Miquel (ICC), Barras


## What next?
------------

- Termination checking
- Pattern match compilation
- Univalence

## References
-------------

Miquel. [Implicit Calculus of Constructions](http://www.pps.univ-paris-diderot.fr/~miquel/publis/tlca01.pdf)
Barras and Bernardo. [he Implicit Calculus of Constructions as a Programming Language with Dependent Types](http://www.lix.polytechnique.fr/~bernardo/writings/barras-bernardo-icc-fossacs08.pdf)
Linger and Sheard. [Erasure and Polymorphism in Pure Type Systems](http://web.cecs.pdx.edu/~sheard/papers/FossacsErasure08.pdf)
Frank Pfenning. [Intensionality, extensionality, and proof irrelevance in modal type theory](http://www.cs.cmu.edu/~fp/papers/lics01.pdf)
