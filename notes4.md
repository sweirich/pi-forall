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

In PiForall we have new kind of quantification, called "forall" that marks
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
------------------------
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

What about contra? This marks dead code too. So contra should be erased too.

    n : [x: True = False] -> [A:Type] -> A
    n = \[x][A]. contra x

What about putting it in data structures? We should be able to define
datatypes with "specificational arguments"

- [Fin.pi](soln/test/Fin.pi)
- [Vec.pi](soln/test/Vec.pi)

Note: erase only from data constructor arguments, not when appear as 
arguments to type constructors. (Parameters to type constructors must 
always be relevant.)

Of course, there are many variations of products: 
[Product.pi](soln/test/Product.pi)

## ERASURE and equality
------------------------

We've been alluding to this all week, but now we'll come down to it.  We're
actually *defining* equality over "erased" terms instead of the terms
themselves.  Note how the definition of equate ignores 'eraseable' elements
like type annotations, erasable arguments, etc.

Why?
  - faster comparison: don't have to look at the whole term when comparing for 
    equality. Coq / Adga look at type annotations
  - more expressive: don't have to *prove* that those parts are equal 
    (proof irrelevance!)
  - this gets really crazy with heterogeneous equality
  - and it is sound: see Miquel (ICC), Barras


# What next?
------------

- Termination checking
- Pattern match compilation
- Univalence