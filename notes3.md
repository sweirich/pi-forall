# Datatypes and Indexed Datatypes

Today we'd like to add datatypes to Pi-Forall. 

Unfortunately, datatypes are both:

* Really important (you see them *everywhere* when working 
  with languages like Coq, Agda, Idris, etc.)
* Really complicated (unlike prior lectures, there are a *lot* of details.)

Unlike the prior two lectures, where we could walk through all of the details
of the specification of the type system, not to mention its implementation, we
won't be able to do that here. There is just too much! My goal is to give you
enough information so that you can pick up the Haskell code and understand
what is going on. 

Even then, realize that the implementation that I'm giving you is not the
complete story! Recall that we're not considering termination. That means that
we can think about eliminating datatypes merely by writing recursive
functions; without having to reason about whether those functions
terminate. Coq and Agda and Idris include a lot of machinery for this
termination analysis, and we won't cover any of it.

We'll work up the general specification of datatypes piece-by-piece,
generalizing from features that we already know to more difficult cases.

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
	 
Void brings up the issue of exhaustiveness in case analysis.

### Nat

Finally natural numbers include a data constructor with an argument. 

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
new structures. These structures won't be all that useful yet, but as we add
parameters and indices to our datatypes, they will be. For example, here's an
example of a datatype declaration where the data constructors have dependent
types.

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
declaration (some parts have been elided compared to `version3`, we're
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

## Eliminating dirt simple datatypes

In your homework assignment, we used case to eliminate boolean types.


----------------------------------------------------------

     not_not_equal : (b : Bool) -> (b = not b) -> Void
     not_not_equal = \b pf. 
          if b then (contra pf) else (contra pf)



- connection between sigma types & indexed types
    { x : Type | { pf : x = Int | ... }}
    
 - show definition of sigma types in Product.pi
 
 - Design issues
     telescopes
     pattern matching
       - indices vs. parameters
       - utter hack when pattern matching datatypes
     induction principle (smaller?)
