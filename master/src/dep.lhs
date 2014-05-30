Design issues in dependently-typed languages
============================================

Four 75 minute lectures

Lecture one, getting off the ground
   - Implementing a simple, dependently-typed core language 
     in Haskell. 
   - predicative polymorphism, a-la Agda
   - use Unbound library to deal with variable names & freshness
   - whnf for equality
   - "local" type inference (InferMe) or bidirectionality?
   - no datatypes at first...
   - HOMEWORK: add simple products, booleans, case analysis
     [special typing rules for product type]

Lecture two, datatypes and equality
   - Datatypes and telescopes
   - Pattern-matching and refinement
   - Coq's equality type
   - (on slides?) Intensional vs. Extensional equality
   - HOMEWORK: simple vector code in this languge? copy some 
      simple Agda/Coq assignments

Lecture three, irrelevance, finish up two (maybe cut)
   - irrelevant arguments for functions and datatypes
   - (on slides?) Prop/Set, []s, etc.

Lecture four, beyond
   - unification
   - sat solvers? others?
   - call-by-value languages
   - Nontermination





