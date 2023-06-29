
Print bool_rect.

(* 
bool_rect = 
fun (P : bool -> Type) (f : P true) (f0 : P false) (b : bool) => if b as b0 return (P b0) then f else f0
     : forall P : bool -> Type, P true -> P false -> forall b : bool, P b
*)

Section MyEq.

Polymorphic Inductive myeq (A :Type)(a:A) : A -> Type :=
  | myrefl : myeq A a a.

Check myeq_rect.

Lemma my_k : forall (A:Type) (x:A) (p : myeq A x x), myeq (myeq A x x) p (myrefl A x).
Proof.
  intros.
  pose (h := myeq_rect).
  specialize h with (y := x) (m := p).
  specialize h with (P := fun a p0 => myeq (myeq A x a) p0 p0). simpl in h.

Polymorphic Inductive myeq : forall (A :Type)(a:A), A -> Type :=
  | myrefl : forall A a, myeq A a a.

Check myeq_rect.

(*
myeq_rect
     : forall (a : A) (P : forall a0 : A, myeq A a a0 -> Type), P a (myrefl A a) -> forall (y : A) (m : myeq A a y), P y m
*)

Lemma my_k : forall (A:Type) (x:A) (p : myeq A x x), myeq (myeq A x x) p (myrefl A x).
Proof.
  intros.
  pose (h := myeq_rect).
  
  specialize h with (m := p).
  specialize (h (fun A x y p0 => myeq (myeq A x y) p0 (myrefl A x))).
  (* goal is 

    myeq (myeq A x x) p (myrefl A x) 

    P (y : A) (m : myeq A x y)  will be instantiated by x and p

    fun y m => myeq (myeq A x y) m m

*)
  specialize (h (fun y m => myeq (myeq A x y) m m)). simpl in h.
  specialize (h (myrefl (myeq A x x) (myrefl A x))).
  specialize (h x p).

  specialize (h (fun a0 e => myeq (myeq A x x) p (myrefl A x))). simpl in h.
  eapply h.
  eapply myeq_rect with (P := fun (a0 : A) (p0 : myeq A a0 a0) => myeq _ p (myrefl A x)).

k : [A:Type] -> [x:A] -> (p : x = x) -> (p = Refl)
k = \ [A][x] p . 
  subst Refl by p




Check eq_rect.

(* 
eq_rect
     : forall (A : Type) (x : A) (P : A -> Type), P x -> forall y : A, x = y -> P y
*)



Definition sym : forall A (x y : A), x = y -> y = x :=

   fun (A : Type) (x y : A) (H : x = y) => 
     match H in (_ = y0) return (y0 = x) with
     | eq_refl => eq_refl
     end.

Definition trans :=
fun (A : Type) (x y z : A) (H : x = y) (H0 : y = z) => 
  match H0 in (_ = y0) return (x = y0) with
  | eq_refl => H
  end.




Definition uip : forall A (x y : A) (p : x = y) (q :x = y),  p = q.
Proof.
  intros.
Search eq eq_refl.
  match q in (_ = y0) return (p = q) with 
  | eq_refl => 
