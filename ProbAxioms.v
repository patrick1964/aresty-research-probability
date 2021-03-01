(*
Formation Rule
A : Type
________
Prob(A) : Type

Introduction Rule
a : A => evid(a) : Prob(A)

Elimination Rule
a : A => f(a) : B
__________________
x : Prob(A) => imp_f(x) : Prob(B)

Computation Rule
imp_f(evid_A(a)) = evid_B(f(a))
*)

(* Formation Rule, Introduction Rule *)
Inductive Prob (X : Type): Type :=
  | evid (x : X).

(*
Theorem imp_as_theorem :
  forall (A B : Type) (f : A -> B), (Prob A) -> (Prob B).
Proof.
  intros A B f probA.
  destruct probA.
  apply f in x.
  apply evid in x.
  apply x.
Qed.
*)

(* Using match with Prob is implicitly assuming that we used evid as the
   constructor - don't do that. *)

Print Prob_rect.
Print Prob_ind.
Print Prob_rec.
Print Prob_sind.

Check evid nat 2.

Axiom prob_imp :
  forall (A : Type) (B : (Prob A) -> Type)
  (f: forall a : A, B (evid A a)),
  forall x : Prob A, Prob (B x).

Axiom prob_comp :
  forall (A : Type) (B : (Prob A) -> Type)
  (f: forall a : A, B (evid A a))
  (a : A),
  prob_imp A B f (evid A a) = evid (B (evid A a)) (f a).

Definition prob_imp_independent (A B : Type) (f : A -> B)
  := prob_imp A (fun (_ : Prob A) => B) f.

Definition prob_comp_indpendent (A B : Type) (f : A -> B) (a : A)
  := prob_comp A (fun (_ : Prob A) => B) f a.