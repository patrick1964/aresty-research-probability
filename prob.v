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

(* Old Elimination Rule
(* Is this needed, or is the computation rule enough? *)
Axiom elimination_rule :
  forall (A B : Type) (a : A) (f : A -> B),
  (forall x : Prob A, (exists impf : (Prob A) -> (Prob B), True)).
*)

(* Equivalent to elimination rule *)
Axiom prob_imp :
  forall (A B : Type) (f : A -> B), (Prob A) -> (Prob B).

Check prob_imp nat bool (fun (n: nat) => true) (evid nat 1).

Axiom prob_comp :
  forall (A B : Type) (f : A -> B) (a: A),
  prob_imp A B f (evid A a) = evid B (f a).

(* Old computation rule
(* Should the forall a be before the impf part? *)
Axiom computation_rule :
  forall (A B : Type) (a : A) (f : A -> B),
  exists (impf : (Prob A) -> (Prob B)), (impf (evid A a)) = (evid B (f a)).
*)
  
  
