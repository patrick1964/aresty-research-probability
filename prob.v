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

Axiom prob_imp_dependent_types :
  forall (A : Type) (B : (Prob A) -> Type)
  (f: forall a : A, Prob (B (evid A a))),
  forall x : Prob A, Prob (B x).

Check prob_imp nat bool (fun (n : nat) => true).

Check (fun (n: nat) => 2) 5.

Check bool : Type.

Check (fun (p : Prob nat) => bool : Type).

Check prob_imp_dependent_types nat (fun (p : Prob nat) => bool)
      (fun (n : nat) => evid bool true).  

Check prob_imp nat bool (fun (n: nat) => true) (evid nat 1).

Check forall x : Prob nat, Prob (bool).

Axiom prob_comp :
  forall (A B : Type) (f : A -> B) (a: A),
  prob_imp A B f (evid A a) = evid B (f a).

Axiom prob_comp_dependent_types :
  forall (A : Type) (a : A) (B : (Prob A) -> Type)
  (f: forall a : A, Prob (B (evid A a))) (x : Prob A) (b : B x),
  prob_imp_dependent_types A B f x = evid (B x) b.

(* Goal: When B is a non-dependent type,
the two elimination rules are the same.
*)
Theorem prob_imp_equivalence : 
  forall (A B : Type) (a : A) (f : A -> B),
  (prob_imp A B f) (evid A a) =
  prob_imp_dependent_types A (fun (_ : Prob A) => B)
  (fun (a : A) => evid B (f a)) (evid A a).
Proof.
  intros A B a f.
  rewrite prob_comp.
  rewrite prob_comp_dependent_types with (b:=f a).
    - reflexivity.
    - apply a.
Qed.

(*
Does this violate injectivity?
*)
Inductive ProbLevel (X : Type) (level : nat) : Type :=
  | absolute_evid (x : X)
  | prob_evid (p : ProbLevel X (level + 1)).

(* Create a ProbLevel with absolute evidence *)
Check absolute_evid nat 2 1.

(* Create a ProbLevel using probabilistic evidence from 1 level higher *)
Check prob_evid nat 2 (absolute_evid nat 3 1).

Axiom prob_level_imp :
  forall (A B : Type) (f : A -> B) (n : nat),
  (ProbLevel A n) -> (ProbLevel B n).

(*
Going from A to ProbLevel A to ProbLevel n B is the same as
going from A to B to ProbLevel n B.
*)
Axiom prob_level_comp_from_absolute :
  forall (A B : Type) (f : A -> B) (a: A) (n : nat),
  prob_level_imp A B f n (absolute_evid A n a)
  = absolute_evid B n (f a).

(*
Going from Prob A (n + 1) to Prob A n to Prob B n is the same as
going from Prob A (n + 1) to Prob B (n + 1) to Prob B n.
*)
Axiom prob_level_comp_from_level :
  forall (A B : Type) (f : A -> B) (n : nat) (p: ProbLevel A (n + 1)),
  prob_level_imp A B f n (prob_evid A n p)
  = prob_evid B n (prob_level_imp A B f (n + 1) p).

