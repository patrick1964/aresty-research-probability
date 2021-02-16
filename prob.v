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
(*
Axiom prob_imp :
  forall (A B : Type) (f : A -> B), (Prob A) -> (Prob B).
*)

Axiom prob_imp_dependent_types :
  forall (A : Type) (B : (Prob A) -> Type)
  (f: forall a : A, B (evid A a)),
  forall x : Prob A, Prob (B x).

(*
Axiom prob_comp :
  forall (A B : Type) (f : A -> B) (a: A),
  prob_imp A B f (evid A a) = evid B (f a).
*)

Axiom prob_comp_dependent_types :
  forall (A : Type) (B : (Prob A) -> Type)
  (f: forall a : A, B (evid A a))
  (a : A),
  prob_imp_dependent_types A B f (evid A a) = evid (B (evid A a)) (f a).

(* TODO think about whether this is necessary? *)
Axiom prob_function_extensionality :
  forall (A : Type) (B : Type) (f1 : Prob A -> B) (f2 : Prob A -> B),
  (forall (a : A), (f1 (evid A a)) = (f2 (evid A a))) -> f1 = f2.

(* Goal: When B is a non-dependent type,
the two elimination rules are the same.
*)
(*
Theorem prob_imp_equivalence : 
  forall (A B : Type) (f : A -> B),
  prob_imp A B f =
  prob_imp_dependent_types A (fun (_ : Prob A) => B)
  (fun (a : A) => (f a)).
Proof.
  intros A B f.
  apply prob_function_extensionality.
  intros a.
  rewrite prob_comp_dependent_types.
  rewrite prob_comp.
  reflexivity.
Qed.
*)

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

(* Two Elimination Rules *)
(*
Axiom prob_level_imp_same_level :
  forall (A B : Type) (f : A -> B) (n : nat),
  (ProbLevel A n) -> (ProbLevel B n).
  
Axiom prob_level_imp_different_levels :
  forall (A B : Type) (m n : nat),
  ((ProbLevel A (m + 1)) -> (ProbLevel B (n + 1))) ->
  ((ProbLevel A m) -> (ProbLevel B n)).
*)

Axiom prob_level_imp_same_level :
  forall (n : nat) (A : Type) (B: (ProbLevel A n) -> Type)
  (f : forall (a : A), B (absolute_evid A n a)),
  forall (p : ProbLevel A n), (ProbLevel (B p) n).

Axiom prob_level_imp_different_levels :
  forall (m n : nat) (A : Type) (B: (ProbLevel A m) -> Type)
  (f : forall (p : ProbLevel A (m + 1)), ProbLevel (B (prob_evid A m p)) (n + 1)),
  forall (p : ProbLevel A m), (ProbLevel (B p) n).

(* Two Computation Rules *)
(*
Axiom prob_level_comp_from_absolute :
  forall (A B : Type) (f : A -> B) (n : nat)
  (a: A),
  prob_level_imp_same_level A B f n (absolute_evid A n a)
  = absolute_evid B n (f a).

Axiom prob_level_comp_from_level :
  forall (A B : Type) (m n : nat) (p: ProbLevel A (m + 1))
  (f : (ProbLevel A (m + 1)) -> (ProbLevel B (n + 1))),
  prob_level_imp_different_levels A B m n f (prob_evid A m p)
  = prob_evid B n (f p).
*)

Axiom prob_level_comp_from_absolute :
  forall (n : nat) (A : Type) (B: (ProbLevel A n) -> Type)
  (f : forall (a : A), B (absolute_evid A n a)),
  forall (a : A), prob_level_imp_same_level n A B f (absolute_evid A n a)
  = absolute_evid (B (absolute_evid A n a)) n (f a).

Axiom prob_level_comp_from_level :
  forall (m n : nat) (A : Type) (B: (ProbLevel A m) -> Type)
  (f : forall (p2 : ProbLevel A (m + 1)), ProbLevel (B (prob_evid A m p2)) (n + 1)),
  forall (p : ProbLevel A (m + 1)),
  prob_level_imp_different_levels m n A B f (prob_evid A m p)
  = prob_evid (B (prob_evid A m p)) n (f p).


(* TODO do we need both parts of the /\? *)
(*
Axiom prob_level_function_extensionality :
  forall (A : Type) (B : Type) (n : nat) (f1 : ProbLevel A n -> B)
    (f2 : ProbLevel A n -> B),
  ((forall (a : A), (f1 (absolute_evid A n a)) = (f2 (absolute_evid A n a)))
  /\
  (forall (p : ProbLevel A (n + 1)), (f1 (prob_evid A n p)) = (f2 (prob_evid A n p))))
  -> f1 = f2.
*)

Axiom prob_level_induction :
  forall (A : Type),
  ((forall (n : nat), (ProbLevel A n)) -> A).

Axiom prob_level_induction_computation_rule :
  forall (A : Type) (f : forall (n : nat), ProbLevel A n),
  (forall (m : nat), absolute_evid A m (prob_level_induction A f) = f m).

Axiom continuum_hypothesis :
  forall (A : Type),
  (forall (a : A), prob_level_induction A (fun (n : nat) => absolute_evid A n a) = a).

Theorem placeholder :
  forall (A : Type),
  (forall (n : nat), ProbLevel A n) = A.
Proof.
  Abort.

(*
TODO (more specific things)
  - clean everything up (change names if any are unclear)
  - try to finish the placeholder theorem (if possible)
  - make dependent types theorem in terms of dependent types
  - a few other theorems I wrote down
*)

(*
Next steps (general)
  - make sure that the axioms are consistent
  - are there any contradictions?
    - step 1: prove that all of the non-induction rules are consistent
    - step 2: prove that adding the induction rules keeps the system consistent
*)

