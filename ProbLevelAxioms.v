Inductive ProbLevel (X : Type) (level : nat) : Type :=
  | absolute_evid (x : X)
  | prob_evid (p : ProbLevel X (level + 1)).

(* Create a ProbLevel with absolute evidence *)
Check absolute_evid nat 2 1.

(* Create a ProbLevel using probabilistic evidence from 1 level higher *)
Check prob_evid nat 2 (absolute_evid nat 3 1).

Axiom prob_level_abs_imp :
  forall (n : nat) (A : Type) (B: (ProbLevel A n) -> Type)
  (f : forall (a : A), B (absolute_evid A n a)),
  forall (p : ProbLevel A n), (ProbLevel (B p) n).

Axiom prob_level_evid_imp :
  forall (m n : nat) (A : Type) (B: (ProbLevel A m) -> Type)
  (f : forall (p : ProbLevel A (m + 1)), ProbLevel (B (prob_evid A m p)) (n + 1)),
  forall (p : ProbLevel A m), (ProbLevel (B p) n).

Axiom prob_level_abs_comp :
  forall (n : nat) (A : Type) (B: (ProbLevel A n) -> Type)
  (f : forall (a : A), B (absolute_evid A n a)),
  forall (a : A), prob_level_abs_imp n A B f (absolute_evid A n a)
  = absolute_evid (B (absolute_evid A n a)) n (f a).

Axiom prob_level_evid_comp :
  forall (m n : nat) (A : Type) (B: (ProbLevel A m) -> Type)
  (f : forall (p2 : ProbLevel A (m + 1)), ProbLevel (B (prob_evid A m p2)) (n + 1)),
  forall (p : ProbLevel A (m + 1)),
  prob_level_evid_imp m n A B f (prob_evid A m p)
  = prob_evid (B (prob_evid A m p)) n (f p).

Definition prob_level_abs_imp_independent (A B : Type) (f : A -> B) (n : nat)
  := (prob_level_abs_imp n A (fun (_ : ProbLevel A n) => B) f).
  
Definition prob_level_evid_imp_independent (A B : Type) (m n : nat)
  (f : (ProbLevel A (m + 1)) -> (ProbLevel B (n + 1)))
  := prob_level_evid_imp m n A (fun (_ : ProbLevel A m) => B) f.

Definition prob_level_abs_comp_independent (A B : Type) (f : A -> B) (n : nat) (a : A)
  := prob_level_abs_comp n A (fun (_ : ProbLevel A n) => B) f.

Definition prob_level_evid_comp_independent (A B : Type) (m n : nat)
  (p : ProbLevel A (m + 1)) (f : (ProbLevel A (m + 1)) -> (ProbLevel B (n + 1)))
  := prob_level_evid_comp m n A (fun (_ : ProbLevel A m) => B) f.
  
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

Axiom prob_level_ind :
  forall (A : Type),
  ((forall (n : nat), (ProbLevel A n)) -> A).

Axiom prob_level_ind_comp :
  forall (A : Type) (f : forall (n : nat), ProbLevel A n),
  (forall (m : nat), absolute_evid A m (prob_level_ind A f) = f m).

Axiom continuum_hypothesis :
  forall (A : Type),
  (forall (a : A), prob_level_ind A (fun (n : nat) => absolute_evid A n a) = a).