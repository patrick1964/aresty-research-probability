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

(* TODO *)
Theorem placeholder :
  forall (A : Type),
  (forall (n : nat), ProbLevel A n) = A.
Proof.
  Abort.
  
Check prob_imp.

(* TODO move to separate file *)
Theorem proj_left : forall (A B : Type), A * B -> A.
Proof.
  intros A B H.
  destruct H.
  apply a.
Qed.

Theorem proj_right : forall (A B : Type), A * B -> B.
Proof.
  intros A B H.
  destruct H.
  apply b.
Qed.

Theorem inj_left : forall (A B : Type), A -> A + B.
Proof.
  intros A B H.
  left. apply H.
Qed.

Theorem inj_right : forall (A B : Type), B -> A + B.
Proof.
  intros A B H.
  right. apply H.
Qed.

Theorem split_prob :
  forall (A B :Type), Prob (A * B) -> ((Prob A) * (Prob B)).
Proof.
  intros A B H.
  split.
    - apply (prob_imp_independent (A * B) A (proj_left A B)). apply H.
    - apply (prob_imp_independent (A * B) B (proj_right A B)). apply H. 
Qed.

Theorem comb_prob :
  forall (A B : Type), ((Prob A) + (Prob B)) -> Prob (A + B).
Proof.
  intros A B H.
  destruct H.
    - apply (prob_imp_independent A (A + B) (inj_left A B)). apply p. 
    - apply (prob_imp_independent B (A + B) (inj_right A B)). apply p.
Qed. 

Theorem prob_pair_to_union :
  forall (A B : Type), ((Prob A) * (Prob B)) -> ((Prob A) + (Prob B)).
Proof.
  intros.
  destruct X as [pA pB].
  left.
  apply pA.
Qed.

Theorem split_prob_general :
  forall (A : Type) (B : A -> Type),
  Prob (forall (a : A), B a) -> forall (a : A), Prob (B a).
Proof.
  intros A B H a.
  - assert (H2: (forall (a' : A), B a') -> (B a)).
    * intros f. apply (f a).
    * apply (prob_imp_independent (forall a : A, B a) (B a) H2).
      apply H.
Qed.

Inductive Sigma (A : Type) (B : A -> Type) :=
  | element (a : A) (b : (B a)).

(*
(* TODO exists requires its argument to be a Prop, not just any Type. *)
Theorem comb_prob_general :
  forall (A : Type) (B : A -> Type),
  (Sigma (a : A) (Prob (B a)). -> (Prob (exists (a : A) (b : (B a)), True))
Proof.
  intros.
  exists.
  Abort.
*)

Theorem comb_prob_general :
  forall (A : Type) (B : A -> Type),
  (exists (a : A) (b : Prob (B a)), True) -> (Prob (exists (a : A) (b : (B a)), True)).
Proof.
  intros.
  exists.
  Abort.


(*
TODO (more specific things)
  - split things into different files
    - some functions, like proj_left, should go into a file of utility functions
    - axioms of the system should go into axioms file
    - theorems have their own file (can be split up further later on
    - research Sigma and Pi types
    - try to prove split_prob_general
    - convert theorems at the bottom into levelled versions
  - abstract
  - 
*)

(*
Next steps (general)
  - make sure that the axioms are consistent
  - are there any contradictions?
    - step 1: prove that all of the non-induction rules are consistent
    - step 2: prove that adding the induction rules keeps the system consistent
*)

