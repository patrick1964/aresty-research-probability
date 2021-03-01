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

Inductive Sigma (A : Type) (B : A -> Type) :=
  | element (a : A) (b : (B a)).

(*
TODO (more specific things)
  - split things into different files
    - some functions, like proj_left, should go into a file of utility functions
    - axioms of the system should go into axioms file
    - theorems have their own file (can be split up further later on
    - research Sigma and Pi types (use sig_t in the documentation page
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