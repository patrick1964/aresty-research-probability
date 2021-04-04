Require Import Coq.Init.Specif.

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

Check nat = bool.

Check existT.

Check sigT.

Definition homotopy (A : Type) (P : A -> Type) (f g: forall (a : A), P a): Type
  := forall (a : A), (f a) = (g a).

Definition homotopy_ind (A B : Type) (f g: A -> B): Type
  := homotopy A (fun (a : A) => B) f g.
  
Definition id (A : Type) (a : A) := a.

Check id.

Check forall (a : nat), (fun (a: nat) => bool) a.
Check forall (a : nat), (fun (a: nat) => bool) a.

Definition Pi (A : Type) (P : A -> Type) : Type := forall (a : A), P a.

Check Pi.

Check existT.

(* TODO use existT f such that isequiv f *)
Definition type_equiv (A B : Type) : Type :=
  sigT (fun (f : A -> B) => (
    prod
    (sigT (fun (g : B -> A) => (homotopy_ind B B (fun (b : B) => (f (g b))) (id B))))
    (sigT (fun (h : B -> A) => (homotopy_ind A A (fun (a : A) => (h (f a))) (id A))))
  )).

(*
TODO (more specific things)
    - research Sigma and Pi types (use sig_t in the documentation page
    - try to prove split_prob_general
    - convert theorems at the bottom into levelled versions
*)

(*
Next steps (general)
  - make sure that the axioms are consistent
  - are there any contradictions?
    - step 1: prove that all of the non-induction rules are consistent
    - step 2: prove that adding the induction rules keeps the system consistent
*)