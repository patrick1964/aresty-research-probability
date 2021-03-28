From research Require Import ProbLevelAxioms.
From research Require Import Utils.

(* TODO *)
Theorem placeholder :
  forall (A : Type),
  (forall (n : nat), ProbLevel A n) = A.
Proof.
  Abort.

Theorem split_prob_level :
  forall (A B : Type) (n : nat),
  ProbLevel (A * B) n -> ((ProbLevel A n) * (ProbLevel B n)).
Proof.
  intros.
  split.
    - apply (prob_level_abs_imp_independent (A * B) A (proj_left A B) n).
      apply X.
    - apply (prob_level_abs_imp_independent (A * B) B (proj_right A B) n).
      apply X.
Qed.

Theorem comb_prob_level :
  forall (A B : Type) (n : nat),
  ((ProbLevel A n) + (ProbLevel B n)) -> ProbLevel (A + B) n.
Proof.
  intros.
  destruct X.
    - apply (prob_level_abs_imp_independent A (A + B) (inj_left A B)). apply p. 
    - apply (prob_level_abs_imp_independent B (A + B) (inj_right A B)). apply p.
Qed. 

Theorem prob_level_pair_to_union :
  forall (A B : Type) (n : nat),
  ((ProbLevel A n) * (ProbLevel B n)) -> ((ProbLevel A n) + (ProbLevel B n)).
Proof.
  intros.
  destruct X as [pA pB].
  left.
  apply pA.
Qed.

Theorem split_prob_level_general :
  forall (A : Type) (B : A -> Type) (n : nat),
  ProbLevel (forall (a : A), B a) n -> forall (a : A), ProbLevel (B a) n.
Proof.
  intros.
  - assert (H2: (forall (a' : A), B a') -> (B a)).
    * intros f. apply (f a).
    * apply (prob_level_abs_imp_independent (forall a : A, B a) (B a) H2).
      apply X.
Qed.

Theorem comb_prob_level_general :
  forall (A : Type) (B : A -> Type) (n : nat),
  sigT (fun (a : A) => ProbLevel (B a) n) -> ProbLevel (sigT B) n.
Proof.
  intros A B n H.
  destruct H.
  assert (H2: (B x) -> sigT B).
    - intros b. apply existT in b. apply b.
    - apply (prob_level_abs_imp_independent (B x) (sigT B) H2). apply p.
Qed.

Inductive IndepLevelled (A B : Type) : Type :=
  | indep : forall (m : nat),
    (ProbLevel (A * B) m = prod (ProbLevel A m) (ProbLevel B m)) -> IndepLevelled A B.
  
  
  
  
  
  
  
  
  