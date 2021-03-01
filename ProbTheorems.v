From research Require Import Utils.
From research Require Import ProbAxioms.

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