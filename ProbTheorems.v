Require Import Coq.Init.Specif.
Require Import Setoid.
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
#[universes(template)]
Inductive sigT (A:Type) (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.
*)

Print sigT.

Check sigT.
Check existT.

Check sigT (fun (n : nat) => bool).
Check existT (fun (n : nat) => bool) 2.

Theorem comb_prob_general :
  forall (A : Type) (B : A -> Type),
  sigT (fun (a : A) => Prob (B a)) -> Prob (sigT B).
Proof.
  intros A B H.
  destruct H.
  assert (H2: (B x) -> sigT B).
    - intros b. apply existT in b. apply b.
    - apply (prob_imp_independent (B x) (sigT B) H2). apply p.
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

Definition indep (A B : Type) : Type :=
  (Prob (A * B) = prod (Prob A) (Prob B)).
  
Definition cond (A B : Type) (a : Prob A) : Type :=
  sigT (fun (p : Prob (A * B)) => (fst (split_prob A B p) = a)).

Theorem pair_cond_equivalence :
  forall (A B : Type),
    type_equiv (Prob (A * B)) (sigT (fun (a : Prob A) => cond A B a)).
Proof.
  intros.
  unfold type_equiv.
  existT (fun (p : Prob (A * B)) => (
    existT (fun (pA : (Prob A) => pA))
  ).
  exists (f : Prob (A * B) ->
  {a : Prob A & {p : Prob (A * B) & fst (split_prob A B p) = a}}).
  exists (fun (p : Prob (A * B)) => (fst (split_prob A B p))).


  
  
  
  
  
  