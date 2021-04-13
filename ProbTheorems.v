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
  type_equiv (Prob (A * B)) (prod (Prob A) (Prob B)).
  
Definition cond (A B : Type) (a : Prob A) : Type :=
  sigT (fun (p : Prob (A * B)) => (fst (split_prob A B p) = a)).
  
(* Why does Prob (A * B) -> sum a * Prob (B | a)
Prob (B | a) = exists an x : Prob (A * B) constructed with a

x : Prob(A * B) -> a : Prob A (split prob, left projection)
To get cond, we need an x, but we already have it

Prove that the projection of x to Prob A = a : Prob A

Now we need a second function

Once we have f and g, h should be equal to one of them
Then we need to prove that the two functions satisfy the equivalence
*)
Theorem f_thm :
  forall (A B : Type), (Prob (A * B)) -> (sigT (fun (a : Prob A) => cond A B a)).
Proof.
  intros A B p.
  apply existT with (x := fst (split_prob A B p)).
  unfold cond.
  apply existT with (x := p).
  reflexivity.
Qed.

Check f_thm.

Print f_thm.

Definition f (A B : Type) (p : Prob (A * B)) :
  {a : Prob A & cond A B a}
  := existT (fun a : Prob A => cond A B a) (fst (split_prob A B p))
  (existT
     (fun p0 : Prob (A * B) =>
      fst (split_prob A B p0) = fst (split_prob A B p)) p eq_refl).

Theorem g_thm :
  forall (A B : Type), (sigT (fun (a : Prob A) => cond A B a)) -> Prob (A * B).
Proof.
  intros A B p.
  destruct p as [a c].
  destruct c.
  apply x.
Qed.

Check g_thm.

Print g_thm.

Definition g (A B : Type) (p : {a : Prob A & cond A B a}) : (Prob (A * B))
  := let (a, c) := p in let (x, _) := c in x.

(*
Definition f (A B : Type) (p : Prob (A * B)) : (sigT (fun (a : Prob A) => cond A B a))
  := .
*)

(*
Theorem f_of_g :
  forall (A B : Type) (p : Prob (A * B)), g A B (f A B p) = p.
Proof.
  intros A B p.

Check existT.
*)

(* P(A * B) = sum (a * P(B | a) *)
Theorem pair_cond_equivalence :
  forall (A B : Type),
    type_equiv (Prob (A * B)) (sigT (fun (a : Prob A) => cond A B a)).
Proof.
  intros.
  unfold type_equiv.
  apply (existT _ (f A B)).
  apply pair.
    - apply existT with (x := g A B).
      unfold homotopy_ind. unfold homotopy. unfold id.
      intros a.
      unfold f.
      reflexivity.
    - apply existT with (x := g A B).
      unfold homotopy_ind. unfold homotopy. unfold id.
      intros aXp.
      destruct aXp as [x c].
      destruct c as [p0 e].
      unfold g.
      unfold f.
      simpl.
      
      
  apply (pair (existT _ (g A B)) (existT _ (g A B))).
  apply (pair (existT with (x := g A B)).
  
Definition f (A B : Type) (Prob A * B) : Type :=
  


  
  
  
  
  
  