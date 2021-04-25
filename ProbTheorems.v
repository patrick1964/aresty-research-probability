Require Import Coq.Init.Specif.
Require Import Setoid.
From research Require Import Utils.
From research Require Import ProbAxioms.

Theorem split_prob_thm :
  forall (A B :Type), Prob (A * B) -> ((Prob A) * (Prob B)).
Proof.
  intros A B H.
  split.
    - apply (prob_imp_independent (A * B) A (proj_left A B)). apply H.
    - apply (prob_imp_independent (A * B) B (proj_right A B)). apply H. 
Qed.

Definition split_prob (A B : Type) (H : Prob (A * B)) : ((Prob A) * (Prob B))
  := (prob_imp_independent (A * B) A (proj_left A B) H,
      prob_imp_independent (A * B) B (proj_right A B) H).

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
      unfold homotopy_ind. unfold homotopy. unfold id. reflexivity.
    - apply existT with (x := g A B).
      unfold homotopy_ind. unfold homotopy. unfold id.
      intros aXp.
      destruct aXp as [a c].
      simpl.
      destruct c.
      rewrite <- e.
      unfold f.
      reflexivity.
Qed.

Definition marginal_prob (A B : Type) : Type :=
  forall (a : Prob A), type_equiv (cond A B a) (Prob B).

Theorem cond_proj_right_thm : forall (A B : Type) (a : Prob A),
  cond A B a -> Prob B.
Proof.
  intros A B a c.
  destruct c as [x _].
  apply split_prob in x.
  apply proj_right in x.
  apply x.
Qed.

Print cond_proj_right_thm.

Definition cond_proj_right (A B : Type) (a : Prob A) (c : cond A B a) : Prob B :=
  let (x, _) := c in
  let x0 := split_prob A B x in let x1 := proj_right (Prob A) (Prob B) x0 in x1.

Theorem ind_to_pair_thm : forall (A B : Type) (H: marginal_prob A B),
  Prob A * Prob B -> Prob (A * B).
Proof.
  intros A B.
  unfold marginal_prob. unfold type_equiv. unfold homotopy_ind. unfold homotopy.
  unfold id.
  intros m.
  intros p.
  destruct p as [a b].
  assert (H : {f : cond A B a -> Prob B &
    ({h : Prob B -> cond A B a & forall a0 : cond A B a, h (f a0) = a0} *
     {g : Prob B -> cond A B a & forall a0 : Prob B, f (g a0) = a0})%type}).
  - apply m.
  - destruct H. destruct p as [h g]. destruct h as [fh eh].
    apply fh in b.
    destruct b.
    apply x0.
Qed.

Print ind_to_pair_thm.

Definition ind_to_pair (A B : Type)
  (m : forall a : Prob A,
       {f : cond A B a -> Prob B &
       ({h : Prob B -> cond A B a & forall a0 : cond A B a, h (f a0) = a0} *
        {g : Prob B -> cond A B a & forall a0 : Prob B, f (g a0) = a0})%type})
  (p : Prob A * Prob B) :=
  let (a, b) := p in
  let H := m a in
  let (x, p0) := H in
  let (h, _) := p0 in
  let (fh, _) := h in let b0 := fh b in let (x0, _) := b0 in x0.

Theorem marginal_to_ind_thm :
  forall (A B : Type), (marginal_prob A B) -> (indep A B).
Proof.
  intros A B.
  unfold marginal_prob.
  unfold type_equiv. unfold homotopy_ind. unfold homotopy. unfold id.
  intros H.
  unfold indep. unfold type_equiv.
  unfold homotopy_ind. unfold homotopy. unfold id.
  apply existT with (x := split_prob A B).
  apply pair.
  - apply existT with (x := ind_to_pair A B H).
    intros p.
    unfold ind_to_pair.
    simpl.

Theorem ind_to_marginal_thm :
  forall (A B : Type), (indep A B) -> (marginal_prob A B).
Proof.
  intros A B i.
  destruct i.
  unfold marginal_prob.
  intros a.
  unfold type_equiv.
  destruct p as [h g].
  unfold homotopy_ind in h. unfold homotopy in h. unfold id in h.
  unfold homotopy_ind in g. unfold homotopy in g. unfold id in g.
  destruct h as [fh eh].
  destruct g as [fg eg].
  unfold homotopy_ind. unfold homotopy. unfold id.
  apply existT with (x := cond_proj_right A B a).
  apply pair.
  - unfold homotopy_ind. unfold homotopy. unfold id. Abort.
    (*apply existT with (x := fun (b : Prob B) => fh (pair a b)).*)
    
Theorem construct_cond : forall (A B : Type) (a : Prob A) (b : Prob B)
  (x : Prob (A * B) -> Prob A * Prob B)
  (fh : Prob A * Prob B -> Prob (A * B))
  (eh : forall a : Prob (A * B), fh (x a) = a)
  (fg : Prob A * Prob B -> Prob (A * B))
  (eg : forall a : Prob A * Prob B, x (fg a) = a),
  (cond A B a).
Proof.
  intros.
  unfold cond.
  apply existT with (x := fg (pair a b)).
  apply x.
  

    
Definition ind_to_marginal (A B : Type) : Type :=
  

Theorem ind_equivalence :
  forall (A B: Type), type_equiv (indep A B) (marginal_prob A B).
Proof.
  Abort.

  
  
  
  
  
  