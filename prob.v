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
Axiom prob_imp :
  forall (A B : Type) (f : A -> B), (Prob A) -> (Prob B).

Axiom prob_imp_dependent_types :
  forall (A : Type) (B : (Prob A) -> Type)
  (f: forall a : A, Prob (B (evid A a))),
  forall x : Prob A, Prob (B x).

Check prob_imp nat bool (fun (n : nat) => true).

Check (fun (n: nat) => 2) 5.

Check bool : Type.

Check (fun (p : Prob nat) => bool : Type).

Check prob_imp_dependent_types nat (fun (p : Prob nat) => bool)
      (fun (n : nat) => evid bool true).  

Check prob_imp nat bool (fun (n: nat) => true) (evid nat 1).

Axiom prob_comp :
  forall (A B : Type) (f : A -> B) (a: A),
  prob_imp A B f (evid A a) = evid B (f a).

Axiom prob_comp_dependent_types :
  forall (A : Type) (a : A) (B : (Prob A) -> Type)
  (f: forall a : A, Prob (B (evid A a))) (x : Prob A),
  prob_imp_dependent_types A B f = Prob (B x).

(* Goal: When B is a non-dependent type,
the two elimination rules are the same.
*)
Theorem prob_imp_equivalence : 
  forall (A B : Type) (a : A) (f : A -> B),
  (prob_imp A B f) (evid A a) =
  prob_imp_dependent_types A (fun (_ : Prob A) => B)
  (fun (a : A) => evid B (f a)) (evid A a).
Proof.
  intros A B a f.
  rewrite prob_comp.
  simpl.
 
  
  
