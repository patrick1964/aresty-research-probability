Inductive Prob {X : Type} : Type :=
  | evid (x : X).

Axiom inference : forall A B : Type,
  ((exists a : A, True) -> (exists b : B, True))
  -> (exists b : B, True) -> (exists a : @Prob A, True).