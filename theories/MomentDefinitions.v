From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions.
Open Scope R_scope.

Definition weighted_average (q : nat -> R) (I : list nat) (f : nat -> R) : R :=
  finite_sum (fun i => q i * f i) I.

Definition finite_probability (q : nat -> R) (I : list nat) : Prop :=
  (forall i, In i I -> 0 <= q i) /\ finite_sum q I = 1.
