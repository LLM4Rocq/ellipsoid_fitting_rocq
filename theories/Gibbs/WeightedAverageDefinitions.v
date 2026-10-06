From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Soft.Definitions.
Open Scope R_scope.

(* Weights on a finite list of indices. weighted_average q I f is the sum of
   the q i * f i over i in I, and finite_probability q I says that the
   weights q i, i in I, are nonnegative and sum to 1. *)

Definition weighted_average (q : nat -> R) (I : list nat) (f : nat -> R) : R :=
  finite_sum (fun i => q i * f i) I.

Definition finite_probability (q : nat -> R) (I : list nat) : Prop :=
  (forall i, In i I -> 0 <= q i) /\ finite_sum q I = 1.
