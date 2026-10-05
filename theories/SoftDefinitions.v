From Stdlib Require Import Reals List.
Import ListNotations.
Open Scope R_scope.

(* Finite indexed families may contain repeated indices. Their cardinality
   in the logarithmic error is the number of entries, including repeats. *)
Fixpoint finite_sum (f : nat -> R) (I : list nat) : R :=
  match I with [] => 0 | i :: rest => f i + finite_sum f rest end.

Fixpoint finite_max (f : nat -> R) (I : list nat) : R :=
  match I with
  | [] => 0
  | i :: rest =>
      match rest with [] => f i | _ :: _ => Rmax (f i) (finite_max f rest) end
  end.

Definition finite_min (f : nat -> R) (I : list nat) : R :=
  - finite_max (fun i => - f i) I.

Definition soft_max (gamma : R) (f : nat -> R) (I : list nat) : R :=
  ln (finite_sum (fun i => exp (gamma * f i)) I) / gamma.

Definition soft_min (beta : R) (f : nat -> R) (I : list nat) : R :=
  - soft_max beta (fun i => - f i) I.

Definition soft_minimax (beta gamma : R) (H : nat -> nat -> R)
    (Y S : list nat) : R :=
  soft_min beta (fun y => soft_max gamma (H y) S) Y.

Definition finite_minimax (H : nat -> nat -> R) (Y S : list nat) : R :=
  finite_min (fun y => finite_max (H y) S) Y.

Definition squared_norm (y : nat -> R) (I : list nat) : R :=
  finite_sum (fun i => y i ^ 2) I.

Definition euclidean_norm (y : nat -> R) (I : list nat) : R :=
  sqrt (squared_norm y I).

Definition cubic_mass (y : nat -> R) (I : list nat) : R :=
  finite_sum (fun i => Rabs (y i) ^ 3) I.
