From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import GaussianDefinitions.
Import ListNotations.
Open Scope R_scope.

Definition gaussian_coordinate_weight (p : nat) (x : R) : R :=
  (1 + Rabs x) ^ p.

Fixpoint gaussian_coordinate_product_weight (p : nat) (xs : list R) : R :=
  match xs with
  | [] => 1
  | x :: rest => gaussian_coordinate_weight p x *
      gaussian_coordinate_product_weight p rest
  end.

Definition gaussian_coordinate_weight_moment (p : nat) : R :=
  gaussian_expectation (gaussian_coordinate_weight p).

Definition finite_polynomial_bound (d : nat) (C : R) (p : nat)
    (F : list R -> R) : Prop :=
  0 <= C /\ forall xs, length xs = d ->
    Rabs (F xs) <= C * gaussian_coordinate_product_weight p xs.
