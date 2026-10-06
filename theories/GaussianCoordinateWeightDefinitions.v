From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import GaussianDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Polynomial weights on coordinates. gaussian_coordinate_weight p x is
   (1 + |x|) ^ p, gaussian_coordinate_product_weight p xs is the product of
   these weights over the entries of xs, and
   gaussian_coordinate_weight_moment p is the Gaussian expectation of the
   weight. finite_polynomial_bound d C p F says that C >= 0 and that
   |F xs| <= C times the product weight of xs on lists of length d. *)

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
