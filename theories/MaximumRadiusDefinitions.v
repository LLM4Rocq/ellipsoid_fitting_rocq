From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import GaussianProductDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Consecutive rows of d scalar Gaussian coordinates in a list of length N*d.
   The empty maximum is 0; all genuine squared row radii are nonnegative. *)
Fixpoint gaussian_maximum_radius (N d : nat) (xs : list R) : R :=
  match N with
  | O => 0
  | S k => Rmax (gaussian_sum_squares (firstn d xs))
      (gaussian_maximum_radius k d (skipn d xs))
  end.

Fixpoint gaussian_radius_exponential_sum (N d : nat) (t : R) (xs : list R) : R :=
  match N with
  | O => 0
  | S k => exp (t * (gaussian_sum_squares (firstn d xs) - INR d)) +
      gaussian_radius_exponential_sum k d t (skipn d xs)
  end.
