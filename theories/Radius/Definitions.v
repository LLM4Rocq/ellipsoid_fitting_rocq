From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Gaussian.IteratedExpectationDefinitions.
Import ListNotations.
Open Scope R_scope.

(* A list of length N * d holds N consecutive rows of d Gaussian
   coordinates. gaussian_maximum_radius N d xs is the largest squared norm
   of a row (0 when N = 0; squared norms are nonnegative), and
   gaussian_radius_exponential_sum N d t xs is the sum over the rows of
   exp (t * (squared norm - d)). *)
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
