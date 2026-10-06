From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.IteratedExpectationDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Partial Gaussian expectations over the last coordinates of a list.
   gaussian_last_marginal F xs integrates F (xs ++ [t]) over one Gaussian
   coordinate t, and gaussian_suffix_marginal n F xs integrates
   F (xs ++ ys) over n Gaussian coordinates ys. *)

Definition gaussian_last_marginal (F : list R -> R) (xs : list R) : R :=
  gaussian_expectation (fun t => F (xs ++ [t])).

Definition gaussian_suffix_marginal (n : nat) (F : list R -> R)
    (xs : list R) : R :=
  gaussian_iterated_expectation n (fun ys => F (xs ++ ys)).
