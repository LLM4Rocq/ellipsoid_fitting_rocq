From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions.
Import ListNotations.
Open Scope R_scope.

Definition gaussian_last_marginal (F : list R -> R) (xs : list R) : R :=
  gaussian_expectation (fun t => F (xs ++ [t])).

Definition gaussian_suffix_marginal (n : nat) (F : list R -> R)
    (xs : list R) : R :=
  gaussian_iterated_expectation n (fun ys => F (xs ++ ys)).
