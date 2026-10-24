(* S1 assembled from the proved small-shift threshold and infimum bounds.
   No measurable choice or attainment of an optimal matrix is used. *)
From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat.
From EllipsoidUniversality Require Import ShiftedConditionStatement.
From EllipsoidUniversality.Shifted Require Import GaussianCondition.

Theorem shifted_condition_theorem : shifted_condition_statement.
Proof.
split.
- move=>n d m C c eps; split.
  - exact: measurable_gaussian_shift_fit.
  - exact: measurable_gaussian_shift_condition_number.
  - exact: measurable_gaussian_shift_optimal_tail.
- move=>C alpha C1 a0 n m hn hm.
  exact: gaussian_shift_condition_threshold C1 a0 hn hm.
- move=>alpha a0 a4 n m hn hm; split.
  - exact: gaussian_shift_optimal_condition a0 a4 hn hm.
  - exact: gaussian_shift_optimal_tail a0 a4 hn hm.
Qed.
