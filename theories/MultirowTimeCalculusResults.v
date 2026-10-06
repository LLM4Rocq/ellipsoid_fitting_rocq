(* Time derivatives along the interpolation path of block arrays, for
   fixed coordinates xs and 0 < t < 1. paper_multirow_time_calculus_results:
   the block array gaussian_row_array n m t xs has derivative
   gaussian_array_velocity n m t xs in t; the array value
   gaussian_array_value has derivative lower_block_first of the array in
   the direction of the velocity, which is the sum over the rows of
   gaussian_row_velocity. When Y or S is empty, the value is constant in t
   and every derivative term is 0 (MultirowTimeEmptyFamilies); otherwise
   the clauses are theorems of RowTimeCalculus. *)
From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions SoftDefinitions LowerDefinitions
  RowArrayDefinitions RowObservableDefinitions TimeDefinitions RowTimeDefinitions.
From EllipsoidFitting Require Import MultirowTimeEmptyFamilies RowTimeCalculus.
Import ListNotations.
Open Scope R_scope.

Theorem paper_multirow_time_calculus_results :
  forall (n m : nat) (beta gamma : R) (y : nat -> nat -> R)
    (B : nat -> matrix n) (Y S : list nat) (t : R) (xs : list R),
  0 < beta -> 0 < gamma -> 0 < t < 1 ->
  @is_derive R R^o (block_NormedModule n m) t 1
    (fun u : R => gaussian_row_array n m u xs : block_NormedModule n m)
    (gaussian_array_velocity n m t xs : block_NormedModule n m) /\
  @is_derive R R^o R^o t 1
    (fun u : R => gaussian_array_value n m beta gamma y B Y S u xs)
    (lower_block_first n m beta gamma y B Y S
      (gaussian_row_array n m t xs) (gaussian_array_velocity n m t xs)) /\
  lower_block_first n m beta gamma y B Y S
      (gaussian_row_array n m t xs) (gaussian_array_velocity n m t xs) =
    finite_sum (fun i => gaussian_row_velocity n m beta gamma y B Y S t i xs)
      (List.seq 0 (Datatypes.S m)) /\
  @is_derive R R^o R^o t 1
    (fun u : R => gaussian_array_value n m beta gamma y B Y S u xs)
    (finite_sum (fun i => gaussian_row_velocity n m beta gamma y B Y S t i xs)
      (List.seq 0 (Datatypes.S m))).
Proof.
  intros n m beta gamma y B Y S t xs Hbeta Hgamma Ht.
  destruct Y as [|z Y'].
  { split; [exact (RowTimeCalculus.gaussian_array_time_derivative n m t xs Ht)|].
    split.
    { rewrite multirow_time_first_Y_nil.
      apply (multirow_time_is_derive_const _ 0); intros u; apply multirow_time_value_Y_nil. }
    split.
    { rewrite multirow_time_first_Y_nil multirow_time_velocity_sum_Y_nil; reflexivity. }
    rewrite multirow_time_velocity_sum_Y_nil.
    apply (multirow_time_is_derive_const _ 0); intros u; apply multirow_time_value_Y_nil. }
  destruct S as [|s S'].
  { split; [exact (RowTimeCalculus.gaussian_array_time_derivative n m t xs Ht)|].
    split.
    { rewrite multirow_time_first_S_nil.
      apply (multirow_time_is_derive_const _ (soft_min beta (fun _ : nat => 0) (z :: Y')));
        intros u; apply multirow_time_value_S_nil. }
    split.
    { rewrite multirow_time_first_S_nil multirow_time_velocity_sum_S_nil; reflexivity. }
    rewrite multirow_time_velocity_sum_S_nil.
    apply (multirow_time_is_derive_const _ (soft_min beta (fun _ : nat => 0) (z :: Y')));
      intros u; apply multirow_time_value_S_nil. }
  have HY : z :: Y' <> [] by discriminate.
  have HS : s :: S' <> [] by discriminate.
  split; [exact (RowTimeCalculus.gaussian_array_time_derivative n m t xs Ht)|].
  split; [exact (RowTimeCalculus.gaussian_array_value_time_derivative n m beta gamma y B _ _ t xs Hbeta Hgamma HY HS Ht)|].
  split; [exact (RowTimeCalculus.gaussian_array_velocity_row_sum n m beta gamma y B _ _ t xs Hbeta Hgamma HY HS)|].
  exact (RowTimeCalculus.gaussian_array_value_row_derivative n m beta gamma y B _ _ t xs Hbeta Hgamma HY HS Ht).
Qed.
