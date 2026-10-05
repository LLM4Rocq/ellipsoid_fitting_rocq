(* Results module of the draft challenge multirow_time_calculus, over the
   MathComp-Analysis port in analysis/. Nothing here is reviewed, solved or
   accepted: the challenge is a draft of the port, and this module is a
   pre-submission proof attempt written on 30 September 2026 by a session
   that did not write the statement.

   The imports before the proof modules are those of
   analysis/challenges/multirow_time_calculus/Challenge.v, in the same order,
   and the statement below is the text of that file, copied unchanged
   (SHA-256 of Challenge.v: e288da017052486ba1c5bb5ee5498324eaace39b5c141a2bce5eb4c830a5150a).

   The proof splits on the index families. When Y or S is empty, the value
   Phi along the path is constant and every derivative term is 0
   (MultirowTimeEmptyFamilies). When both are nonempty, the four clauses are
   the checkpoint theorems gaussian_array_time_derivative,
   gaussian_array_value_time_derivative, gaussian_array_velocity_row_sum and
   gaussian_array_value_row_derivative of RowTimeCalculus, whose hypotheses
   Y <> [] and S <> [] are then available. The first clause is the same
   theorem in all three cases; block_NormedModule n m is
   tuple_NormedModule (matrix_NormedModule n) m by definition. *)
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
