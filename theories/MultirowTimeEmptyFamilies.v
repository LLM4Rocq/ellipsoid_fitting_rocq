From Stdlib Require Import Reals List Lra.
From Stdlib Require Import Logic.FunctionalExtensionality.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions SoftDefinitions GibbsDefinitions SoftMatrixDefinitions
  LowerDefinitions RowArrayDefinitions RowObservableDefinitions RowTimeDefinitions.
Import ListNotations.
Open Scope R_scope.

(* The soft minimax and its first derivative when one of the index families
   Y and S is empty, the cases that the theorems of RowTimeCalculus exclude
   by Y <> [] and S <> []. Since Stdlib's ln 0 is 0, an empty soft maximum
   is 0, so the block value lower_block_phi does not depend on the array and
   gaussian_array_value is constant in time. Every Gibbs average over an
   empty family is 0, so lower_block_first and the row velocities vanish. *)

Lemma multirow_time_ln_0 : Rpower.ln 0 = 0.
Proof. unfold Rpower.ln; destruct (Rlt_dec _ _) as [H|_]; [exact (False_ind _ (Rlt_irrefl _ H))|reflexivity]. Qed.

Lemma multirow_time_finite_sum_ext (f g : nat -> R) (I : list nat) :
  (forall i : nat, f i = g i) -> finite_sum f I = finite_sum g I.
Proof. intros H; induction I as [|i I IH]; simpl; [reflexivity|rewrite H IH; reflexivity]. Qed.

Lemma multirow_time_finite_sum_0 (I : list nat) : finite_sum (fun _ : nat => 0) I = 0.
Proof. induction I as [|i I IH]; simpl; [reflexivity|rewrite IH; lra]. Qed.

Lemma multirow_time_soft_max_nil gamma (f : nat -> R) : soft_max gamma f [] = 0.
Proof. unfold soft_max; simpl; rewrite multirow_time_ln_0; unfold Rdiv; apply Rmult_0_l. Qed.

(* Empty outer family Y: the value is 0 and the derivative is 0. *)
Lemma multirow_time_phi_Y_nil n m beta gamma y B S (A : block_array n m) :
  lower_block_phi n m beta gamma y B [] S A = 0.
Proof.
  unfold lower_block_phi, soft_matrix_phi, soft_minimax, soft_min.
  rewrite multirow_time_soft_max_nil; lra.
Qed.

Lemma multirow_time_first_Y_nil n m beta gamma y B S (A U : block_array n m) :
  lower_block_first n m beta gamma y B [] S A U = 0.
Proof. reflexivity. Qed.

(* Empty inner family S: the value does not depend on the array, and the derivative is 0. *)
Lemma multirow_time_soft_minimax_S_nil beta gamma (H : nat -> nat -> R) (Y : list nat) :
  soft_minimax beta gamma H Y [] = soft_min beta (fun _ : nat => 0) Y.
Proof.
  unfold soft_minimax; f_equal; apply functional_extensionality; intros z.
  apply multirow_time_soft_max_nil.
Qed.

Lemma multirow_time_phi_S_nil n m beta gamma y B Y (A : block_array n m) :
  lower_block_phi n m beta gamma y B Y [] A = soft_min beta (fun _ : nat => 0) Y.
Proof. unfold lower_block_phi, soft_matrix_phi; apply multirow_time_soft_minimax_S_nil. Qed.

Lemma multirow_time_first_S_nil n m beta gamma y B Y (A U : block_array n m) :
  lower_block_first n m beta gamma y B Y [] A U = 0.
Proof.
  unfold lower_block_first, lower_first, gibbs_average.
  transitivity (finite_sum (fun _ : nat => 0) Y); [|apply multirow_time_finite_sum_0].
  apply multirow_time_finite_sum_ext; intros i.
  unfold lower_inner_first, gibbs_average; simpl; apply Rmult_0_r.
Qed.

(* The row velocities and their sum vanish in both empty cases. *)
Lemma multirow_time_row_velocity_Y_nil n m beta gamma y B S t i (xs : list R) :
  gaussian_row_velocity n m beta gamma y B [] S t i xs = 0.
Proof.
  unfold gaussian_row_velocity; rewrite !multirow_time_first_Y_nil.
  unfold Rdiv; rewrite !Rmult_0_l; lra.
Qed.

Lemma multirow_time_row_velocity_S_nil n m beta gamma y B Y t i (xs : list R) :
  gaussian_row_velocity n m beta gamma y B Y [] t i xs = 0.
Proof.
  unfold gaussian_row_velocity; rewrite !multirow_time_first_S_nil.
  unfold Rdiv; rewrite !Rmult_0_l; lra.
Qed.

Lemma multirow_time_velocity_sum_Y_nil n m beta gamma y B S t (xs : list R) (L : list nat) :
  finite_sum (fun i => gaussian_row_velocity n m beta gamma y B [] S t i xs) L = 0.
Proof.
  transitivity (finite_sum (fun _ : nat => 0) L); [|apply multirow_time_finite_sum_0].
  apply multirow_time_finite_sum_ext; intros i; apply multirow_time_row_velocity_Y_nil.
Qed.

Lemma multirow_time_velocity_sum_S_nil n m beta gamma y B Y t (xs : list R) (L : list nat) :
  finite_sum (fun i => gaussian_row_velocity n m beta gamma y B Y [] t i xs) L = 0.
Proof.
  transitivity (finite_sum (fun _ : nat => 0) L); [|apply multirow_time_finite_sum_0].
  apply multirow_time_finite_sum_ext; intros i; apply multirow_time_row_velocity_S_nil.
Qed.

(* A real function that is constant on R has derivative 0 at every point. *)
Lemma multirow_time_is_derive_const (f : R -> R) (c t : R) :
  (forall u : R, f u = c) -> @is_derive R R^o R^o t 1 f 0.
Proof.
  intros H.
  have -> : f = (fun _ : R => c) by apply functional_extensionality; intros u; exact (H u).
  exact: is_derive_cst.
Qed.

(* The array value along the path is constant in both empty cases. *)
Lemma multirow_time_value_Y_nil n m beta gamma y B S (xs : list R) (u : R) :
  gaussian_array_value n m beta gamma y B [] S u xs = 0.
Proof. unfold gaussian_array_value; apply multirow_time_phi_Y_nil. Qed.

Lemma multirow_time_value_S_nil n m beta gamma y B Y (xs : list R) (u : R) :
  gaussian_array_value n m beta gamma y B Y [] u xs = soft_min beta (fun _ : nat => 0) Y.
Proof. unfold gaussian_array_value; apply multirow_time_phi_S_nil. Qed.
