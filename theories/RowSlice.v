From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights Cubic
  MatrixDefinitions MatrixGibbsDefinitions MatrixSecondDefinitions
  MatrixThirdDefinitions MatrixThird OperatorDefinitions TensorDefinitions TensorSum
  SoftMatrixDefinitions SoftMatrixCalculus SoftMatrix RowSliceDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* The soft minimax of an array of matrices A as a function of one block
   A i, the other blocks being fixed. soft_matrix_block_replace n A i M
   replaces block i by M. The scores are then affine in M, with offset
   soft_matrix_row_offset (block i set to 0) and coefficients
   soft_matrix_coefficients (soft_matrix_row_scores). So soft_matrix_third,
   the third derivative in block i, is matrix_nested_third_derivative of
   this affine family (soft_matrix_row_third,
   soft_matrix_row_third_at_current).
   soft_matrix_row_projective_sum: if every y z is a unit vector with
   entries at most theta / sqrt (S n) and every B s is symmetric with
   operator norm at most k, the projective norms of these third derivatives
   are finite (N = EFin (fine N)), and their sum over the blocks is at most
   10 k^3 (beta+gamma)^2 theta / sqrt (S n). soft_matrix_row_radial_sum
   weights the blocks by radii at most Rmax. *)

Lemma soft_matrix_block_replace_current n (A : nat -> matrix n) i :
  soft_matrix_block_replace n A i (A i) = A.
Proof.
  apply functional_extensionality; intros j; unfold soft_matrix_block_replace.
  destruct (Nat.eq_dec j i); [subst; reflexivity|reflexivity].
Qed.

Lemma soft_matrix_block_replace_as_add n (A : nat -> matrix n) i M :
  soft_matrix_block_replace n A i M =
    soft_matrix_block_add n (soft_matrix_block_replace n A i (matrix_zero n)) i M.
Proof.
  apply functional_extensionality; intros j.
  unfold soft_matrix_block_replace, soft_matrix_block_add.
  destruct (Nat.eq_dec j i); [|reflexivity].
  unfold matrix_add, matrix_zero; symmetry; exact (@add0r (matrix_NormedModule n) M).
Qed.

Theorem soft_matrix_row_scores n y B I (A : nat -> matrix n) i M :
  NoDup I -> In i I ->
  matrix_affine_scores n (soft_matrix_row_offset n y B I A i)
    (soft_matrix_coefficients n y B i) M =
  soft_matrix_scores n y B I (soft_matrix_block_replace n A i M).
Proof.
  intros HD Hi; rewrite soft_matrix_block_replace_as_add.
  symmetry; apply soft_matrix_scores_perturbation; assumption.
Qed.

Theorem soft_matrix_row_shared_scores n y B I (A : nat -> matrix n) i :
  NoDup I -> In i I ->
  matrix_affine_scores n (soft_matrix_row_offset n y B I A i)
    (soft_matrix_coefficients n y B i) (A i) = soft_matrix_scores n y B I A.
Proof.
  intros HD Hi; rewrite (soft_matrix_row_scores n y B I A i (A i) HD Hi).
  apply f_equal; apply soft_matrix_block_replace_current.
Qed.

Theorem soft_matrix_row_shared_inner n gamma y B I S (A : nat -> matrix n) i :
  NoDup I -> In i I ->
  matrix_inner_values n gamma (soft_matrix_row_offset n y B I A i)
    (soft_matrix_coefficients n y B i) S (A i) = soft_matrix_inner n gamma y B I S A.
Proof.
  intros HD Hi; unfold matrix_inner_values, soft_matrix_inner.
  rewrite (soft_matrix_row_shared_scores n y B I A i HD Hi); reflexivity.
Qed.

Lemma soft_matrix_third_rebase n beta gamma H coeff Y S (M U V W : matrix n) :
  matrix_nested_third_derivative n beta gamma (matrix_affine_scores n H coeff M)
    coeff Y S (matrix_zero n) U V W =
  matrix_nested_third_derivative n beta gamma H coeff Y S M U V W.
Proof.
  unfold matrix_nested_third_derivative, matrix_inner_cumulant,
    matrix_inner_covariance, matrix_inner_derivative, matrix_inner_values.
  rewrite !matrix_affine_scores_at_zero; reflexivity.
Qed.

Theorem soft_matrix_row_third n beta gamma y B I Y S (A : nat -> matrix n) i M U V W :
  NoDup I -> In i I ->
  matrix_nested_third_derivative n beta gamma (soft_matrix_row_offset n y B I A i)
    (soft_matrix_coefficients n y B i) Y S M U V W =
  soft_matrix_third n beta gamma y B I Y S (soft_matrix_block_replace n A i M) i U V W.
Proof.
  intros HD Hi; unfold soft_matrix_third.
  rewrite <- (soft_matrix_row_scores n y B I A i M HD Hi).
  symmetry; apply soft_matrix_third_rebase.
Qed.

Theorem soft_matrix_row_third_at_current n beta gamma y B I Y S
    (A : nat -> matrix n) i :
  NoDup I -> In i I ->
  matrix_nested_third_derivative n beta gamma (soft_matrix_row_offset n y B I A i)
    (soft_matrix_coefficients n y B i) Y S (A i) =
  soft_matrix_third n beta gamma y B I Y S A i.
Proof.
  intros HD Hi; apply functional_extensionality; intros U.
  apply functional_extensionality; intros V; apply functional_extensionality; intros W.
  rewrite (soft_matrix_row_third n beta gamma y B I Y S A i (A i) U V W HD Hi).
  rewrite soft_matrix_block_replace_current; reflexivity.
Qed.

Theorem soft_matrix_row_projective_sum n beta gamma y B I Y S
    (A : nat -> matrix n) theta k :
  0 < beta -> 0 < gamma -> 0 <= k -> 0 < theta -> Y <> [] -> S <> [] -> NoDup I ->
  (forall z, In z Y -> euclidean_norm (y z) I = 1) ->
  (forall z i, In z Y -> In i I -> Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  (forall i, In i I ->
    let N := projective_operator_norm (matrix_nested_third_derivative n beta gamma
      (soft_matrix_row_offset n y B I A i) (soft_matrix_coefficients n y B i) Y S (A i)) in
    N = EFin (fine N) /\ 0 <= fine N) /\
  finite_sum (fun i => fine (projective_operator_norm (matrix_nested_third_derivative n beta gamma
    (soft_matrix_row_offset n y B I A i) (soft_matrix_coefficients n y B i) Y S (A i)))) I <=
    10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt (INR (Datatypes.S n)).
Proof.
  intros Hb Hg Hk Htheta HY HS HD Hunit Hcap Hsym HB.
  destruct (soft_matrix_projective_sum_bound n beta gamma y B I Y S A theta k
    Hb Hg Hk Htheta HY HS Hunit Hcap Hsym HB) as [Hfinite Hsum].
  split.
  - intros i Hi.
    rewrite (soft_matrix_row_third_at_current n beta gamma y B I Y S A i HD Hi).
    exact (Hfinite i Hi).
  - erewrite gibbs_sum_ext; [exact Hsum|].
    intros i Hi; rewrite (soft_matrix_row_third_at_current n beta gamma y B I Y S A i HD Hi).
    reflexivity.
Qed.

Theorem soft_matrix_row_radial_sum n beta gamma y B I Y S
    (A : nat -> matrix n) theta k (radius : nat -> R) Rmax :
  0 < beta -> 0 < gamma -> 0 <= k -> 0 < theta -> Y <> [] -> S <> [] -> NoDup I ->
  (forall z, In z Y -> euclidean_norm (y z) I = 1) ->
  (forall z i, In z Y -> In i I -> Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  0 <= Rmax -> (forall i, In i I -> radius i <= Rmax) ->
  finite_sum (fun i => radius i * fine (projective_operator_norm
    (matrix_nested_third_derivative n beta gamma (soft_matrix_row_offset n y B I A i)
      (soft_matrix_coefficients n y B i) Y S (A i)))) I <=
  Rmax * (10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt (INR (Datatypes.S n))).
Proof.
  intros Hb Hg Hk Htheta HY HS HD Hunit Hcap Hsym HB HR Hr.
  destruct (soft_matrix_row_projective_sum n beta gamma y B I Y S A theta k
    Hb Hg Hk Htheta HY HS HD Hunit Hcap Hsym HB) as [Hfinite Hsum].
  eapply Rle_trans with (finite_sum (fun i => Rmax * fine (projective_operator_norm
    (matrix_nested_third_derivative n beta gamma (soft_matrix_row_offset n y B I A i)
      (soft_matrix_coefficients n y B i) Y S (A i)))) I).
  - apply cubic_sum_le; intros i Hi; apply Rmult_le_compat_r.
    + exact (proj2 (Hfinite i Hi)).
    + apply Hr; exact Hi.
  - rewrite cubic_sum_scale; apply Rmult_le_compat_l; assumption.
Qed.
