From Stdlib Require Import Reals List Lia Lra FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.Trace Soft.Definitions Gibbs.Definitions
  Gibbs.Weights Gibbs.CumulantDefinitions Gibbs.MatrixDefinitions
  Gibbs.MatrixSecondDerivativeDefinitions
  Gibbs.MatrixThirdDerivativeDefinitions Soft.MatrixDefinitions
  Soft.BlockSliceDefinitions Soft.MinimaxDerivativeDefinitions
  Soft.LowerThirdDefinitions Matrix.BlockInjection Matrix.BlockBasis
  Tensor.GibbsCumulantAtoms Soft.MatrixScorePerturbation Soft.BlockSlice.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Derivatives of the block soft minimax in the directions of one block.
   Fix a block index i <= m. The block scores are affine in the block A_i:
   the other blocks give the offset soft_matrix_row_offset (the scores with
   block i replaced by 0), and block i enters through the coefficient
   matrices soft_matrix_coefficients n y B i z s = y z i * B s
   (block_row_score). So the derivatives of the block soft minimax at A in
   directions block_inject n m i U, supported on block i, are the
   derivatives of the matrix nested soft minimax at the matrix A_i, with
   these offsets and coefficients: block_row_first for the first derivative
   and block_row_third for the third. The lemmas block_row_inner_value,
   block_row_inner_first, block_row_inner_covariance and
   block_row_inner_cumulant match the inner terms first.
   block_row_first_from_array and block_row_third_from_array state the same
   for the block array whose blocks are rows 0, ..., rows m. *)

Lemma block_rows_entry n m (rows : nat -> matrix n) j : (j <= m)%coq_nat ->
  block_entry n m (tuple_build (matrix_NormedModule n) m rows) j = rows j.
Proof. intros Hj; unfold block_entry; apply tuple_entry_build; exact Hj. Qed.

Lemma block_rows_offset n m y B (rows : nat -> matrix n) i :
  soft_matrix_row_offset n y B (List.seq 0 (S m))
    (block_entry n m (tuple_build (matrix_NormedModule n) m rows)) i =
  soft_matrix_row_offset n y B (List.seq 0 (S m)) rows i.
Proof.
  apply functional_extensionality; intros z; apply functional_extensionality; intros s.
  unfold soft_matrix_row_offset, soft_matrix_scores; apply gibbs_sum_ext; intros j Hj.
  unfold soft_matrix_block_replace; destruct (Nat.eq_dec j i); [reflexivity|].
  apply in_seq in Hj; rewrite (block_rows_entry n m rows j ltac:(lia)); reflexivity.
Qed.

Lemma block_row_score n m y B i (U : matrix n) : (i <= m)%coq_nat ->
  forall z s, lower_block_scores n m y B z s (block_inject n m i U) =
    trace_pair n (soft_matrix_coefficients n y B i z s) U.
Proof.
  intros Hi z s; unfold lower_block_scores, soft_matrix_scores, soft_matrix_coefficients.
  rewrite trace_pair_left_scale.
  transitivity (finite_sum (fun j => match Nat.eq_dec j i with
      left _ => y z i * trace_pair n (B s) U | right _ => 0 end)
    (List.seq 0 (S m))).
  - apply gibbs_sum_ext; intros j Hj.
    apply in_seq in Hj.
    rewrite (block_entry_inject n m i j U ltac:(lia)).
    destruct (Nat.eq_dec j i) as [Heq|Hne].
    + subst j; rewrite Nat.eqb_refl; reflexivity.
    + assert (Heqb : Nat.eqb j i = false) by (apply Nat.eqb_neq; exact Hne).
      rewrite Heqb linear0.
      change (y z j * 0 = 0); ring.
  - apply soft_matrix_single_sum.
    + apply seq_NoDup.
    + apply in_seq; lia.
Qed.

Lemma block_row_score_function n m y B i (U : matrix n) : (i <= m)%coq_nat ->
  forall z, (fun s => lower_block_scores n m y B z s (block_inject n m i U)) =
    (fun s => trace_pair n (soft_matrix_coefficients n y B i z s) U).
Proof.
  intros Hi z; apply functional_extensionality; intros s.
  apply block_row_score; exact Hi.
Qed.

Lemma block_row_inner_value n m gamma y B S (A : block_array n m) i :
  (i<=m)%coq_nat ->
  lower_inner_value gamma (lower_block_scores n m y B) S A =
  matrix_inner_values n gamma
    (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (block_entry n m A) i)
    (soft_matrix_coefficients n y B i) S (block_entry n m A i).
Proof.
  intro Hi; symmetry.
  rewrite (soft_matrix_row_shared_inner n gamma y B (List.seq 0 (Datatypes.S m)) S
    (block_entry n m A) i (seq_NoDup _ _) ltac:(apply in_seq; lia)).
  reflexivity.
Qed.

Lemma block_row_inner_first n m gamma y B S (A : block_array n m) i U :
  (i<=m)%coq_nat ->
  lower_inner_first gamma (lower_block_scores n m y B) S A (block_inject n m i U) =
  matrix_inner_derivative n gamma
    (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (block_entry n m A) i)
    (soft_matrix_coefficients n y B i) S (block_entry n m A i) U.
Proof.
  intro Hi; apply functional_extensionality; intros z.
  unfold lower_inner_first, matrix_inner_derivative.
  rewrite (soft_matrix_row_shared_scores n y B (List.seq 0 (Datatypes.S m))
    (block_entry n m A) i (seq_NoDup _ _) ltac:(apply in_seq; lia)).
  rewrite (block_row_score_function n m y B i U Hi); reflexivity.
Qed.

Lemma block_row_inner_covariance n m gamma y B S (A : block_array n m) i U V :
  (i<=m)%coq_nat ->
  lower_inner_covariance gamma (lower_block_scores n m y B) S A
    (block_inject n m i U) (block_inject n m i V) =
  matrix_inner_covariance n gamma
    (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (block_entry n m A) i)
    (soft_matrix_coefficients n y B i) S (block_entry n m A i) U V.
Proof.
  intro Hi; apply functional_extensionality; intros z.
  unfold lower_inner_covariance, matrix_inner_covariance.
  rewrite (soft_matrix_row_shared_scores n y B (List.seq 0 (Datatypes.S m))
    (block_entry n m A) i (seq_NoDup _ _) ltac:(apply in_seq; lia)).
  rewrite (block_row_score_function n m y B i U Hi)
    (block_row_score_function n m y B i V Hi); reflexivity.
Qed.

Lemma block_row_inner_cumulant n m gamma y B S (A : block_array n m) i U V W :
  (i<=m)%coq_nat ->
  lower_inner_cumulant gamma (lower_block_scores n m y B) S A
    (block_inject n m i U) (block_inject n m i V) (block_inject n m i W) =
  matrix_inner_cumulant n gamma
    (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (block_entry n m A) i)
    (soft_matrix_coefficients n y B i) S (block_entry n m A i) U V W.
Proof.
  intro Hi; apply functional_extensionality; intros z.
  unfold lower_inner_cumulant, matrix_inner_cumulant.
  rewrite (soft_matrix_row_shared_scores n y B (List.seq 0 (Datatypes.S m))
    (block_entry n m A) i (seq_NoDup _ _) ltac:(apply in_seq; lia)).
  rewrite (block_row_score_function n m y B i U Hi)
    (block_row_score_function n m y B i V Hi)
    (block_row_score_function n m y B i W Hi); reflexivity.
Qed.

Theorem block_row_first n m beta gamma y B Y S (A : block_array n m) i (U : matrix n) :
  (i <= m)%coq_nat ->
  lower_block_first n m beta gamma y B Y S A (block_inject n m i U) =
  matrix_nested_derivative n beta gamma
    (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (block_entry n m A) i)
    (soft_matrix_coefficients n y B i) Y S (block_entry n m A i) U.
Proof.
  intro Hi; unfold lower_block_first, lower_first, matrix_nested_derivative.
  rewrite (block_row_inner_value n m gamma y B S A i Hi).
  rewrite (block_row_inner_first n m gamma y B S A i U Hi); reflexivity.
Qed.

Theorem block_row_third n m beta gamma y B Y S (A : block_array n m) i (U V W : matrix n) :
  (i <= m)%coq_nat ->
  lower_block_third n m beta gamma y B Y S A
    (block_inject n m i U) (block_inject n m i V) (block_inject n m i W) =
  matrix_nested_third_derivative n beta gamma
    (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (block_entry n m A) i)
    (soft_matrix_coefficients n y B i) Y S (block_entry n m A i) U V W.
Proof.
  intro Hi; unfold lower_block_third, lower_third, matrix_nested_third_derivative.
  rewrite (block_row_inner_value n m gamma y B S A i Hi).
  rewrite (block_row_inner_cumulant n m gamma y B S A i U V W Hi)
    (block_row_inner_covariance n m gamma y B S A i U V Hi)
    (block_row_inner_covariance n m gamma y B S A i U W Hi)
    (block_row_inner_covariance n m gamma y B S A i V W Hi)
    (block_row_inner_first n m gamma y B S A i U Hi)
    (block_row_inner_first n m gamma y B S A i V Hi)
    (block_row_inner_first n m gamma y B S A i W Hi); reflexivity.
Qed.

Theorem block_row_first_from_array n m beta gamma y B Y S (rows : nat -> matrix n) i U :
  (i <= m)%coq_nat ->
  lower_block_first n m beta gamma y B Y S (tuple_build (matrix_NormedModule n) m rows)
    (block_inject n m i U) =
  matrix_nested_derivative n beta gamma (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) rows i)
    (soft_matrix_coefficients n y B i) Y S (rows i) U.
Proof.
  intro Hi; rewrite (block_row_first n m beta gamma y B Y S _ i U Hi).
  rewrite block_rows_offset (block_rows_entry n m rows i Hi); reflexivity.
Qed.

Theorem block_row_third_from_array n m beta gamma y B Y S (rows : nat -> matrix n) i U V W :
  (i <= m)%coq_nat ->
  lower_block_third n m beta gamma y B Y S (tuple_build (matrix_NormedModule n) m rows)
    (block_inject n m i U) (block_inject n m i V) (block_inject n m i W) =
  matrix_nested_third_derivative n beta gamma (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) rows i)
    (soft_matrix_coefficients n y B i) Y S (rows i) U V W.
Proof.
  intro Hi; rewrite (block_row_third n m beta gamma y B Y S _ i U V W Hi).
  rewrite block_rows_offset (block_rows_entry n m rows i Hi); reflexivity.
Qed.
