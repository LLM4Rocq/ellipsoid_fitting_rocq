From Stdlib Require Import Reals List Lia Lra FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  SoftDefinitions GibbsDefinitions GibbsWeights ThirdDefinitions
  MatrixGibbsDefinitions MatrixSecondDefinitions MatrixThirdDefinitions
  SoftMatrixDefinitions RowSliceDefinitions LowerDefinitions FullThirdDefinitions
  BlockOperatorDefinitions BlockBasis BlockC3Definitions BlockGibbsC3
  TensorGibbs SoftMatrixCalculus RowSlice.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/BlockRowEvaluation.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem of the original keeps its name and its arguments,
   in the same order. No item is added. The statements mention only the
   definitions of the ported modules MatrixDefinitions, LowerDefinitions,
   FullThirdDefinitions, SoftMatrixDefinitions, RowSliceDefinitions,
   MatrixGibbsDefinitions, MatrixSecondDefinitions, MatrixThirdDefinitions,
   BlockOperatorDefinitions and BlockC3Definitions, Stdlib's lists and the
   order on nat. Those ports keep the names, the arguments and the meaning of
   the definitions, so each statement says the same thing as in the
   original. Two changes of notation are forced by loading ssreflect.

   1. Order on indices. With ssreflect loaded, (i <= m)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so the
      hypotheses are written (i <= m)%coq_nat, which is Stdlib's le, as in
      block_entry_inject of BlockBasis and tuple_entry_build of
      MatrixCoordinates.

   2. Lists of indices. With ssreflect loaded, seq is the type of
      MathComp's lists. The original's seq 0 (S m) is Stdlib's list
      function, so it is written List.seq 0 (S m), as in LowerDefinitions.
      The term is the original's.

   The original took three lemmas from the bundle ComparisonProofs, through
   its inner modules TensorGibbs, SoftMatrixCalculus and RowSlice. The port
   imports the ported standalone modules of these names instead:
   trace_pair_left_scale of TensorGibbs, soft_matrix_single_sum of
   SoftMatrixCalculus, and soft_matrix_row_shared_inner and
   soft_matrix_row_shared_scores of RowSlice.

   Proofs. The sum in the proof of block_row_score is written with the match
   that the original's if Nat.eq_dec j i then x else 0 stands for, the form
   of soft_matrix_single_sum in the port of SoftMatrixCalculus. Coquelicot's
   linear_zero on trace_pair_linear becomes MathComp's linear0, since the
   port of MatrixTrace declares trace_pair n B a linear map. Stdlib's
   "rewrite A, B" and "rewrite ... by tac" are written in the forms that
   ssreflect accepts. *)

Lemma block_rows_entry n m (rows : nat -> matrix n) j : (j <= m)%coq_nat ->
  block_entry n m (tuple_build (matrix_NormedModule n) m rows) j = rows j.
Proof. intros Hj; unfold block_entry; apply tuple_entry_build; exact Hj. Qed.

Lemma block_rows_roundtrip n m (A : block_array n m) :
  tuple_build (matrix_NormedModule n) m (block_entry n m A) = A.
Proof.
  apply tuple_ext; intros j Hj.
  rewrite (tuple_entry_build _ _ _ _ Hj); reflexivity.
Qed.

Lemma block_rows_scores n m y B (rows : nat -> matrix n) :
  soft_matrix_scores n y B (List.seq 0 (S m))
    (block_entry n m (tuple_build (matrix_NormedModule n) m rows)) =
  soft_matrix_scores n y B (List.seq 0 (S m)) rows.
Proof.
  apply functional_extensionality; intros z; apply functional_extensionality; intros s.
  unfold soft_matrix_scores; apply gibbs_sum_ext; intros j Hj.
  apply in_seq in Hj; rewrite (block_rows_entry n m rows j ltac:(lia)); reflexivity.
Qed.

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

Lemma block_rows_phi n m beta gamma y B Y S (rows : nat -> matrix n) :
  lower_block_phi n m beta gamma y B Y S (tuple_build (matrix_NormedModule n) m rows) =
  soft_matrix_phi n beta gamma y B (List.seq 0 (Datatypes.S m)) Y S rows.
Proof. unfold lower_block_phi, soft_matrix_phi; rewrite block_rows_scores; reflexivity. Qed.

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

Theorem block_row_second n m beta gamma y B Y S (A : block_array n m) i (U V : matrix n) :
  (i <= m)%coq_nat ->
  lower_block_second n m beta gamma y B Y S A (block_inject n m i U) (block_inject n m i V) =
  matrix_nested_second_derivative n beta gamma
    (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (block_entry n m A) i)
    (soft_matrix_coefficients n y B i) Y S (block_entry n m A i) U V.
Proof.
  intro Hi; unfold lower_block_second, lower_second, matrix_nested_second_derivative.
  rewrite (block_row_inner_value n m gamma y B S A i Hi).
  rewrite (block_row_inner_covariance n m gamma y B S A i U V Hi)
    (block_row_inner_first n m gamma y B S A i U Hi)
    (block_row_inner_first n m gamma y B S A i V Hi); reflexivity.
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

Theorem block_row_second_from_array n m beta gamma y B Y S (rows : nat -> matrix n) i U V :
  (i <= m)%coq_nat ->
  lower_block_second n m beta gamma y B Y S (tuple_build (matrix_NormedModule n) m rows)
    (block_inject n m i U) (block_inject n m i V) =
  matrix_nested_second_derivative n beta gamma (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) rows i)
    (soft_matrix_coefficients n y B i) Y S (rows i) U V.
Proof.
  intro Hi; rewrite (block_row_second n m beta gamma y B Y S _ i U V Hi).
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

Theorem full_block_row_operator_evaluations n m beta gamma y B Y S :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] ->
  exists (D1 : block_array n m -> block_first_operator_space n m)
    (D2 : block_array n m -> block_second_operator_space n m)
    (D3 : block_array n m -> block_third_operator_space n m),
  block_operator_C3 n m (lower_block_phi n m beta gamma y B Y S) D1 D2 D3 /\
  (forall A U V W,
    block_first_evaluation n m (D1 A) U = lower_block_first n m beta gamma y B Y S A U /\
    block_second_evaluation n m (D2 A) U V = lower_block_second n m beta gamma y B Y S A U V /\
    block_third_evaluation n m (D3 A) U V W = lower_block_third n m beta gamma y B Y S A U V W) /\
  (forall A i U V W, (i<=m)%coq_nat ->
    block_first_evaluation n m (D1 A) (block_inject n m i U) =
      matrix_nested_derivative n beta gamma
        (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (block_entry n m A) i)
        (soft_matrix_coefficients n y B i) Y S (block_entry n m A i) U /\
    block_second_evaluation n m (D2 A) (block_inject n m i U) (block_inject n m i V) =
      matrix_nested_second_derivative n beta gamma
        (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (block_entry n m A) i)
        (soft_matrix_coefficients n y B i) Y S (block_entry n m A i) U V /\
    block_third_evaluation n m (D3 A) (block_inject n m i U) (block_inject n m i V) (block_inject n m i W) =
      matrix_nested_third_derivative n beta gamma
        (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (block_entry n m A) i)
        (soft_matrix_coefficients n y B i) Y S (block_entry n m A i) U V W).
Proof.
  intros Hb Hg HY HS.
  destruct (full_block_soft_minimax_C3 n m beta gamma y B Y S Hb Hg HY HS)
    as [D1 [D2 [D3 [HC HE]]]].
  exists D1,D2,D3; split; [exact HC|]; split; [exact HE|].
  intros A i U V W Hi.
  destruct (HE A (block_inject n m i U) (block_inject n m i V) (block_inject n m i W))
    as [H1 [H2 H3]].
  rewrite H1 H2 H3; split; [apply block_row_first; exact Hi|].
  split; [apply block_row_second|apply block_row_third]; exact Hi.
Qed.
