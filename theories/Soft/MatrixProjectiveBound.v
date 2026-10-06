From Stdlib Require Import Reals List Lia Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Matrix.Definitions Matrix.OperatorDefinitions Matrix.OperatorNorm
  Matrix.OperatorNormProperties Tensor.Definitions Tensor.GibbsCumulantAtoms
  Tensor.ProjectiveSum Soft.MatrixDefinitions Soft.MatrixScorePerturbation.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* A low-influence bound on the third-order terms of the soft minimax of a
   family of matrices (Soft.MatrixDefinitions). The coefficients
   y z i * B s inherit symmetry and operator norm bounds from B s
   (soft_matrix_coefficients_symmetric,
   soft_matrix_coefficients_operator_bound). If every y z is a unit vector
   on I with coordinates at most theta / sqrt (INR (S n)) in absolute
   value, and every B s is symmetric with operator norm at most k, then the
   projective operator norms (Tensor.Definitions) of the terms
   soft_matrix_third of the blocks i of I are finite, and their sum is at
   most 10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt (INR (S n))
   (soft_matrix_projective_sum_bound). *)

Theorem soft_matrix_coefficients_symmetric n y B S :
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  forall i z s, In s S -> symmetric_matrix n (soft_matrix_coefficients n y B i z s).
Proof.
  intros HB i z s Hs; apply matrix_scale_symmetric; apply HB; exact Hs.
Qed.

Theorem soft_matrix_coefficients_operator_bound n y B S k :
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  forall i z s, In s S ->
    matrix_operator_norm n (soft_matrix_coefficients n y B i z s) <= k * Rabs (y z i).
Proof.
  intros HB i z s Hs; unfold soft_matrix_coefficients; rewrite matrix_operator_norm_scale.
  rewrite (Rmult_comm k); apply Rmult_le_compat_l; [apply Rabs_pos|apply HB; exact Hs].
Qed.

(* The low-influence scale theta / sqrt (INR (S n)) uses the matrix
   dimension S n, as in the paper. The list I indexes the matrix blocks,
   independently of n. *)
Theorem soft_matrix_projective_sum_bound n beta gamma y B I Y S (A : nat -> matrix n) theta k :
  0 < beta -> 0 < gamma -> 0 <= k -> 0 < theta -> Y <> [] -> S <> [] ->
  (forall z, In z Y -> euclidean_norm (y z) I = 1) ->
  (forall z i, In z Y -> In i I -> Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  (forall i, In i I ->
    let N := projective_operator_norm (soft_matrix_third n beta gamma y B I Y S A i) in
    N = EFin (fine N) /\ 0 <= fine N) /\
  finite_sum (fun i => fine (projective_operator_norm (soft_matrix_third n beta gamma y B I Y S A i))) I <=
    10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt (INR (Datatypes.S n)).
Proof.
  intros Hb Hg Hk Htheta HY HS Hunit Hcap Hsym HB; unfold soft_matrix_third.
  apply (matrix_nested_projective_sum_low_influence n beta gamma (soft_matrix_scores n y B I A)
    (soft_matrix_coefficients n y B) y I Y S (Datatypes.S n) theta k); try assumption.
  - lia.
  - intros i z s Hi Hz Hs; exact (soft_matrix_coefficients_symmetric n y B S Hsym i z s Hs).
  - intros i z s Hi Hz Hs; exact (soft_matrix_coefficients_operator_bound n y B S k HB i z s Hs).
Qed.
