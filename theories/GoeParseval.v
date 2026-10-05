From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  OperatorDefinitions OperatorProperties NormEquivalence TensorDefinitions
  SecondChaosDefinitions SecondChaosAlgebra SymmetricDefinitions SymmetricBasis
  SymmetricDivergence.
Open Scope R_scope.

(* Parseval's identity in the orthonormal basis of the symmetric matrices
   made of the diagonal units e_a e_a^T (symmetric_diagonal_basis) and of
   the matrices (e_a e_b^T + e_b e_a^T) / sqrt 2 for a < b
   (symmetric_offdiagonal_basis). goe_symmetric_parseval: for symmetric U
   and V, the sum over this basis of trace_pair n W U * trace_pair n W V is
   trace_pair n U V. *)

Theorem goe_symmetric_parseval n (U V : matrix n) :
  symmetric_matrix n U -> symmetric_matrix n V ->
  coordinate_sum n (fun a =>
    trace_pair n (symmetric_diagonal_basis n a) U *
    trace_pair n (symmetric_diagonal_basis n a) V) +
  coordinate_sum n (fun a => coordinate_sum n (fun b =>
    if Nat.ltb a b then
      trace_pair n (symmetric_offdiagonal_basis n a b) U *
      trace_pair n (symmetric_offdiagonal_basis n a b) V
    else 0)) = trace_pair n U V.
Proof.
  intros HU HV; unfold trace_pair at 5.
  rewrite (symmetric_ordered_sum_partition n
    (fun a b => matrix_entry n U a b * matrix_entry n V b a)).
  apply f_equal2.
  - apply coordinate_sum_ext; intros a Ha.
    rewrite !symmetric_diagonal_trace by assumption; reflexivity.
  - apply coordinate_sum_ext; intros a Ha; apply coordinate_sum_ext; intros b Hb.
    destruct (Nat.ltb a b); [|reflexivity].
    rewrite !symmetric_offdiagonal_trace by assumption.
    rewrite (HU b a Hb Ha), (HV b a Hb Ha).
    replace (/ sqrt 2 * (matrix_entry n U a b + matrix_entry n U a b) *
      (/ sqrt 2 * (matrix_entry n V a b + matrix_entry n V a b))) with
      ((/ sqrt 2 * / sqrt 2) * (4 * matrix_entry n U a b * matrix_entry n V a b)) by ring.
    rewrite symmetric_inv_sqrt2_square; field.
Qed.
