From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  OperatorDefinitions OperatorProperties NormEquivalence TensorDefinitions
  SecondChaosDefinitions SecondChaosAlgebra SymmetricDefinitions SymmetricBasis
  SymmetricDivergence.
Open Scope R_scope.

(* Port of the inner module GoeParseval of theories/InterpolationProofs.v
   (also copied in GoeProofs.v and JointProofs.v) from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original used nothing from Coquelicot directly. Its only Coquelicot
   content came through matrix n, matrix_entry, coordinate_sum, trace_pair,
   the second chaos and the symmetric basis. Their ports keep the same names,
   arguments and values, so the import of Coquelicot is dropped and the
   statements below are the text of the original.

   This file loads no MathComp module, so (a <= n)%nat is Stdlib's Peano
   order le, as in the original. The ports of SymmetricBasis and
   SecondChaosAlgebra write the same order as (a <= n)%coq_nat, which is the
   same term. The arithmetic, sqrt, the literals, Nat.eqb and Nat.ltb are
   Stdlib's, as before.

   The proofs are the original ones, unchanged: the lemmas they use keep
   their statements in the ports, as the same terms. *)

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
