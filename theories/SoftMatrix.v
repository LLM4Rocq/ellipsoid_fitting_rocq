From Stdlib Require Import Reals List Lia Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema MatrixDefinitions
  OperatorDefinitions OperatorBounds OperatorProperties TensorDefinitions TensorGibbs
  TensorSum SoftMatrixDefinitions SoftMatrixCalculus.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/SoftMatrix.v from Coquelicot to MathComp-Analysis.

   Every theorem of the original keeps its name and its arguments, in the
   same order. No lemma is added. soft_matrix_coefficients_symmetric,
   soft_matrix_coefficients_operator_bound, soft_matrix_inner_bounds,
   soft_matrix_outer_bounds and soft_matrix_minimax_bounds keep the text of
   the original, except that ln is written Rpower.ln (see below). The two
   other statements change form in the ways of the ports of TensorSum and
   SoftMatrixCalculus, which they apply, and of the restated challenge
   ellipsoid_soft_matrix in analysis/challenges.

   1. Extended reals. In soft_matrix_projective_sum_bound and
      soft_matrix_deterministic_lemma, Coquelicot's Finite r and real x on
      Rbar become MathComp's EFin r (r%:E) and fine x on \bar R, as in the
      ports of TensorDefinitions and TensorSum. projective_operator_norm is
      the infimum of the same set of costs in both libraries, and
      N = EFin (fine N) says, as N = Finite (real N) did, that N is a real
      number. So the statements say the same thing as before.

   2. Frechet derivatives. In soft_matrix_deterministic_lemma, Coquelicot's
      filterdiff f (locally (matrix_zero n)) l becomes
      is_diff (matrix_zero n) f l of MathComp-Analysis, as in
      soft_matrix_coordinate_derivatives of the port of SoftMatrixCalculus:
      f is differentiable at the zero matrix and its differential is l, a
      linear and continuous map. The real-valued maps are typed into R^o,
      the normed module view of R, which is R by definition. On matrix n the
      norm is the Frobenius norm of MatrixDefinitions, as in Coquelicot.

   Stdlib's logarithm is written Rpower.ln, the constant that the bare ln of
   the original denotes. This module does not import MathComp's exp, so a
   bare ln would also be Stdlib's; the full name keeps the statements
   unambiguous for importers that do load exp. The arithmetic, sqrt, INR,
   Rabs and length are Stdlib's, as before.

   In the proofs, (1 <= S n)%nat of matrix_nested_projective_sum_low_influence
   is (1 <= S n)%coq_nat, Stdlib's le, in the port of TensorSum, and lia
   proves it as before. Stdlib's "apply A, B" is written as two steps. *)

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

Theorem soft_matrix_inner_bounds n gamma y B I S (A : nat -> matrix n) z :
  0 < gamma -> S <> [] ->
  finite_max (soft_matrix_scores n y B I A z) S <= soft_matrix_inner n gamma y B I S A z /\
  soft_matrix_inner n gamma y B I S A z <=
    finite_max (soft_matrix_scores n y B I A z) S + Rpower.ln (INR (length S)) / gamma.
Proof. intros Hg HS; apply soft_max_bounds; assumption. Qed.

Theorem soft_matrix_outer_bounds n beta gamma y B I Y S (A : nat -> matrix n) :
  0 < beta -> Y <> [] ->
  finite_min (soft_matrix_inner n gamma y B I S A) Y - Rpower.ln (INR (length Y)) / beta <=
    soft_matrix_phi n beta gamma y B I Y S A /\
  soft_matrix_phi n beta gamma y B I Y S A <=
    finite_min (soft_matrix_inner n gamma y B I S A) Y.
Proof. intros Hb HY; apply soft_min_bounds; assumption. Qed.

Theorem soft_matrix_minimax_bounds n beta gamma y B I Y S (A : nat -> matrix n) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  finite_minimax (soft_matrix_scores n y B I A) Y S - Rpower.ln (INR (length Y)) / beta <=
    soft_matrix_phi n beta gamma y B I Y S A /\
  soft_matrix_phi n beta gamma y B I Y S A <=
    finite_minimax (soft_matrix_scores n y B I A) Y S + Rpower.ln (INR (length S)) / gamma.
Proof. intros Hb Hg HY HS; apply soft_minimax_bounds; assumption. Qed.

(* The low-influence scale uses the matrix dimension S n, as in the paper.
   The coordinate list I independently indexes the N matrix blocks. *)
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

(* The deterministic finite soft-extremum lemma at every block array A:
   two log-sum-exp sandwiches, actual evaluated coordinate derivatives,
   and the summed projective estimate with an explicit constant 10.
   Operator-valued C3 regularity is not part of this statement. *)
Theorem soft_matrix_deterministic_lemma n beta gamma y B I Y S (A : nat -> matrix n) theta k :
  0 < beta -> 0 < gamma -> 0 <= k -> 0 < theta -> Y <> [] -> S <> [] -> NoDup I ->
  (forall z, In z Y -> euclidean_norm (y z) I = 1) ->
  (forall z i, In z Y -> In i I -> Rabs (y z i) <= theta / sqrt (INR (Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  (forall z, finite_max (soft_matrix_scores n y B I A z) S <= soft_matrix_inner n gamma y B I S A z /\
    soft_matrix_inner n gamma y B I S A z <=
      finite_max (soft_matrix_scores n y B I A z) S + Rpower.ln (INR (length S)) / gamma) /\
  (finite_min (soft_matrix_inner n gamma y B I S A) Y - Rpower.ln (INR (length Y)) / beta <=
    soft_matrix_phi n beta gamma y B I Y S A /\
    soft_matrix_phi n beta gamma y B I Y S A <= finite_min (soft_matrix_inner n gamma y B I S A) Y) /\
  (forall i, In i I ->
    is_diff (matrix_zero n)
      ((fun M => soft_matrix_phi n beta gamma y B I Y S (soft_matrix_block_add n A i M))
        : matrix n -> R^o)
      (soft_matrix_first n beta gamma y B I Y S A i) /\
    forall U : matrix n,
    is_diff (matrix_zero n)
      ((fun M => soft_matrix_first n beta gamma y B I Y S (soft_matrix_block_add n A i M) i U)
        : matrix n -> R^o)
      (soft_matrix_second n beta gamma y B I Y S A i U) /\
    forall V : matrix n,
    is_diff (matrix_zero n)
      ((fun M => soft_matrix_second n beta gamma y B I Y S (soft_matrix_block_add n A i M) i U V)
        : matrix n -> R^o)
      (soft_matrix_third n beta gamma y B I Y S A i U V)) /\
  (forall i, In i I ->
    let N := projective_operator_norm (soft_matrix_third n beta gamma y B I Y S A i) in
    N = EFin (fine N) /\ 0 <= fine N) /\
  finite_sum (fun i => fine (projective_operator_norm (soft_matrix_third n beta gamma y B I Y S A i))) I <=
    10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt (INR (Datatypes.S n)).
Proof.
  intros Hb Hg Hk Htheta HY HS HD Hunit Hcap Hsym HB; split.
  - intros z; apply soft_matrix_inner_bounds; assumption.
  - split.
    + apply soft_matrix_outer_bounds; assumption.
    + split.
      * intros i Hi; apply soft_matrix_coordinate_derivatives; assumption.
      * apply soft_matrix_projective_sum_bound; assumption.
Qed.
