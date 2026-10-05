From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import normedtype.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import SoftDefinitions MatrixDefinitions OperatorDefinitions GoeDefinitions TensorDefinitions
  MatrixThirdDefinitions SecondChaosDefinitions SoftMatrixDefinitions RowSliceDefinitions
  LowerDefinitions FullThirdDefinitions BlockOperatorDefinitions BlockRowEvaluation
  RowArrayDefinitions RowObservableDefinitions RowMarginalDefinitions RowRadiusNorm
  MaximumRadiusDefinitions MaximumRadiusRegularity.
From EllipsoidFitting Require Import TensorGibbs TensorNestedRepresentation
  SecondChaosBounds RowSlice Cubic.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/RowRemainderSum.v from Coquelicot to MathComp-Analysis.

   Every lemma and theorem keeps its name and its arguments, in the same
   order. No item is added. The proofs are the original ones, with the
   renamings below.

   Imports. The original imported the bundle ComparisonProofs and opened its
   inner modules TensorGibbs, TensorNestedRepresentation, SecondChaosBounds,
   RowSlice and Cubic. The port imports the standalone ported modules of the
   same names directly, in the same order and after the other imports, so
   that every short name resolves to the same module as before. Cubic is the
   module copied unchanged from theories/Cubic.v, which is identical to the
   inner copy of the bundle.

   Four changes of notation, which keep the meaning of every statement.

   1. Norms. Coquelicot's norm x becomes MathComp's norm, written (`|x|)%R.
      The vectors fst (gaussian_row_pair n i xs) are elements of vector n,
      the nested tuples of MatrixDefinitions, whose products are
      euclidean_product of MatrixEuclideanProduct and keep Coquelicot's
      product norm sqrt (norm (fst x) ^ 2 + norm (snd x) ^ 2), not
      MathComp's max norm (difference 1 of analysis/README.md). So the norm
      is still the Euclidean norm of the S n coordinates, as in the ports of
      SecondChaosBounds and RowRadiusNorm, and the constants 4 and 40 are
      stated against the same norm as in the original.

   2. Extended reals. Coquelicot's real x on Rbar becomes MathComp's fine x
      on \bar R, as in the ports of TensorDefinitions, SecondChaosBounds and
      RowSlice. projective_operator_norm is the infimum of the same set of
      costs in both libraries, and both real and fine send the two infinite
      values to 0, so fine (projective_operator_norm T) is the value that
      real (projective_operator_norm T) was.

   3. seq 0 (S m) is written List.seq 0 (S m). It is Stdlib's list of the
      naturals 0, ..., m, as before; the qualification guards against
      MathComp's type seq in importers that load ssreflect.

   4. The MathComp imports are limited to ssralg, ssrnum, Rstruct,
      normedtype and ereal: the norm on vector n needs the first four, and
      fine the last. None of them opens MathComp's ssreflect, ssrnat or exp
      in this file, so (i<=m)%nat is Stdlib's Peano le and + and * on nat
      are Nat.add and Nat.mul, as in the original; (i<=m)%nat is the
      (i <= m)%coq_nat of the ported BlockRowEvaluation. R_scope is opened
      after the imports, so the arithmetic, ^, Rabs, sqrt and INR are
      Stdlib's, and the proofs keep Stdlib's tactic syntax.

   The definitions the statements use (gaussian_row_remainder,
   gaussian_row_pair, gaussian_row_matrix, soft_matrix_row_offset,
   soft_matrix_coefficients, matrix_nested_third_derivative,
   chaos_contraction, symmetric_matrix, matrix_operator_norm,
   euclidean_norm, finite_sum, gaussian_maximum_radius, row_prefixes,
   goe_vector_index) keep their names, arguments and values in their
   ports. So every statement says the same thing as in the original. *)

Theorem gaussian_row_remainder_slice n m beta gamma y B Y S t i xs :
  (i<=m)%nat ->
  gaussian_row_remainder n m beta gamma y B Y S t i xs =
  chaos_contraction n
    (matrix_nested_third_derivative n beta gamma
      (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (fun j=>gaussian_row_matrix n t j xs) i)
      (soft_matrix_coefficients n y B i) Y S (gaussian_row_matrix n t i xs))
    (fst(gaussian_row_pair n i xs)).
Proof.
  intro Hi; unfold gaussian_row_remainder, gaussian_row_array.
  apply chaos_contraction_ext; intros U V W HU HV HW.
  apply block_row_third_from_array; exact Hi.
Qed.

Theorem gaussian_row_remainder_projective_bound n m beta gamma y B Y S t i xs :
  (i<=m)%nat -> S<>[] -> (forall s, In s S -> symmetric_matrix n (B s)) ->
  Rabs(gaussian_row_remainder n m beta gamma y B Y S t i xs) <=
  4*(`|fst(gaussian_row_pair n i xs)|)%R^2 * fine(projective_operator_norm
    (matrix_nested_third_derivative n beta gamma
      (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (fun j=>gaussian_row_matrix n t j xs) i)
      (soft_matrix_coefficients n y B i) Y S (gaussian_row_matrix n t i xs))).
Proof.
  intros Hi HS Hsym; rewrite gaussian_row_remainder_slice by exact Hi.
  pose proof (nested_third_atoms_represents n beta gamma
    (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (fun j=>gaussian_row_matrix n t j xs) i)
    (soft_matrix_coefficients n y B i) Y S (gaussian_row_matrix n t i xs) HS) as HR.
  assert (HC : forall z s, In z Y -> In s S -> symmetric_matrix n (soft_matrix_coefficients n y B i z s)).
  { intros z s Hz Hs; unfold soft_matrix_coefficients; apply matrix_scale_symmetric, Hsym; exact Hs. }
  specialize (HR HC).
  destruct (chaos_projective_bound n _ _ (fst(gaussian_row_pair n i xs)) HR) as [r [HE [Hpos HB]]].
  rewrite HE; exact HB.
Qed.

Lemma row_finite_sum_abs_le f I : Rabs(finite_sum f I) <= finite_sum (fun i=>Rabs(f i)) I.
Proof.
  induction I as [|i I IH]; simpl; [rewrite Rabs_R0; lra|].
  eapply Rle_trans; [apply Rabs_triang|]; lra.
Qed.

Theorem gaussian_row_remainder_radial_sum n m beta gamma y B Y S t theta k xs Rmax :
  0<beta -> 0<gamma -> 0<=k -> 0<theta -> Y<>[] -> S<>[] ->
  (forall z, In z Y -> euclidean_norm(y z)(List.seq 0 (Datatypes.S m))=1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) -> Rabs(y z i)<=theta/sqrt(INR(Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s)<=k) ->
  0<=Rmax -> (forall i, In i (List.seq 0 (Datatypes.S m)) -> (`|fst(gaussian_row_pair n i xs)|)%R^2<=Rmax) ->
  finite_sum (fun i=>Rabs(gaussian_row_remainder n m beta gamma y B Y S t i xs))
    (List.seq 0 (Datatypes.S m)) <=
  40*k^3*(beta+gamma)^2*theta/sqrt(INR(Datatypes.S n))*Rmax.
Proof.
  intros Hb Hg Hk Htheta HY HS Hy Hcap Hsym HB HR Hr.
  pose proof (soft_matrix_row_radial_sum n beta gamma y B (List.seq 0 (Datatypes.S m)) Y S
    (fun j=>gaussian_row_matrix n t j xs) theta k (fun i=>(`|fst(gaussian_row_pair n i xs)|)%R^2) Rmax
    Hb Hg Hk Htheta HY HS (seq_NoDup _ _) Hy Hcap Hsym HB HR Hr) as Hsum.
  eapply Rle_trans with (finite_sum (fun i=>4*((`|fst(gaussian_row_pair n i xs)|)%R^2*
    fine(projective_operator_norm(matrix_nested_third_derivative n beta gamma
      (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (fun j=>gaussian_row_matrix n t j xs) i)
      (soft_matrix_coefficients n y B i) Y S (gaussian_row_matrix n t i xs))))) (List.seq 0 (Datatypes.S m))).
  - apply cubic_sum_le; intros i Hi.
    rewrite <- Rmult_assoc; apply gaussian_row_remainder_projective_bound; try assumption.
    apply in_seq in Hi; lia.
  - rewrite cubic_sum_scale.
    eapply Rle_trans; [apply Rmult_le_compat_l; [lra|exact Hsum]|].
    right; unfold Rdiv; ring.
Qed.

Theorem gaussian_row_remainder_maximum_sum n m beta gamma y B Y S t theta k xs :
  0<beta -> 0<gamma -> 0<=k -> 0<theta -> Y<>[] -> S<>[] ->
  (forall z, In z Y -> euclidean_norm(y z)(List.seq 0 (Datatypes.S m))=1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) -> Rabs(y z i)<=theta/sqrt(INR(Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s)<=k) ->
  length xs=(Datatypes.S m*(Datatypes.S n+Datatypes.S(goe_vector_index n)))%nat ->
  finite_sum (fun i=>Rabs(gaussian_row_remainder n m beta gamma y B Y S t i xs))
    (List.seq 0 (Datatypes.S m)) <=
  40*k^3*(beta+gamma)^2*theta/sqrt(INR(Datatypes.S n))*
    gaussian_maximum_radius (Datatypes.S m) (Datatypes.S n)
      (row_prefixes (Datatypes.S m) (Datatypes.S n) (Datatypes.S(goe_vector_index n)) xs).
Proof.
  intros Hb Hg Hk Htheta HY HS Hy Hcap Hsym HB HL.
  apply gaussian_row_remainder_radial_sum; try assumption.
  - exact (proj1 (gaussian_maximum_radius_bounds _ _ _)).
  - intros i Hi; apply in_seq in Hi.
    exact (proj1 (gaussian_interleaved_maximum_norm_characterization n (Datatypes.S m) xs HL ltac:(lia)) i ltac:(lia)).
Qed.

Theorem gaussian_row_remainder_absolute_sum n m beta gamma y B Y S t theta k xs :
  0<beta -> 0<gamma -> 0<=k -> 0<theta -> Y<>[] -> S<>[] ->
  (forall z, In z Y -> euclidean_norm(y z)(List.seq 0 (Datatypes.S m))=1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) -> Rabs(y z i)<=theta/sqrt(INR(Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s)<=k) ->
  length xs=(Datatypes.S m*(Datatypes.S n+Datatypes.S(goe_vector_index n)))%nat ->
  Rabs(finite_sum (fun i=>gaussian_row_remainder n m beta gamma y B Y S t i xs)
    (List.seq 0 (Datatypes.S m))) <=
  40*k^3*(beta+gamma)^2*theta/sqrt(INR(Datatypes.S n))*
    gaussian_maximum_radius (Datatypes.S m) (Datatypes.S n)
      (row_prefixes (Datatypes.S m) (Datatypes.S n) (Datatypes.S(goe_vector_index n)) xs).
Proof.
  intros Hb Hg Hk Htheta HY HS Hy Hcap Hsym HB HL.
  eapply Rle_trans; [apply row_finite_sum_abs_le|].
  exact (gaussian_row_remainder_maximum_sum n m beta gamma y B Y S t theta k xs
    Hb Hg Hk Htheta HY HS Hy Hcap Hsym HB HL).
Qed.
