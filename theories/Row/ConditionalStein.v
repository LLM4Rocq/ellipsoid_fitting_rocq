From Stdlib Require Import Reals List Lia Lra FunctionalExtensionality.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Goe.Definitions Joint.Definitions
  Tensor.Definitions Soft.MatrixDefinitions Soft.BlockSliceDefinitions
  Soft.MinimaxDerivativeDefinitions Soft.LowerThirdDefinitions
  Gibbs.NestedGradientDefinitions Gibbs.MatrixDefinitions
  Gibbs.MatrixThirdDerivativeDefinitions Chaos.SecondOrderDefinitions
  Gaussian.Iterated.Definitions Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions Gibbs.MatrixNestedGradient
  Matrix.BlockInjection Row.BlockDirectionDerivatives Row.CoordinateDefinitions
  Row.Coordinates Row.JointDecoding Row.ArrayDefinitions Row.ArrayCoordinates
  Row.ObservableDefinitions Gaussian.Iterated.RowExchange.
From EllipsoidFitting Require Gaussian.Iterated.Expectation
  Joint.ListCoordinates Joint.SteinIdentities Gaussian.Iterated.BlockExchange
  Tensor.GibbsCumulantAtoms Soft.MatrixScorePerturbation.
Import ListNotations.
Open Scope R_scope.

(* Gaussian integration by parts for one row of the multirow interpolation.
   The list xs holds the coordinates of m + 1 rows; row i gives a joint
   vector (x, z) (gaussian_row_pair), and gaussian_row_array is the block
   array of the interpolated rows. gaussian_row_velocity is the
   contribution of row i to the time derivative of the block soft minimax
   along this array, and gaussian_row_remainder the contraction with x of
   its third derivative in the directions of row i.
   - gaussian_row_current_velocity_slice and
     gaussian_row_current_remainder_slice: these are the joint observables
     of Joint.Definitions for the nested soft minimax of row i alone, with
     offsets from the other rows (soft_matrix_row_offset) and coefficients
     soft_matrix_coefficients n y B i.
   - gaussian_row_sections: the same when row i is placed among fixed other
     rows (row_assemble); the offsets do not depend on row i.
   - gaussian_row_conditional_stein: for fixed other rows, symmetric B s and
     0 < t < 1, the expectation over row i of the velocity is
     sqrt t / (2 * (n + 1) * sqrt (n + 1)) times that of the remainder
     (joint_gaussian_stein_cancellation).
   - gaussian_row_full_stein_of_regular: the same identity for the
     expectation over all the coordinates, when the velocity and the
     remainder are continuous and polynomially bounded
     (gaussian_row_conditional_identity). *)

Theorem gaussian_row_current_velocity_slice n m beta gamma y B Y S t i xs :
  (i<=m)%nat ->
  let off := soft_matrix_row_offset n y B (seq 0 (Datatypes.S m))
    (fun j=>gaussian_row_matrix n t j xs) i in
  let pair := gaussian_row_pair n i xs in
  gaussian_row_velocity n m beta gamma y B Y S t i xs =
    joint_quadratic_trace n beta gamma off (soft_matrix_coefficients n y B i)
      Y S (matrix_zero n) t (fst pair) (snd pair) / (2*sqrt t) -
    joint_goe_trace n beta gamma off (soft_matrix_coefficients n y B i)
      Y S (matrix_zero n) t (fst pair) (snd pair) / (2*sqrt (1-t)).
Proof.
  intro Hi; cbn zeta.
  unfold gaussian_row_velocity; cbn zeta.
  fold (block_inject n m i (joint_quadratic_input n (fst (gaussian_row_pair n i xs)))).
  fold (block_inject n m i (goe_matrix n (snd (gaussian_row_pair n i xs)))).
  unfold gaussian_row_array.
  rewrite !block_row_first_from_array by exact Hi.
  unfold joint_quadratic_trace, joint_goe_trace.
  rewrite <- !matrix_nested_gradient_trace.
  rewrite (Soft.MatrixScorePerturbation.soft_matrix_trace_pair_swap n
    (joint_quadratic_input n (fst (gaussian_row_pair n i xs)))).
  rewrite (Soft.MatrixScorePerturbation.soft_matrix_trace_pair_swap n
    (goe_matrix n (snd (gaussian_row_pair n i xs)))).
  reflexivity.
Qed.

Theorem gaussian_row_current_remainder_slice n m beta gamma y B Y S t i xs :
  (i<=m)%nat ->
  let off := soft_matrix_row_offset n y B (seq 0 (Datatypes.S m))
    (fun j=>gaussian_row_matrix n t j xs) i in
  let pair := gaussian_row_pair n i xs in
  gaussian_row_remainder n m beta gamma y B Y S t i xs =
    joint_remainder n beta gamma off (soft_matrix_coefficients n y B i)
      Y S (matrix_zero n) t (fst pair) (snd pair).
Proof.
  intro Hi; cbn zeta.
  unfold gaussian_row_remainder, joint_remainder; cbn zeta.
  apply f_equal with (f:=fun T => chaos_contraction n T (fst (gaussian_row_pair n i xs))).
  apply functional_extensionality; intro U.
  apply functional_extensionality; intro V.
  apply functional_extensionality; intro W.
  fold (block_inject n m i U); fold (block_inject n m i V); fold (block_inject n m i W).
  unfold gaussian_row_array.
  rewrite block_row_third_from_array by exact Hi; reflexivity.
Qed.

Theorem gaussian_row_sections n m beta gamma y B Y S t i background anchor :
  length background = ((Datatypes.S m-1)*(Datatypes.S n+Datatypes.S(goe_vector_index n)))%nat ->
  (i<=m)%nat ->
  let off := soft_matrix_row_offset n y B (seq 0 (Datatypes.S m))
    (fun j=>gaussian_row_matrix n t j
      (row_assemble (Datatypes.S m) (Datatypes.S n+Datatypes.S(goe_vector_index n)) i background
        (joint_vector_to_list n (goe_vector_index n) anchor))) i in
  forall x z,
  gaussian_row_velocity n m beta gamma y B Y S t i
    (row_assemble (Datatypes.S m) (Datatypes.S n+Datatypes.S(goe_vector_index n)) i background
      (joint_vector_to_list n (goe_vector_index n) (x,z))) =
    joint_quadratic_trace n beta gamma off (soft_matrix_coefficients n y B i)
      Y S (matrix_zero n) t x z / (2*sqrt t) -
    joint_goe_trace n beta gamma off (soft_matrix_coefficients n y B i)
      Y S (matrix_zero n) t x z / (2*sqrt (1-t)) /\
  gaussian_row_remainder n m beta gamma y B Y S t i
    (row_assemble (Datatypes.S m) (Datatypes.S n+Datatypes.S(goe_vector_index n)) i background
      (joint_vector_to_list n (goe_vector_index n) (x,z))) =
    joint_remainder n beta gamma off (soft_matrix_coefficients n y B i)
      Y S (matrix_zero n) t x z.
Proof.
  intros HB Hi; cbn zeta; intros x z.
  rewrite gaussian_row_current_velocity_slice by exact Hi.
  rewrite gaussian_row_current_remainder_slice by exact Hi.
  rewrite gaussian_row_pair_assemble by (try exact HB; lia).
  cbn [fst snd].
  rewrite (gaussian_row_offset_independent n (Datatypes.S m) t y B
    (seq 0 (Datatypes.S m)) i background (x,z) anchor HB ltac:(lia)).
  split; reflexivity.
Qed.

Theorem gaussian_row_conditional_stein n m beta gamma y B Y S t i background :
  length background = ((Datatypes.S m-1)*(Datatypes.S n+Datatypes.S(goe_vector_index n)))%nat ->
  (i<=m)%nat -> 0<beta -> 0<gamma -> Y<>[] -> S<>[] -> 0<t<1 ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  let K := (Datatypes.S n+Datatypes.S(goe_vector_index n))%nat in
  gaussian_list_domain K (fun row => gaussian_row_velocity n m beta gamma y B Y S t i
    (row_assemble (Datatypes.S m) K i background row)) /\
  gaussian_list_domain K (fun row => gaussian_row_remainder n m beta gamma y B Y S t i
    (row_assemble (Datatypes.S m) K i background row)) /\
  gaussian_iterated_expectation K (fun row => gaussian_row_velocity n m beta gamma y B Y S t i
    (row_assemble (Datatypes.S m) K i background row)) =
  (sqrt t/(2*INR(Datatypes.S n)*sqrt(INR(Datatypes.S n)))) *
    gaussian_iterated_expectation K (fun row => gaussian_row_remainder n m beta gamma y B Y S t i
      (row_assemble (Datatypes.S m) K i background row)).
Proof.
  intros HB Hi Hb Hg HY HS Ht Hsym; cbn zeta.
  set (K := (Datatypes.S n+Datatypes.S(goe_vector_index n))%nat).
  set (anchor := joint_vector_of_list n (goe_vector_index n) []).
  set (off := soft_matrix_row_offset n y B (seq 0 (Datatypes.S m))
    (fun j=>gaussian_row_matrix n t j
      (row_assemble (Datatypes.S m) K i background
        (joint_vector_to_list n (goe_vector_index n) anchor))) i).
  set (V := fun x z => joint_quadratic_trace n beta gamma off
    (soft_matrix_coefficients n y B i) Y S (matrix_zero n) t x z / (2*sqrt t) -
    joint_goe_trace n beta gamma off (soft_matrix_coefficients n y B i)
      Y S (matrix_zero n) t x z / (2*sqrt(1-t))).
  set (Rem := joint_remainder n beta gamma off (soft_matrix_coefficients n y B i)
      Y S (matrix_zero n) t).
  assert (Hcoeff : forall z s, In z Y -> In s S -> symmetric_matrix n (soft_matrix_coefficients n y B i z s)).
  { intros z s Hz Hs; unfold soft_matrix_coefficients.
    apply Tensor.GibbsCumulantAtoms.matrix_scale_symmetric, Hsym, Hs. }
  destruct (Joint.SteinIdentities.joint_gaussian_stein_cancellation n beta gamma
    off (soft_matrix_coefficients n y B i) Y S (matrix_zero n) t Hb Hg HY HS Ht Hcoeff)
    as [HD [_ [_ [HVD HE]]]].
  assert (HRD : gaussian_pair_domain n (goe_vector_index n) Rem).
  { apply (proj1 (Forall_forall _ _) HD); unfold Rem; simpl; auto. }
  assert (Hsections : forall row, length row=K ->
    gaussian_pair_pullback n (goe_vector_index n) V row =
      gaussian_row_velocity n m beta gamma y B Y S t i (row_assemble (Datatypes.S m) K i background row) /\
    gaussian_pair_pullback n (goe_vector_index n) Rem row =
      gaussian_row_remainder n m beta gamma y B Y S t i (row_assemble (Datatypes.S m) K i background row)).
  { intros row Hrow.
    pose proof (gaussian_row_sections n m beta gamma y B Y S t i background anchor HB Hi
      (fst (joint_vector_of_list n (goe_vector_index n) row))
      (snd (joint_vector_of_list n (goe_vector_index n) row))) as H.
    cbn zeta in H.
    rewrite <- surjective_pairing in H.
    rewrite Joint.ListCoordinates.joint_vector_to_of_list in H by exact Hrow.
    unfold gaussian_pair_pullback, V, Rem, off; split; symmetry; tauto. }
  split.
  - eapply Gaussian.Iterated.BlockExchange.gaussian_list_domain_ext;
      [intros row Hrow; exact (proj1 (Hsections row Hrow))|exact HVD].
  - split.
    + eapply Gaussian.Iterated.BlockExchange.gaussian_list_domain_ext;
        [intros row Hrow; exact (proj2 (Hsections row Hrow))|exact HRD].
    + unfold gaussian_pair_expectation in HE; fold K V Rem in HE.
      rewrite (Gaussian.Iterated.Expectation.gaussian_iterated_expectation_ext K
        (gaussian_pair_pullback n (goe_vector_index n) V) _ (fun row Hrow => proj1 (Hsections row Hrow))) in HE.
      rewrite (Gaussian.Iterated.Expectation.gaussian_iterated_expectation_ext K
        (gaussian_pair_pullback n (goe_vector_index n) Rem) _ (fun row Hrow => proj2 (Hsections row Hrow))) in HE.
      exact HE.
Qed.

Theorem gaussian_row_full_stein_of_regular n m beta gamma y B Y S t i CV CR :
  (i<=m)%nat -> 0<beta -> 0<gamma -> Y<>[] -> S<>[] -> 0<t<1 ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  let D := ((Datatypes.S m)*(Datatypes.S n+Datatypes.S(goe_vector_index n)))%nat in
  finite_joint_continuous D (gaussian_row_velocity n m beta gamma y B Y S t i) ->
  finite_polynomial_bound D CV 2 (gaussian_row_velocity n m beta gamma y B Y S t i) ->
  finite_joint_continuous D (gaussian_row_remainder n m beta gamma y B Y S t i) ->
  finite_polynomial_bound D CR 2 (gaussian_row_remainder n m beta gamma y B Y S t i) ->
  gaussian_list_domain D (gaussian_row_velocity n m beta gamma y B Y S t i) /\
  gaussian_list_domain D (gaussian_row_remainder n m beta gamma y B Y S t i) /\
  gaussian_iterated_expectation D (gaussian_row_velocity n m beta gamma y B Y S t i) =
    (sqrt t/(2*INR(Datatypes.S n)*sqrt(INR(Datatypes.S n)))) *
      gaussian_iterated_expectation D (gaussian_row_remainder n m beta gamma y B Y S t i).
Proof.
  intros Hi Hb Hg HY HS Ht Hsym D HCV HBV HCR HBR.
  apply (gaussian_row_conditional_identity (Datatypes.S m)
    (Datatypes.S n+Datatypes.S(goe_vector_index n)) i
    (gaussian_row_velocity n m beta gamma y B Y S t i)
    (gaussian_row_remainder n m beta gamma y B Y S t i) CV CR 2 2
    (sqrt t/(2*INR(Datatypes.S n)*sqrt(INR(Datatypes.S n)))));
    try assumption; [lia|].
  intros background HB.
  exact (proj2 (proj2 (gaussian_row_conditional_stein n m beta gamma y B Y S t i background
    HB Hi Hb Hg HY HS Ht Hsym))).
Qed.
