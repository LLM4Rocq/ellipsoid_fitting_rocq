(* Endpoints of the joint interpolation path of JointDefinitions.
   joint_matrix n C t x z is C + goe_matrix n z at t = 0
   (joint_matrix_at_zero) and C + joint_quadratic_input n x at t = 1
   (joint_matrix_at_one). joint_endpoint_modulus_continuous: for every K
   and every real a, the modulus
   K * (|sqrt t - sqrt a| + |sqrt (1 - t) - sqrt (1 - a)|) is continuous in
   t at a, since Stdlib's sqrt is continuous on the whole line (it is 0 on
   the negative reals). The arithmetic in every statement is Stdlib's. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorDefinitions
  SoftDefinitions MatrixGibbsDefinitions GoeDefinitions GaussianProductDefinitions
  GaussianVectorDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions JointDefinitions JointCoordinates
  GaussianPairExchange GaussianExpectationContinuity TimeDefinitions
  JointTimeCalculus JointLipschitz.
From EllipsoidFitting Require Import GaussianProduct GaussianCoordinateMarginals
  GaussianVectorDomain GaussianVectorAlgebra.
Import ListNotations.
Open Scope R_scope.

Lemma joint_endpoint_modulus_continuous K a :
  {for a, continuous (fun t => K*(Rabs(sqrt t-sqrt a)+Rabs(sqrt(1-t)-sqrt(1-a))))}.
Proof.
  have Hsqrt : continuous sqrt.
  { move=> x; rewrite (funext RsqrtE); exact: sqrt_continuous. }
  apply continuous_mult; [apply continuous_const|].
  apply continuous_plus.
  - apply: (continuous_comp (f := fun t => sqrt t - sqrt a)); [|exact: continuous_Rabs].
    apply continuous_minus; [exact: Hsqrt|apply continuous_const].
  - apply: (continuous_comp (f := fun t => sqrt (1-t) - sqrt (1-a))); [|exact: continuous_Rabs].
    apply continuous_minus; [|apply continuous_const].
    apply: (continuous_comp (f := fun t => 1-t)); [|exact: Hsqrt].
    apply continuous_minus; [apply continuous_const|apply continuous_id].
Qed.

Lemma joint_matrix_at_zero n C x z :
  joint_matrix n C 0 x z=matrix_add n C (goe_matrix n z).
Proof.
  rewrite (joint_matrix_normalized_path n C 0 x z (Rle_refl 0)).
  replace (1-0) with 1 by ring; rewrite sqrt_0 sqrt_1.
  apply matrix_ext; intros i j Hi Hj.
  rewrite !matrix_entry_add !matrix_entry_scale; ring.
Qed.

Lemma joint_matrix_at_one n C x z :
  joint_matrix n C 1 x z=matrix_add n C (joint_quadratic_input n x).
Proof.
  rewrite (joint_matrix_normalized_path n C 1 x z Rle_0_1).
  replace (1-1) with 0 by ring; rewrite sqrt_0 sqrt_1.
  apply matrix_ext; intros i j Hi Hj.
  rewrite !matrix_entry_add !matrix_entry_scale; ring.
Qed.
