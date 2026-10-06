(* Regularity of gaussian_suffix_marginal n F, the iterated Gaussian
   expectation of F over its last n coordinates, as a function of the first
   d. Let F be a jointly continuous function of d + n coordinates, bounded
   by C times the polynomial weight gaussian_coordinate_product_weight p.
   Then gaussian_suffix_marginal n F is jointly continuous, and bounded by
   C * gaussian_coordinate_weight_moment p ^ n times the same weight on d
   coordinates (gaussian_suffix_marginal_regular,
   gaussian_suffix_marginal_continuous). The proof is by induction on n:
   it integrates out the last coordinates one at a time
   (GaussianCoordinateMarginals). *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions GaussianProduct
  GaussianLastDefinitions GaussianLastIntegration GaussianCoordinateDefinitions
  GaussianCoordinateTopology GaussianCoordinateWeightDefinitions GaussianCoordinateWeights
  GaussianCoordinateMarginals GaussianCoordinateSuffixAlgebra.
Import ListNotations.
Open Scope R_scope.

Theorem gaussian_suffix_marginal_regular d n F C p :
  finite_joint_continuous (d+n) F -> finite_polynomial_bound (d+n) C p F ->
  finite_joint_continuous d (gaussian_suffix_marginal n F) /\
  finite_polynomial_bound d (C*gaussian_coordinate_weight_moment p^n) p
    (gaussian_suffix_marginal n F).
Proof.
  revert d F C; induction n as [|n IH]; intros d F C HC HB.
  - rewrite Nat.add_0_r in HC,HB; split.
    + apply (finite_joint_continuous_ext d F); [|exact HC].
      intros xs Hxs; symmetry; apply gaussian_suffix_marginal_zero.
    + simpl; rewrite Rmult_1_r.
      apply (finite_polynomial_bound_ext d C p F); [|exact HB].
      intros xs Hxs; symmetry; apply gaussian_suffix_marginal_zero.
  - rewrite Nat.add_succ_r in HC,HB.
    pose proof (gaussian_last_marginal_continuous (d+n) F C p HC HB) as HC1.
    pose proof (gaussian_last_marginal_polynomial_bound (d+n) F C p HC HB) as HB1.
    destruct (IH d (gaussian_last_marginal F)
      (C*gaussian_coordinate_weight_moment p) HC1 HB1) as [HCS HBS].
    split.
    + apply (finite_joint_continuous_ext d
        (gaussian_suffix_marginal n (gaussian_last_marginal F))); [|exact HCS].
      intros xs Hxs; symmetry; apply gaussian_suffix_marginal_succ.
    + replace (C*gaussian_coordinate_weight_moment p^S n) with
        ((C*gaussian_coordinate_weight_moment p)*gaussian_coordinate_weight_moment p^n)
        by (simpl; ring).
      apply (finite_polynomial_bound_ext d _ p
        (gaussian_suffix_marginal n (gaussian_last_marginal F))); [|exact HBS].
      intros xs Hxs; symmetry; apply gaussian_suffix_marginal_succ.
Qed.

Theorem gaussian_suffix_marginal_continuous d n F C p :
  finite_joint_continuous (d+n) F -> finite_polynomial_bound (d+n) C p F ->
  finite_joint_continuous d (gaussian_suffix_marginal n F).
Proof. intros HC HB; exact (proj1 (gaussian_suffix_marginal_regular d n F C p HC HB)). Qed.
