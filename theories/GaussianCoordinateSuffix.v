(* Port of theories/GaussianCoordinateSuffix.v from Coquelicot to
   MathComp-Analysis.

   Every theorem keeps its name, its arguments in the same order and its
   text. The only change to the file is that the Coquelicot import line
   (Coquelicot and Compactness) is dropped: no statement or proof here names
   a Coquelicot notion.

   The statements use finite_joint_continuous (ported
   GaussianCoordinateDefinitions), finite_polynomial_bound and
   gaussian_coordinate_weight_moment (ported
   GaussianCoordinateWeightDefinitions) and gaussian_suffix_marginal
   (ported GaussianLastDefinitions). Their texts are the original ones.
   finite_joint_continuous and finite_polynomial_bound involve no integral,
   so they mean what they meant. gaussian_suffix_marginal n F xs is an
   iterated Gaussian expectation over the last n coordinates, and
   gaussian_coordinate_weight_moment p the Gaussian expectation of the
   weight 1 + Rabs x ^ p; the Gaussian expectation underneath is now the
   Lebesgue integral over the line (difference 4 of analysis/README.md).
   Under the hypotheses of these theorems every integrand is continuous in
   the integrated variable and bounded by a constant times a polynomial
   weight, so it is absolutely integrable against the kernel, where the
   Lebesgue and the improper Riemann integrals agree. The conclusions are
   therefore the same statements as before, about the same numbers. This
   agreement is a mathematical argument and is not proved in Rocq.

   The proofs are the original ones, word for word. They use
   gaussian_last_marginal_continuous and
   gaussian_last_marginal_polynomial_bound (ported
   GaussianCoordinateMarginals), finite_joint_continuous_ext (ported
   GaussianCoordinateTopology), finite_polynomial_bound_ext,
   gaussian_suffix_marginal_zero and gaussian_suffix_marginal_succ (ported
   GaussianCoordinateSuffixAlgebra), whose statements are the original
   texts.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So ++, length, the %nat scope, + on nat and the
   operations on R are Stdlib's, as in the original. *)

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
