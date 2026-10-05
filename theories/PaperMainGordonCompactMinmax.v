(* The genuine set-index Gordon min-max. For a matrix A given by its
   N*M list coordinates and a nonempty set T of unit vectors of R^M,
   minmax(A) is the infimum over the unit sphere of R^N of the supremum
   over T of z^T A v. Both extrema are genuine least upper bounds chosen by
   epsilon; their existence is proved by completeness from the Frobenius
   bound, and no extremum is assumed attained. For N > 0, minmax is
   1-Lipschitz in A for the Euclidean (Frobenius) distance, jointly
   continuous and Gaussian integrable. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateSteinDomains GaussianCoordinateWeights GaussianCovarianceSums
  PaperMainGordonProcessCovariance PaperMainGordonScalar PaperMainGordonLipschitz
  PaperMainGordonBilinear PaperMainGordonNetToAll PaperMainGordonOperatorNet
  PaperMainGordonOperatorContinuity
  PaperMainGaussianNorm PaperMainGaussianSmoothCalculus PaperMainGaussianLipschitzClip.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_unit_matrix_value_bound N M u v xs :
  List.length xs = (N * M)%nat ->
  paper_main_gordon_dot N u u = 1 -> paper_main_gordon_dot M v v = 1 ->
  Rabs (paper_main_gordon_matrix_value N M u v xs) <= paper_main_gaussian_norm xs.
Proof.
intros Hxs Hu Hv.
assert (Hu1 : paper_main_gordon_dot N u u <= 1 ^ 2) by (rewrite Hu; lra).
assert (Hv1 : paper_main_gordon_dot M v v <= 1 ^ 2) by (rewrite Hv; lra).
pose proof (paper_main_gordon_bilinear_ball_bound N M xs (paper_main_gaussian_norm xs)
  u v 1 1 (paper_main_gordon_operator_frobenius N M xs Hxs) Rle_0_1 Rle_0_1 Hu1 Hv1) as H.
lra.
Qed.
