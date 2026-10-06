(* The bilinear form of a matrix at unit vectors is bounded by its
   Frobenius norm. For an N-by-M matrix A given by its N*M row-major list
   coordinates xs (paper_main_gordon_matrix_value) and unit vectors u of
   R^N and v of R^M, |u^T A v| <= paper_main_gaussian_norm xs, the
   Euclidean norm of xs (paper_main_gordon_unit_matrix_value_bound), from
   the ball bound paper_main_gordon_bilinear_ball_bound and the Frobenius
   operator bound paper_main_gordon_operator_frobenius. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Gaussian.CoordinatePolynomialDomain Gaussian.CoordinateWeights
  Analysis.FiniteSumAlgebra Gordon.ProcessCovariance Gordon.Scalar
  Gordon.Lipschitz Gordon.Bilinear Gordon.NetToAll Gordon.OperatorNet
  Gordon.OperatorContinuity Gaussian.Norm Gaussian.SmoothCalculus
  Gaussian.LipschitzClip.
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
