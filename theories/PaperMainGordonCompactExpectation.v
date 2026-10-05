(* Gordon's expectation bound for the genuine set-index min-max. For N > 0
   and a nonempty set T of unit vectors of R^M,
     w(T) - E ||g_N|| <= E minmax_T(A),
   where w(T) is the Gaussian width of T (a genuine supremum), g_N is a
   standard Gaussian vector of R^N, and A is an N x M standard Gaussian
   matrix. The exact Gaussian norm mean is kept; the sqrt N form follows.
   The proof uses the checked finite comparison through a new exact-mean
   helper, finite nets inside T and inside the unit sphere, and the
   Frobenius bound for the bilinear error; it needs no compactness of T and
   assumes no attained extremum. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality Epsilon.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights GaussianCoordinateSteinDomains
  GaussianFiniteSums GaussianCovarianceDefinitions GaussianCovarianceSums
  MaximumRadiusMoments GaussianExpectationContinuity PaperMainGordonFinite PaperMainGordonProcessCovariance
  PaperMainGordonProcesses PaperMainGordonScalar PaperMainGaussianNorm
  PaperMainGordonWidth PaperMainGordonSetWidth PaperMainGordonNets
  PaperMainGordonNetExistence PaperMainGordonBilinear PaperMainGordonNetToAll
  PaperMainGordonOperatorNet PaperMainGordonCompactMinmax.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_le_of_forall_eps (a b c : R) :
  0 <= c -> (forall eps, 0 < eps -> a - eps * c <= b) -> a <= b.
Proof.
intros Hc H; apply Rnot_lt_le; intros Hlt.
assert (Hpos : 0 < (a - b) / (2 * (c + 1))) by (apply Rdiv_lt_0_compat; lra).
specialize (H _ Hpos).
assert (Hlt2 : (a - b) / (2 * (c + 1)) * c < a - b).
{ apply (Rmult_lt_reg_r (2 * (c + 1))); [lra|].
  replace ((a - b) / (2 * (c + 1)) * c * (2 * (c + 1))) with ((a - b) * c)
    by (field; lra).
  nra. }
lra.
Qed.
