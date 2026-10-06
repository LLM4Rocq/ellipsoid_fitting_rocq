(* If a - eps * c <= b for every eps > 0, with c >= 0, then a <= b
   (paper_main_gordon_le_of_forall_eps): the limit step of the net
   arguments of Gordon's escape bound. *)
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
