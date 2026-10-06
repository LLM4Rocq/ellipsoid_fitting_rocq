(* The one-dimensional Gaussian shift derivative is proved, so the concrete
   smoothing of every bounded Euclidean-Lipschitz test is a bounded C2 test
   with the same squared-gradient bound. No approximation premise remains. *)
From Stdlib Require Import Reals List Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions GaussianDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateDerivativeDefinitions
  GaussianProductDefinitions PaperMainGaussianSmoothCalculus
  PaperMainGaussianSmoothCovariance PaperMainGordonLipschitz
  PaperMainGaussianLipschitzSmooth PaperMainGaussianLipschitzSmoothDerivative
  PaperMainGaussianLipschitzSmoothDerivativeLift
  PaperMainGaussianAffineIntegralDerivative.
Open Scope R_scope.

Lemma paper_main_real_lipschitz_continuous (h : R -> R) L :
  0 <= L -> (forall x y, Rabs (h x - h y) <= L * Rabs (x - y)) -> continuous h.
Proof.
intros HL Hlip x; apply (proj2 (continuous_Reals h x)); intros e He.
exists (e / (L + 1)); split.
- apply Rdiv_lt_0_compat; lra.
- intros y Hy.
  pose proof (Hlip y x) as Hh.
  pose proof (Rabs_pos (y - x)) as Hd.
  pose proof (Rmult_lt_compat_r (L + 1) _ _ ltac:(lra) Hy) as Hm.
  replace (e / (L + 1) * (L + 1)) with e in Hm by (field; lra).
  nra.
Qed.

Theorem paper_main_gaussian_shift_derivative_proved eps :
  0 < eps -> paper_main_gaussian_shift_derivative_interface eps.
Proof.
intros Heps h K L a HK HL Hb Hlip.
pose proof (paper_main_real_lipschitz_continuous h L HL Hlip) as Hh.
split.
- exact (paper_main_gaussian_shift_expectation_derivative eps h K a Heps HK Hh Hb).
- assert (HE : (fun z => (z * z - 1) * h (a + eps * z)) =
    (fun z => h (a + eps * z) * (z ^ 2 - 1))).
  { apply functional_extensionality; intros z; ring. }
  rewrite HE.
  apply (is_derive_ext (fun t => gaussian_expectation (fun z => h (t + eps * z) * z))).
  + intros t; f_equal; apply functional_extensionality; intros z; ring.
  + exact (paper_main_gaussian_shift_weighted_expectation_derivative eps h K a Heps HK Hh Hb).
Qed.
