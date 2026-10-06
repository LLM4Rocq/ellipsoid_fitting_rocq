(* Variance of Euclidean-Lipschitz Gaussian tests. The variance of F under
   the iterated Gaussian expectation (paper_main_gaussian_variance) is
   nonnegative, equals E[F^2] - (E F)^2 (paper_main_gaussian_variance_identity),
   and is at most L^2 when F is L-Lipschitz for the Euclidean distance
   (paper_main_gaussian_lipschitz_variance): read on row vectors through
   GaussianLawBridge, this is the Gaussian Poincare inequality
   gauss_poincare_lipschitz of the library. paper_main_variance_derivative_nonnegative
   is the monotonicity of a function with a nonnegative derivative. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinateWeightDefinitions
  GaussianCoordinatePolynomialContinuity GaussianCoordinateWeights
  GaussianCoordinateSteinDomains GaussianProductDefinitions GaussianProduct
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainGordonLipschitz PaperMainGaussianSmoothLaw
  PaperMainGaussianLipschitzClip PaperMainGaussianLipschitzApproximation
  PaperMainGaussianLipschitzApproximationLaw PaperMainGaussianLipschitzConcentration.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_variance_derivative_nonnegative f df x :
  0 <= x ->
  (forall u, @is_derive R R^o R^o u 1 f (df u)) ->
  (forall u, 0 <= u -> 0 <= df u) -> f 0 <= f x.
Proof.
intros Hx HD Hsg.
destruct (MVT_gen f 0 x df) as [c [Hc He]].
- intros u _; exact (HD u).
- intros u _; apply (proj2 (continuity_pt_filterlim f u)).
  exact (is_derive_continuous f u (df u) (HD u)).
- rewrite (Rmin_left _ _ Hx) (Rmax_right _ _ Hx) in Hc.
  pose proof (Hsg c ltac:(lra)); nra.
Qed.

Definition paper_main_gaussian_variance d (F : list R -> R) : R :=
  gaussian_iterated_expectation d
    (fun xs => (F xs - gaussian_iterated_expectation d F) *
               (F xs - gaussian_iterated_expectation d F)).

Lemma paper_main_gaussian_lipschitz_center d F L c :
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs ((F xs - c) - (F ys - c)) <= L * paper_main_gordon_distance d xs ys.
Proof.
intros Hlip xs ys Hx Hy.
replace ((F xs - c) - (F ys - c)) with (F xs - F ys) by ring.
exact (Hlip xs ys Hx Hy).
Qed.

Lemma paper_main_gaussian_lipschitz_square_domain d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  gaussian_iterated_integrable d (fun xs => F xs * F xs).
Proof.
intros HL Hlip.
pose proof (paper_main_gaussian_lipschitz_continuous d F L HL Hlip) as HC.
pose proof (paper_main_gaussian_lipschitz_polynomial_bound d F L HL Hlip) as HB.
exact (proj1 (gaussian_coordinate_polynomial_domain d _ _ 4
  (finite_joint_continuous_mult d F F HC HC)
  (finite_polynomial_bound_mult d _ _ 2 2 F F HB HB))).
Qed.

Theorem paper_main_gaussian_variance_identity d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  gaussian_iterated_expectation d (fun xs => F xs * F xs) =
    paper_main_gaussian_variance d F + (gaussian_iterated_expectation d F) ^ 2.
Proof.
intros HL Hlip.
set (m := gaussian_iterated_expectation d F).
destruct (paper_main_gaussian_lipschitz_domain d F L HL Hlip) as [HIF _].
pose proof (paper_main_gaussian_lipschitz_square_domain d F L HL Hlip) as HIS.
destruct (gaussian_iterated_scale d F (-2*m) HIF) as [HIT HET].
destruct (gaussian_iterated_add d (fun xs => F xs * F xs) (fun xs => (-2*m)*F xs)
  HIS HIT) as [HIA HEA].
destruct (gaussian_iterated_constant d (m ^ 2)) as [HIC HEC].
destruct (gaussian_iterated_add d
  (fun xs => F xs * F xs + (-2*m)*F xs) (fun _ => m^2) HIA HIC) as [_ HEB].
assert (HE : paper_main_gaussian_variance d F =
  gaussian_iterated_expectation d (fun xs => F xs * F xs + (-2*m)*F xs + m^2)).
{ unfold paper_main_gaussian_variance; apply gaussian_iterated_expectation_ext;
    intros xs _; unfold m; ring. }
rewrite HE HEB HEA HET HEC; unfold m; ring.
Qed.

Theorem paper_main_gaussian_variance_nonnegative d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 <= paper_main_gaussian_variance d F.
Proof.
intros HL Hlip.
set (G := fun xs => F xs - gaussian_iterated_expectation d F).
pose proof (paper_main_gaussian_lipschitz_center d F L (gaussian_iterated_expectation d F) Hlip) as HGlip.
pose proof (paper_main_gaussian_lipschitz_square_domain d G L HL HGlip) as HIS.
destruct (gaussian_iterated_constant d 0) as [HI0 HE0].
pose proof (gaussian_iterated_monotone d (fun _ => 0) (fun xs => G xs * G xs)
  HI0 HIS ltac:(intros xs _; nra)) as H.
rewrite HE0 in H; exact H.
Qed.

From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral probability.
From GaussianAnalysis Require Import measurable_matrix gauss euclidean gauss_concentration.
From EllipsoidFitting Require Import GaussianLawBridge RealsBridge.

Section lipschitz_variance.
Local Notation RR := (R : realType).

Theorem paper_main_gaussian_lipschitz_variance d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  paper_main_gaussian_variance d F <= L ^ 2.
Proof.
move=> HL Hlip; rewrite /paper_main_gaussian_variance.
set m := gaussian_iterated_expectation d F.
have HGlip := paper_main_gaussian_lipschitz_center d F L m Hlip.
have HGC := paper_main_gaussian_lipschitz_continuous d _ L HL HGlip.
have HGB := paper_main_gaussian_lipschitz_polynomial_bound d _ L HL HGlip.
rewrite (proj2 (gaussian_iterated_expectation_gauss_poly _ _ _ _
  (finite_joint_continuous_mult d _ _ HGC HGC)
  (finite_polynomial_bound_mult d _ _ 2 2 _ _ HGB HGB))).
have Em : m = (\int[gauss d]_x F (list_of_row x))%R.
  exact: (proj2 (gaussian_iterated_expectation_gauss_poly _ _ _ _
    (paper_main_gaussian_lipschitz_continuous d F L HL Hlip)
    (paper_main_gaussian_lipschitz_polynomial_bound d F L HL Hlip))).
pose G := fun x : 'rV[RR]_d => (F (list_of_row x) : RR).
have GL (x y : 'rV[RR]_d) : (`|G x - G y| <= L * frobenius (x - y))%R.
  have := Hlip (list_of_row x) (list_of_row y) (list_of_row_length x)
    (list_of_row_length y).
  by rewrite paper_main_gordon_distance_list_of_row RabsF => /RleP.
have := gauss_poincare_lipschitz GL; rewrite -/G -Em RpowE => /RleP.
by under eq_Rintegral do rewrite expr2.
Qed.

End lipschitz_variance.
