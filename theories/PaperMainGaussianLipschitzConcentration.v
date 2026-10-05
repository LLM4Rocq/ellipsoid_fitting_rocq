(* Gaussian concentration for every Euclidean-Lipschitz test on length-d
   lists, under the exact public Gaussian product law. The proof uses the
   actual clipped Gaussian smoothings and their proved convergence. *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianProductDefinitions GaussianProduct GaussianCoordinatePolynomialContinuity
  GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainGordonLipschitz
  PaperMainGaussianSmoothCovariance PaperMainGaussianMGFBound
  PaperMainGaussianSmoothLaw PaperMainGaussianSmoothTail
  PaperMainGaussianTailLimit PaperMainGaussianLipschitzClip
  PaperMainGaussianLipschitzSmooth PaperMainGaussianLipschitzSmoothDerivative
  PaperMainGaussianLipschitzSmoothDerivativeLift
  PaperMainGaussianLipschitzApproximation PaperMainGaussianLipschitzApproximationLaw
  PaperMainGaussianAffineIntegralSmoothing PaperMainGaussianLipschitzConcentrationTail.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem paper_main_gaussian_lipschitz_centered_mgf d F L t :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 <= t ->
  (\int[gaussian_product_law d]_x
     (exp (t * (F (tval x) - gaussian_iterated_expectation d F)))%:E <=
     (exp (t ^ 2 * L ^ 2 / 2))%:E)%E.
Proof.
move=> HL Hlip Ht.
under eq_integral do rewrite RexpE.
rewrite RexpE.
eapply (@paper_main_centered_exponential_limit_bound _ _ (gaussian_product_law d)
  (paper_main_gaussian_approximant_random d F)
  (paper_main_gaussian_smooth_random d F)
  (fun n => gaussian_iterated_expectation d (paper_main_gaussian_approximant d F n))
  (gaussian_iterated_expectation d F) t _).
- move=> n; exact: (paper_main_gaussian_approximant_random_measurable d F L n HL Hlip).
- move=> x; exact: (paper_main_gaussian_approximant_random_cvg d F L x HL Hlip).
- exact: (paper_main_gaussian_approximant_mean_cvg d F L HL Hlip).
- move=> n.
  have HI := paper_main_gaussian_shift_derivative_proved _ (paper_main_gaussian_width_pos n).
  have HS := paper_main_gaussian_approximant_smooth_test_conditional d F L n HI HL Hlip.
  have HG := paper_main_gaussian_approximant_gradient_conditional d F L n HI HL Hlip.
  have [_ HB] := paper_main_gaussian_smooth_law_centered_mgf d _ _ _ _ L t HS HG Ht.
  move: HB.
  under eq_integral do rewrite /paper_main_gaussian_centered_exp RexpE.
  rewrite RexpE; done.
Qed.

Theorem paper_main_gaussian_lipschitz_mgf_integrable d F L t :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 <= t ->
  (gaussian_product_law d).-integrable setT
    (fun x => (exp (t * (F (tval x) - gaussian_iterated_expectation d F)))%:E).
Proof.
move=> HL Hlip Ht; apply/integrableP; split.
- have HE : (fun x : d.-tuple (measurableTypeR R) =>
      (exp (t * (F (tval x) - gaussian_iterated_expectation d F)))%:E) =
    (fun x => (expR (t * (paper_main_gaussian_smooth_random d F x -
      gaussian_iterated_expectation d F))%R)%:E).
  { apply: funext => x; rewrite RexpE; reflexivity. }
  rewrite HE; apply: paper_main_centered_exponential_measurable.
  exact: (paper_main_gaussian_lipschitz_random_measurable d F L HL Hlip).
- have HA : (\int[gaussian_product_law d]_x
      `|(exp (t * (F (tval x) - gaussian_iterated_expectation d F)))%:E| =
    \int[gaussian_product_law d]_x
      (exp (t * (F (tval x) - gaussian_iterated_expectation d F)))%:E)%E.
  { apply: eq_integral => x _; apply: gee0_abs.
    by rewrite lee_fin RexpE expR_ge0. }
  rewrite HA.
  apply: le_lt_trans (paper_main_gaussian_lipschitz_centered_mgf d F L t HL Hlip Ht) _.
  exact: ltry.
Qed.

Theorem paper_main_gaussian_lipschitz_upper_tail d F L u :
  0 < L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 < u ->
  (gaussian_product_law d
     [set x | Rle (gaussian_iterated_expectation d F + u) (F (tval x))] <=
   (exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
Proof.
move=> HL Hlip Hu.
apply: paper_main_gaussian_mgf_upper_tail => //.
- exact: (paper_main_gaussian_lipschitz_continuous d F L (Rlt_le _ _ HL) Hlip).
- apply: paper_main_gaussian_lipschitz_centered_mgf => //.
  + exact: Rlt_le.
  + apply Rlt_le, Rdiv_lt_0_compat => //; exact: pow_lt.
Qed.

Lemma paper_main_gaussian_lipschitz_neg d F L :
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (-1 * F xs - (-1 * F ys)) <= L * paper_main_gordon_distance d xs ys.
Proof.
intros Hlip xs ys Hx Hy.
replace (-1 * F xs - (-1 * F ys)) with (- (F xs - F ys)) by ring.
rewrite Rabs_Ropp; exact (Hlip xs ys Hx Hy).
Qed.

Lemma paper_main_gaussian_lipschitz_neg_mean d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  gaussian_iterated_expectation d (fun xs => -1 * F xs) =
    -1 * gaussian_iterated_expectation d F.
Proof.
intros HL Hlip.
destruct (paper_main_gaussian_lipschitz_domain d F L HL Hlip) as [HI _].
exact (proj2 (gaussian_iterated_scale d F (-1) HI)).
Qed.

Theorem paper_main_gaussian_lipschitz_lower_tail d F L u :
  0 < L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 < u ->
  (gaussian_product_law d
     [set x | Rle (F (tval x)) (gaussian_iterated_expectation d F - u)] <=
   (exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
Proof.
move=> HL Hlip Hu.
have H := paper_main_gaussian_lipschitz_upper_tail d (fun xs => -1 * F xs) L u
  HL (paper_main_gaussian_lipschitz_neg d F L Hlip) Hu.
rewrite (paper_main_gaussian_lipschitz_neg_mean d F L (Rlt_le _ _ HL) Hlip) in H.
have HS : [set x : d.-tuple (measurableTypeR R) |
    Rle (F (tval x)) (gaussian_iterated_expectation d F - u)] =
  [set x | Rle (-1 * gaussian_iterated_expectation d F + u) (-1 * F (tval x))].
{ apply/seteqP; split=> x /= Hx; lra. }
rewrite HS; exact H.
Qed.

Theorem paper_main_gaussian_lipschitz_two_sided_tail d F L u :
  0 < L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 < u ->
  (gaussian_product_law d
     [set x | Rle u (Rabs (F (tval x) - gaussian_iterated_expectation d F))] <=
   (2 * exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
Proof.
move=> HL Hlip Hu.
have Hc := paper_main_gaussian_lipschitz_continuous d F L (Rlt_le _ _ HL) Hlip.
have Hcn : finite_joint_continuous d (fun xs => -1 * F xs)
  by apply finite_joint_continuous_scale.
have HS : [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (F (tval x) - gaussian_iterated_expectation d F))] =
  [set x | Rle (gaussian_iterated_expectation d F + u) (F (tval x))] `|`
  [set x | Rle (-1 * gaussian_iterated_expectation d F + u) (-1 * F (tval x))].
{ apply/seteqP; split=> x /=.
  - unfold Rabs; destruct Rcase_abs => Hx; [right|left]; lra.
  - move=> [Hx|Hx]; unfold Rabs; destruct Rcase_abs; lra. }
rewrite HS.
have H1 := paper_main_gaussian_lipschitz_upper_tail d F L u HL Hlip Hu.
have H2 := paper_main_gaussian_lipschitz_lower_tail d F L u HL Hlip Hu.
have HS2 : [set x : d.-tuple (measurableTypeR R) |
    Rle (F (tval x)) (gaussian_iterated_expectation d F - u)] =
  [set x | Rle (-1 * gaussian_iterated_expectation d F + u) (-1 * F (tval x))].
{ apply/seteqP; split=> x /= Hx; lra. }
rewrite HS2 in H2.
eapply le_trans; first exact: (measureU2 _
  (paper_main_gaussian_smooth_ge_measurable d F _ Hc)
  (paper_main_gaussian_smooth_ge_measurable d (fun xs => -1 * F xs) _ Hcn)).
have H := leeD H1 H2.
move: H; rewrite -EFinD.
have HE (z : R) : (z + z)%R = Rmult 2 z.
{ change (z + z = 2 * z); lra. }
rewrite HE; trivial.
Qed.
