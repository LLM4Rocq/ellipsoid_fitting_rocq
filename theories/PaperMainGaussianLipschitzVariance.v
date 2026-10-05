(* Variance control for Euclidean-Lipschitz Gaussian tests, derived from
   the actual exponential moment bound. This is an input to cone widths. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions
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

Lemma paper_main_variance_cosh_quadratic x :
  2 + x ^ 2 <= exp x + exp (-x).
Proof.
assert (H0 : forall u, 2 <= exp u + exp (-u)).
{ intros u; pose proof (exp_ineq1_le u); pose proof (exp_ineq1_le (-u)); lra. }
assert (H1 : forall u, 0 <= u -> 0 <= exp u - exp (-u) - 2*u).
{ intros u Hu.
  pose proof (paper_main_variance_derivative_nonnegative
    (fun t => exp t - exp (-t) - 2*t)
    (fun t => exp t + exp (-t) - 2) u Hu) as H.
  assert (HD : forall t, @is_derive R R^o R^o t 1
    (fun t => exp t - exp (-t) - 2*t) (exp t + exp (-t) - 2)).
  { intros t; auto_derive; try lra; simpl; ring. }
  specialize (H HD ltac:(intros t _; pose proof (H0 t); lra)).
  simpl in H; rewrite Ropp_0 exp_0 in H; lra. }
assert (H2 : forall u, 0 <= u -> 2 + u^2 <= exp u + exp (-u)).
{ intros u Hu.
  pose proof (paper_main_variance_derivative_nonnegative
    (fun t => exp t + exp (-t) - 2 - t^2)
    (fun t => exp t - exp (-t) - 2*t) u Hu) as H.
  assert (HD : forall t, @is_derive R R^o R^o t 1
    (fun t => exp t + exp (-t) - 2 - t^2) (exp t - exp (-t) - 2*t)).
  { intros t; auto_derive; try lra; simpl; ring. }
  specialize (H HD H1); simpl in H; rewrite Ropp_0 exp_0 in H; lra. }
destruct (Rle_dec 0 x) as [Hx|Hx]; [exact (H2 x Hx)|].
pose proof (H2 (-x) ltac:(lra)) as H; rewrite Ropp_involutive in H; nra.
Qed.

Theorem paper_main_gaussian_lipschitz_square_law d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x) * F (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (F (tval x) * F (tval x))%:E =
    (gaussian_iterated_expectation d (fun xs => F xs * F xs))%:E)%E.
Proof.
move=> HL Hlip.
have HC := paper_main_gaussian_lipschitz_continuous d F L HL Hlip.
have HB := paper_main_gaussian_lipschitz_polynomial_bound d F L HL Hlip.
apply: (paper_main_gaussian_law_transport d _ _ 4).
- exact: (finite_joint_continuous_mult d F F HC HC).
- exact: (finite_polynomial_bound_mult d _ _ 2 2 F F HB HB).
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

Theorem paper_main_gaussian_variance_exponential_bound d F L t :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  0 <= t ->
  2 + t ^ 2 * paper_main_gaussian_variance d F <= 2 * exp (t ^ 2 * L ^ 2 / 2).
Proof.
move=> HL Hlip Ht.
pose G := fun xs => F xs - gaussian_iterated_expectation d F.
have HGlip := paper_main_gaussian_lipschitz_center d F L (gaussian_iterated_expectation d F) Hlip.
have [HIS HES] := paper_main_gaussian_lipschitz_square_law d G L HL HGlip.
have [HIC HEC] := paper_main_gaussian_law_transport d (fun _ => 2) _ 0
  (finite_joint_continuous_constant d 2) (finite_polynomial_bound_constant d 2).
rewrite (proj2 (gaussian_iterated_constant d 2)) in HEC.
have HIP := paper_main_gaussian_lipschitz_mgf_integrable d F L t HL Hlip Ht.
have HBP := paper_main_gaussian_lipschitz_centered_mgf d F L t HL Hlip Ht.
have HlipN := paper_main_gaussian_lipschitz_neg d F L Hlip.
have HIN := paper_main_gaussian_lipschitz_mgf_integrable d (fun xs => -1 * F xs) L t HL HlipN Ht.
have HBN := paper_main_gaussian_lipschitz_centered_mgf d (fun xs => -1 * F xs) L t HL HlipN Ht.
have EN : (fun x : d.-tuple (measurableTypeR R) =>
    (exp (t * (-1 * F (tval x) - gaussian_iterated_expectation d (fun xs => -1 * F xs))))%:E) =
  (fun x => (exp (- (t * G (tval x))))%:E).
{ apply: funext => x.
  rewrite (paper_main_gaussian_lipschitz_neg_mean d F L HL Hlip).
  apply f_equal; apply f_equal; unfold G; ring. }
rewrite EN in HIN HBN.
have HIT : (gaussian_product_law d).-integrable setT
  (fun x => ((t ^ 2)%:E * (G (tval x) * G (tval x))%:E)%E).
  exact: integrableZl HIS.
have HIA := integrableD measurableT HIC HIT.
have HIB := integrableD measurableT HIP HIN.
have Hcmp : (\int[gaussian_product_law d]_x
    (2%:E + (t ^ 2)%:E * (G (tval x) * G (tval x))%:E) <=
  \int[gaussian_product_law d]_x
    ((exp (t * G (tval x)))%:E + (exp (- (t * G (tval x))))%:E))%E.
{ eapply (le_integral measurableT HIA HIB).
  move=> x _; rewrite -EFinM -EFinD -EFinD lee_fin; apply/RleP.
  pose proof (paper_main_variance_cosh_quadratic (t * G (tval x))) as H.
  change (2 + t ^ 2 * (G (tval x) * G (tval x)) <=
    exp (t * G (tval x)) + exp (- (t * G (tval x)))); nra. }
rewrite (integralD measurableT HIC HIT) (integralD measurableT HIP HIN)
  (integralZl measurableT HIS) HEC HES in Hcmp.
have HB := leeD HBP HBN.
have HT := le_trans Hcmp HB.
move: HT; rewrite -EFinM -EFinD -EFinD lee_fin => /RleP H.
change (2 + t ^ 2 * paper_main_gaussian_variance d F <=
  exp (t ^ 2 * L ^ 2 / 2) + exp (t ^ 2 * L ^ 2 / 2)) in H; lra.
Qed.

Lemma paper_main_variance_exponential_slope V a :
  (forall s, 0 < s -> 2 + s * V <= 2 * exp (s * a)) -> V <= 2 * a.
Proof.
intros HB; apply Rnot_lt_le; intros HV.
assert (HD : derivable_pt_lim (fun s => exp (s * a)) 0 a).
{ apply Reals_of_is_derive; auto_derive; simpl; rewrite ?Rmult_0_l ?exp_0; ring. }
set (eps := (V - 2*a)/4).
assert (Heps : 0 < eps) by (unfold eps; lra).
destruct (HD eps Heps) as [delta Hdelta].
set (h := delta / 2).
assert (Hh : 0 < h) by (unfold h; pose proof (cond_pos delta); lra).
assert (Hhd : Rabs h < delta).
{ rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hh)); unfold h; pose proof (cond_pos delta); lra. }
pose proof (Hdelta h ltac:(lra) Hhd) as Hlim.
rewrite Rplus_0_l Rmult_0_l exp_0 in Hlim.
pose proof (Rle_abs ((exp (h*a)-1)/h - a)) as Hab.
assert (Hq : (exp (h*a)-1)/h < a + eps) by lra.
pose proof (Rmult_lt_compat_r h _ _ Hh Hq) as Hmul.
replace ((exp (h*a)-1)/h*h) with (exp (h*a)-1) in Hmul by (field; lra).
pose proof (HB h Hh); unfold eps in Hmul; nra.
Qed.

Theorem paper_main_gaussian_lipschitz_variance d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  paper_main_gaussian_variance d F <= L ^ 2.
Proof.
intros HL Hlip.
replace (L ^ 2) with (2 * (L ^ 2 / 2)) by field.
apply paper_main_variance_exponential_slope; intros s Hs.
pose proof (paper_main_gaussian_variance_exponential_bound d F L (sqrt s)
  HL Hlip (sqrt_pos s)) as H.
rewrite (pow2_sqrt s (Rlt_le _ _ Hs)) in H.
replace (s * (L ^ 2 / 2)) with (s * L ^ 2 / 2) by field; exact H.
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
