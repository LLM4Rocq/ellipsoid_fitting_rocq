(* Integrating the bounded-test Gaussian exponential-moment inequality. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions
  GaussianProductDefinitions GaussianProduct GaussianCoordinateSteinDomains
  PaperMainGaussianSmoothCovariance PaperMainGaussianSmoothExponential
  PaperMainGaussianBoundedMGF.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gaussian_integrating_factor_derivative h dh m v s :
  @is_derive R R^o R^o s 1 h (dh s) ->
  @is_derive R R^o R^o s 1
    (fun u => h u * exp (-m * u - v * u ^ 2 / 2))
    ((dh s - (m + v * s) * h s) * exp (-m * s - v * s ^ 2 / 2)).
Proof.
intros Hh.
assert (Hp : @is_derive R R^o R^o s 1 (fun u => -m * u - v * u ^ 2 / 2) (-m - v * s)).
{ auto_derive; [lra|simpl; field]. }
pose proof (is_derive_exp_comp (fun u => -m * u - v * u ^ 2 / 2) s (-m - v * s) Hp) as HE.
pose proof (is_derive_mult h (fun u => exp (-m * u - v * u ^ 2 / 2))
  s (dh s) (exp (-m * s - v * s ^ 2 / 2) * (-m - v * s)) Hh HE) as H.
replace ((dh s - (m + v * s) * h s) * exp (-m * s - v * s ^ 2 / 2)) with
  (dh s * exp (-m * s - v * s ^ 2 / 2) + h s * (exp (-m * s - v * s ^ 2 / 2) * (-m - v * s))) by ring.
exact H.
Qed.

Lemma paper_main_gaussian_mgf_ode_bound h dh m v :
  h 0 = 1 ->
  (forall s, 0 <= s -> @is_derive R R^o R^o s 1 h (dh s)) ->
  (forall s, 0 <= s -> dh s <= (m + v * s) * h s) ->
  forall t, 0 <= t -> h t <= exp (m * t + v * t ^ 2 / 2).
Proof.
intros H0 HD Hbound t Ht.
destruct (Req_dec t 0) as [->|Ht0].
- rewrite H0; replace (m * 0 + v * 0 ^ 2 / 2) with 0 by field; rewrite exp_0; apply Rle_refl.
- assert (Htpos : 0 < t) by lra.
  set (q := fun u => h u * exp (-m * u - v * u ^ 2 / 2)).
  set (dq := fun u => (dh u - (m + v * u) * h u) * exp (-m * u - v * u ^ 2 / 2)).
  assert (HDq : forall u, 0 <= u -> @is_derive R R^o R^o u 1 q (dq u)).
  { intros u Hu; apply paper_main_gaussian_integrating_factor_derivative; apply HD; exact Hu. }
  assert (Hsg : forall u, 0 <= u -> dq u <= 0).
  { intros u Hu; unfold dq; specialize (Hbound u Hu).
    pose proof (exp_pos (-m * u - v * u ^ 2 / 2)); nra. }
  assert (Hmin : Rmin 0 t = 0) by (apply Rmin_left; lra).
  assert (Hmax : Rmax 0 t = t) by (apply Rmax_right; lra).
  destruct (MVT_gen q 0 t dq) as [c [Hc Heq]].
  + intros u Hu; rewrite Hmin Hmax in Hu; apply HDq; lra.
  + intros u Hu; rewrite Hmin Hmax in Hu.
    apply (proj2 (continuity_pt_filterlim q u)).
    exact (is_derive_continuous q u (dq u) (HDq u ltac:(lra))).
  + rewrite Hmin Hmax in Hc.
    pose proof (Hsg c ltac:(lra)) as Hdc.
    assert (Hmono : q t <= q 0) by nra.
    unfold q in Hmono; rewrite H0 in Hmono.
    replace (-m * 0 - v * 0 ^ 2 / 2) with 0 in Hmono by field.
    rewrite exp_0 Rmult_1_l in Hmono.
    apply (Rmult_le_reg_r (exp (-m * t - v * t ^ 2 / 2))); [apply exp_pos|].
    rewrite <- exp_plus.
    replace (m * t + v * t ^ 2 / 2 + (-m * t - v * t ^ 2 / 2)) with 0 by field.
    rewrite exp_0; exact Hmono.
Qed.

Lemma paper_main_gaussian_mgf_zero d (f : list R -> R) :
  gaussian_iterated_expectation d (fun xs => exp (0 * f xs)) = 1.
Proof.
transitivity (gaussian_iterated_expectation d (fun _ => 1)).
- apply gaussian_iterated_expectation_ext; intros xs Hxs; rewrite Rmult_0_l exp_0; reflexivity.
- exact (proj2 (gaussian_iterated_constant d 1)).
Qed.

Theorem paper_main_gaussian_bounded_mgf_bound d f Df D2f M L t :
  paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  (forall xs, List.length xs = d ->
    finite_sum (fun a => Df a xs ^ 2) (List.seq 0 d) <= L ^ 2) ->
  0 <= t ->
  gaussian_iterated_expectation d (fun xs => exp (t * f xs)) <=
    exp (t * gaussian_iterated_expectation d f + t ^ 2 * L ^ 2 / 2).
Proof.
intros Hsmooth Hgrad Ht.
replace (t * gaussian_iterated_expectation d f + t ^ 2 * L ^ 2 / 2) with
  (gaussian_iterated_expectation d f * t + L ^ 2 * t ^ 2 / 2) by field.
apply (paper_main_gaussian_mgf_ode_bound
  (fun s => gaussian_iterated_expectation d (fun xs => exp (s * f xs)))
  (fun s => gaussian_iterated_expectation d (fun xs => f xs * exp (s * f xs)))
  (gaussian_iterated_expectation d f) (L ^ 2)).
- apply paper_main_gaussian_mgf_zero.
- intros s Hs; exact (proj1 (paper_main_gaussian_bounded_mgf_differential d f Df D2f M L Hsmooth Hgrad s Hs)).
- intros s Hs; pose proof (proj2 (paper_main_gaussian_bounded_mgf_differential d f Df D2f M L Hsmooth Hgrad s Hs)); nra.
- exact Ht.
Qed.

Theorem paper_main_gaussian_bounded_centered_mgf d f Df D2f M L t :
  paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  (forall xs, List.length xs = d ->
    finite_sum (fun a => Df a xs ^ 2) (List.seq 0 d) <= L ^ 2) ->
  0 <= t ->
  gaussian_iterated_expectation d
    (fun xs => exp (t * (f xs - gaussian_iterated_expectation d f))) <=
    exp (t ^ 2 * L ^ 2 / 2).
Proof.
intros Hsmooth Hgrad Ht.
pose proof (paper_main_gaussian_exp_smooth d t f Df D2f M Ht Hsmooth) as HE.
destruct HE as [HEc HED HEDc HED2 HED2c HEb HEDb HED2b].
pose proof (proj1 (gaussian_coordinate_polynomial_domain d
  (paper_main_gaussian_exp_test t f) (paper_main_gaussian_exp_constant t M) 0 HEc HEb)) as Hint.
assert (Hshift : gaussian_iterated_expectation d
  (fun xs => exp (t * (f xs - gaussian_iterated_expectation d f))) =
  exp (-t * gaussian_iterated_expectation d f) *
    gaussian_iterated_expectation d (fun xs => exp (t * f xs))).
{ transitivity (gaussian_iterated_expectation d (fun xs =>
    exp (-t * gaussian_iterated_expectation d f) * exp (t * f xs))).
  - apply gaussian_iterated_expectation_ext; intros xs Hxs.
    rewrite <- exp_plus; f_equal; ring.
  - exact (proj2 (gaussian_iterated_scale d (fun xs => exp (t * f xs))
      (exp (-t * gaussian_iterated_expectation d f)) Hint)). }
rewrite Hshift.
replace (exp (t ^ 2 * L ^ 2 / 2)) with
  (exp (-t * gaussian_iterated_expectation d f) *
    exp (t * gaussian_iterated_expectation d f + t ^ 2 * L ^ 2 / 2)).
- apply Rmult_le_compat_l; [apply Rlt_le, exp_pos|].
  exact (paper_main_gaussian_bounded_mgf_bound d f Df D2f M L t Hsmooth Hgrad Ht).
- rewrite <- exp_plus; f_equal; field.
Qed.
