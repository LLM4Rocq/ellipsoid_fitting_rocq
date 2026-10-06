(* The expected maximum squared radius of N rows of d standard Gaussian
   coordinates. One row has expected squared radius d
   (gaussian_sum_squares_expectation, gaussian_maximum_radius_single).
   gaussian_maximum_radius_parameter_bound: for 0 < t < 1/2 the expected
   maximum is at most d + ln N / t + d t / (1 - 2 t), by Jensen's
   inequality and the moment generating function of the centered
   chi-square law. gaussian_maximum_radius_expected_bound: for a suitable
   t, it is at most d + 2 sqrt (d ln N) + 2 ln N. The logarithm is
   Stdlib's natural logarithm, written Rpower.ln to tell it apart from
   MathComp's exp.ln. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions Gaussian.Expectation
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Gaussian.CoordinateWeightDefinitions Gaussian.CoordinateMarginals
  Gaussian.PolynomialGrowthIntegrals Gaussian.CenteredChiSquare
  Gaussian.ExponentialJensen Radius.ScalarInequalities Radius.Definitions
  Radius.Regularity Radius.ExponentialMoments.
Import ListNotations.
Open Scope R_scope.

Theorem gaussian_maximum_radius_parameter_bound N d t :
  (0<N)%nat -> 0<t<1/2 ->
  gaussian_iterated_expectation (N*d) (gaussian_maximum_radius N d) <=
    INR d + Rpower.ln (INR N)/t + INR d*t/(1-2*t).
Proof.
  intros HN Ht.
  pose proof (proj1 (gaussian_maximum_radius_domain N d)) as HM.
  destruct (gaussian_iterated_constant (N*d) (-INR d)) as [HC HCE].
  destruct (gaussian_iterated_add (N*d) (gaussian_maximum_radius N d)
    (fun _ => -INR d) HM HC) as [HCI HCIE].
  destruct (gaussian_radius_exponential_sum_moment N d t ltac:(lra)) as [HG HGE].
  pose proof (gaussian_iterated_log_majorant_bound (N*d)
    (fun xs => gaussian_maximum_radius N d xs - INR d)
    (gaussian_radius_exponential_sum N d t) t ltac:(lra) HCI HG) as HB.
  assert (Hexp : forall xs, length xs=(N*d)%nat ->
    exp (t*(gaussian_maximum_radius N d xs-INR d)) <=
      gaussian_radius_exponential_sum N d t xs).
  { intros xs Hxs; apply gaussian_maximum_radius_exponential_majorant; [exact HN|lra]. }
  specialize (HB Hexp).
  change (gaussian_iterated_expectation (N*d)
    (fun xs => gaussian_maximum_radius N d xs + -INR d) <=
      Rpower.ln (gaussian_iterated_expectation (N*d) (gaussian_radius_exponential_sum N d t))/t) in HB.
  rewrite HCIE, HCE, HGE in HB.
  assert (HNpos : 0<INR N) by (apply lt_0_INR; exact HN).
  assert (HZpos : 0<gaussian_iterated_expectation d
      (fun xs => exp (t*(gaussian_sum_squares xs-INR d)))).
  { destruct (gaussian_centered_chisquare_exponential_moment d t ltac:(lra))
      as [_ [_ [_ HE]]]; rewrite HE.
    apply Rmult_lt_0_compat; [apply exp_pos|apply pow_lt].
    apply Rdiv_lt_0_compat; [lra|apply sqrt_lt_R0; lra]. }
  rewrite ln_mult in HB by assumption.
  pose proof (gaussian_centered_chisquare_log_bound d t ltac:(lra)) as HL.
  assert (Hfrac : Rpower.ln (gaussian_iterated_expectation d
      (fun xs => exp (t*(gaussian_sum_squares xs-INR d)))) / t <=
      INR d*t/(1-2*t)).
  { apply (Rmult_le_reg_r t); [lra|].
    replace (Rpower.ln (gaussian_iterated_expectation d
      (fun xs => exp (t*(gaussian_sum_squares xs-INR d))))/t*t) with
      (Rpower.ln (gaussian_iterated_expectation d
        (fun xs => exp (t*(gaussian_sum_squares xs-INR d))))) by (field; lra).
    replace (INR d*t/(1-2*t)*t) with (INR d*t*t/(1-2*t)) by (field; lra).
    exact HL. }
  unfold Rdiv in HB, Hfrac |- *; nra.
Qed.

Lemma maximum_radius_squares_integrable d :
  gaussian_iterated_integrable d gaussian_sum_squares.
Proof.
  apply (gaussian_iterated_polynomial_integrable d gaussian_sum_squares (INR d) 2).
  - apply maximum_radius_squares_continuous.
  - split; [apply pos_INR|].
    intros xs Hxs; rewrite Rabs_pos_eq by apply maximum_radius_squares_nonnegative.
    rewrite <- Hxs; apply maximum_radius_squares_polynomial.
Qed.

Theorem gaussian_sum_squares_expectation d :
  gaussian_iterated_expectation d gaussian_sum_squares = INR d.
Proof.
  induction d as [|d IH]; [reflexivity|].
  change (gaussian_expectation (fun x =>
    gaussian_iterated_expectation d (fun xs => x*x+gaussian_sum_squares xs)) = INR (S d)).
  assert (HE : forall x, gaussian_iterated_expectation d
    (fun xs => x*x+gaussian_sum_squares xs) = x*x+INR d).
  { intro x; destruct (gaussian_iterated_constant d (x*x)) as [HC HCE].
    rewrite (proj2 (gaussian_iterated_add d (fun _ => x*x) gaussian_sum_squares
      HC (maximum_radius_squares_integrable d))), HCE, IH; reflexivity. }
  assert (Hfun : (fun x => gaussian_iterated_expectation d
    (fun xs => x*x+gaussian_sum_squares xs)) = (fun x => x^2+INR d)).
  { apply functional_extensionality; intro x; rewrite HE; simpl; ring. }
  rewrite Hfun, gaussian_expectation_add.
  - rewrite gaussian_expectation_of_constant, (proj1 (proj2 (proj2 gaussian_standard_moments))), S_INR; ring.
  - exact (proj1 (proj2 (gaussian_power_moments 2))).
  - exact (proj2 (proj1 (gaussian_iterated_constant 1 (INR d)))).
Qed.

Theorem gaussian_maximum_radius_single d :
  gaussian_iterated_expectation (1*d) (gaussian_maximum_radius 1 d) = INR d.
Proof.
  replace (1*d)%nat with d by lia.
  transitivity (gaussian_iterated_expectation d gaussian_sum_squares).
  - apply gaussian_iterated_expectation_ext; intros xs Hxs.
    change (Rmax (gaussian_sum_squares (firstn d xs)) 0 = gaussian_sum_squares xs).
    rewrite <- Hxs, firstn_all, Rmax_left by apply maximum_radius_squares_nonnegative.
    reflexivity.
  - apply gaussian_sum_squares_expectation.
Qed.

Theorem gaussian_maximum_radius_expected_bound N d :
  (0<N)%nat -> (0<d)%nat ->
  gaussian_iterated_expectation (N*d) (gaussian_maximum_radius N d) <=
    INR d + 2*sqrt (INR d * Rpower.ln (INR N)) + 2*Rpower.ln (INR N).
Proof.
  intros HN Hd; destruct (Nat.eq_dec N 1) as [->|HN1].
  - rewrite gaussian_maximum_radius_single; simpl INR; rewrite ln_1, Rmult_0_r, sqrt_0; lra.
  - assert (HD : 0<INR d) by (apply lt_0_INR; exact Hd).
    assert (HL : 0<Rpower.ln (INR N)).
    { pose proof (lt_INR 1 N ltac:(lia)) as H.
      pose proof (ln_increasing 1 (INR N) ltac:(lra) H) as HH.
      rewrite ln_1 in HH; exact HH. }
    destruct (gaussian_radius_parameter (INR d) (Rpower.ln (INR N)) HD HL) as [Ht HE].
    pose proof (gaussian_maximum_radius_parameter_bound N d
      (sqrt (Rpower.ln (INR N))/(sqrt (INR d)+2*sqrt (Rpower.ln (INR N)))) HN Ht) as HB.
    lra.
Qed.
