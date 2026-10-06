(* The centered chi-square variable gaussian_sum_squares xs - INR d, for d
   independent standard Gaussian coordinates. For t < 1/2 its exponential
   moment is exp (-t * INR d) * (1 / sqrt (1-2*t)) ^ d
   (gaussian_centered_chisquare_exponential_moment). Its logarithm is
   INR d / 2 * (-2*t - ln (1-2*t)) (gaussian_centered_chisquare_log_moment)
   and is at most INR d * t * t / (1-2*t) when 0 <= t
   (gaussian_centered_chisquare_log_bound). The logarithm is written
   Rpower.ln, Stdlib's, so that the statements keep their meaning where
   MathComp's exp module makes a bare ln mean exp.ln. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Gaussian.ChiSquareMoments Radius.ScalarInequalities.
Import ListNotations.
Open Scope R_scope.

Theorem gaussian_centered_chisquare_exponential_moment d t :
  t < 1/2 ->
  gaussian_iterated_integrable d
    (fun xs => exp (t * (gaussian_sum_squares xs - INR d))) /\
  gaussian_iterated_absolutely_integrable d
    (fun xs => exp (t * (gaussian_sum_squares xs - INR d))) /\
  gaussian_iterated_has_expectation d
    (fun xs => exp (t * (gaussian_sum_squares xs - INR d)))
    (exp (-t * INR d) * (1 / sqrt (1-2*t)) ^ d) /\
  gaussian_iterated_expectation d
    (fun xs => exp (t * (gaussian_sum_squares xs - INR d))) =
    exp (-t * INR d) * (1 / sqrt (1-2*t)) ^ d.
Proof.
  intro Ht.
  destruct (gaussian_chisquare_exponential_moment d t Ht) as [HI [HA [HV HE]]].
  destruct (gaussian_iterated_scale d _ (exp (-t * INR d)) HI) as [HSI HSE].
  assert (Hext : forall xs, length xs = d ->
    exp (-t * INR d) * exp (t * gaussian_sum_squares xs) =
      exp (t * (gaussian_sum_squares xs - INR d))).
  { intros xs Hxs; rewrite <- exp_plus; f_equal; ring. }
  assert (HCI : gaussian_iterated_integrable d
    (fun xs => exp (t * (gaussian_sum_squares xs - INR d)))).
  { apply gaussian_iterated_integrable_ext with
      (F := fun xs => exp (-t * INR d) * exp (t * gaussian_sum_squares xs)); assumption. }
  assert (HCE : gaussian_iterated_expectation d
    (fun xs => exp (t * (gaussian_sum_squares xs - INR d))) =
    exp (-t * INR d) * (1 / sqrt (1-2*t)) ^ d).
  { rewrite <- (gaussian_iterated_expectation_ext d _ _ Hext), HSE, HE; reflexivity. }
  split; [exact HCI |].
  split.
  - unfold gaussian_iterated_absolutely_integrable.
    apply gaussian_iterated_integrable_ext with
      (F := fun xs => exp (t * (gaussian_sum_squares xs - INR d))); [|exact HCI].
    intros xs Hxs; symmetry; apply Rabs_pos_eq, Rlt_le, exp_pos.
  - split; [rewrite <- HCE; apply gaussian_iterated_has_expectation_correct; exact HCI |exact HCE].
Qed.

Theorem gaussian_centered_chisquare_log_moment d t :
  t < 1/2 ->
  Rpower.ln (gaussian_iterated_expectation d
    (fun xs => exp (t * (gaussian_sum_squares xs - INR d)))) =
    INR d / 2 * (-2*t - Rpower.ln (1-2*t)).
Proof.
  intro Ht.
  destruct (gaussian_centered_chisquare_exponential_moment d t Ht) as [HI [HA [HV HE]]].
  rewrite HE.
  assert (Hs : 0 < sqrt (1-2*t)) by (apply sqrt_lt_R0; lra).
  assert (Hq : 0 < 1 / sqrt (1-2*t)) by (apply Rdiv_lt_0_compat; lra).
  rewrite ln_mult by (try apply exp_pos; apply pow_lt; exact Hq).
  rewrite ln_exp, ln_pow by exact Hq.
  assert (Hinv : Rpower.ln (1 / sqrt (1-2*t)) = - Rpower.ln (sqrt (1-2*t))).
  { unfold Rdiv; rewrite Rmult_1_l; apply ln_Rinv; exact Hs. }
  rewrite Hinv.
  pose proof (ln_mult (sqrt (1-2*t)) (sqrt (1-2*t)) Hs Hs) as Hlog.
  rewrite (sqrt_def (1-2*t) ltac:(lra)) in Hlog.
  nra.
Qed.

Theorem gaussian_centered_chisquare_log_bound d t :
  0 <= t < 1/2 ->
  Rpower.ln (gaussian_iterated_expectation d
    (fun xs => exp (t * (gaussian_sum_squares xs - INR d)))) <=
    INR d * t * t / (1-2*t).
Proof.
  intro Ht.
  rewrite gaussian_centered_chisquare_log_moment by lra.
  apply gaussian_centered_log_expression_bound; [apply pos_INR |exact Ht].
Qed.
