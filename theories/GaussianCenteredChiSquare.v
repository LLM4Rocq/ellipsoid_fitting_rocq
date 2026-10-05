(* Port of theories/GaussianCenteredChiSquare.v from Coquelicot to
   MathComp-Analysis.

   The three theorems keep their names, their arguments in the same order,
   and the text of their statements, except that the logarithm is written
   Rpower.ln. It is Stdlib's logarithm, the one that a bare ln denotes in the
   original. This module imports no MathComp module, so a bare ln would also
   mean Rpower.ln here. The qualified name keeps the statements unambiguous
   for importers that load MathComp's exp module, where a bare ln is
   MathComp's exp.ln.

   The iterated operators come from the ported GaussianProductDefinitions,
   where they are stated with the Lebesgue integral over the line (difference
   4 of analysis/README.md). So in gaussian_centered_chisquare_exponential_moment
   the predicates gaussian_iterated_integrable and
   gaussian_iterated_absolutely_integrable ask at each level for Lebesgue
   integrability over the line, and gaussian_iterated_has_expectation for
   Lebesgue integrals against gaussian_density. For t < 1/2 every function
   integrated at a level is a positive constant times
   x |-> exp (t * (x*x)) * gaussian_kernel x, which is continuous, positive
   and absolutely integrable, so the Lebesgue and the improper Riemann
   readings say the same thing and give the same values.

   The proofs are those of the original, with one change. Coquelicot's
   ln_div is not in Stdlib, so the proof of
   gaussian_centered_chisquare_log_moment computes the logarithm of
   1 / sqrt (1-2*t) with Stdlib's ln_Rinv. The Coquelicot import is dropped.

   Assumptions. Stdlib defines Rpower.ln through ln_exists, whose proof uses
   Stdlib.Logic.Classical_Prop.classic, so the two statements that mention
   Rpower.ln carry that axiom besides the seven of analysis/README.md. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions GaussianProduct
  GaussianChiSquare RadiusAlgebra.
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
