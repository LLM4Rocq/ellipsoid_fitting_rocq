(* Linearity and order properties of the Gaussian integral and expectation
   on the line (GaussianDefinitions). gaussian_has_integral f l says that
   f * gaussian_kernel is Lebesgue integrable on the line with integral l;
   gaussian_integral_exists f is the integrability alone. The module
   proves the uniqueness of the value, rules for scaling, sums, differences
   and constants (gaussian_expectation_of_constant: the expectation of c is
   c), and gaussian_expectation_nonnegative, gaussian_expectation_monotone
   and gaussian_expectation_absolute_bound, |E f| <= E |f|. The hypothesis
   gaussian_absolutely_integrable f of the last one is not used: it
   follows from gaussian_integral_exists f. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import GaussianKernel GaussianMass GaussianFubiniLebesgue.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_integral_unique f l :
  gaussian_has_integral f l -> gaussian_integral f = l.
Proof. by move=> [_ Hl]. Qed.

Lemma gaussian_integral_correct f :
  gaussian_integral_exists f -> gaussian_has_integral f (gaussian_integral f).
Proof. by move=> Hf; split. Qed.

Lemma gaussian_has_integral_scale f l c :
  gaussian_has_integral f l ->
  gaussian_has_integral (fun x => c * f x) (c * l).
Proof.
  move=> [Hi Hl].
  have E : (fun x => c * f x * gaussian_kernel x) =
      (fun x => c * (f x * gaussian_kernel x)).
  { apply/funext => x; ring. }
  rewrite /gaussian_has_integral /whole_line_has_integral E.
  split.
  - exact: (fubini_integrable_scale setT _ c measurableT Hi).
  - rewrite (fubini_integral_scale_l _ c Hi).
    by unfold gaussian_integral in Hl; rewrite Hl.
Qed.

Lemma gaussian_has_integral_add f g lf lg :
  gaussian_has_integral f lf -> gaussian_has_integral g lg ->
  gaussian_has_integral (fun x => f x + g x) (lf + lg).
Proof.
  move=> [Hf Hlf] [Hg Hlg].
  have E : (fun x => (f x + g x) * gaussian_kernel x) =
      (fun x => f x * gaussian_kernel x + g x * gaussian_kernel x).
  { apply/funext => x; ring. }
  rewrite /gaussian_has_integral /whole_line_has_integral E.
  split.
  - apply: (eq_integrable measurableT _ _ _ (integrableD measurableT Hf Hg)).
    by move=> y _ /=; rewrite -EFinD -RplusE.
  - rewrite /whole_line_integral (RintegralD measurableT Hf Hg).
    unfold gaussian_integral, whole_line_integral in Hlf, Hlg.
    by rewrite Hlf Hlg -RplusE.
Qed.

Lemma gaussian_has_integral_sub f g lf lg :
  gaussian_has_integral f lf -> gaussian_has_integral g lg ->
  gaussian_has_integral (fun x => f x - g x) (lf - lg).
Proof.
  move=> [Hf Hlf] [Hg Hlg].
  have E : (fun x => (f x - g x) * gaussian_kernel x) =
      (fun x => f x * gaussian_kernel x - g x * gaussian_kernel x).
  { apply/funext => x; ring. }
  rewrite /gaussian_has_integral /whole_line_has_integral E.
  split.
  - apply: (eq_integrable measurableT _ _ _ (integrableB measurableT Hf Hg)).
    by move=> y _ /=; rewrite -EFinB -RminusE.
  - rewrite /whole_line_integral (RintegralB measurableT Hf Hg).
    unfold gaussian_integral, whole_line_integral in Hlf, Hlg.
    by rewrite Hlf Hlg -RminusE.
Qed.

Lemma gaussian_integral_scale f c :
  gaussian_integral_exists f ->
  gaussian_integral (fun x => c * f x) = c * gaussian_integral f.
Proof.
  intro Hf; apply gaussian_integral_unique.
  apply gaussian_has_integral_scale; apply gaussian_integral_correct; exact Hf.
Qed.

Lemma gaussian_integral_add f g :
  gaussian_integral_exists f -> gaussian_integral_exists g ->
  gaussian_integral (fun x => f x + g x) = gaussian_integral f + gaussian_integral g.
Proof.
  intros Hf Hg; apply gaussian_integral_unique.
  apply gaussian_has_integral_add; apply gaussian_integral_correct; assumption.
Qed.

Lemma gaussian_integral_sub f g :
  gaussian_integral_exists f -> gaussian_integral_exists g ->
  gaussian_integral (fun x => f x - g x) = gaussian_integral f - gaussian_integral g.
Proof.
  intros Hf Hg; apply gaussian_integral_unique.
  apply gaussian_has_integral_sub; apply gaussian_integral_correct; assumption.
Qed.

Lemma gaussian_expectation_scale f c :
  gaussian_integral_exists f ->
  gaussian_expectation (fun x => c * f x) = c * gaussian_expectation f.
Proof.
  intro Hf; unfold gaussian_expectation; rewrite (gaussian_integral_scale f c Hf).
  unfold Rdiv; ring.
Qed.

Lemma gaussian_expectation_add f g :
  gaussian_integral_exists f -> gaussian_integral_exists g ->
  gaussian_expectation (fun x => f x + g x) = gaussian_expectation f + gaussian_expectation g.
Proof.
  intros Hf Hg; unfold gaussian_expectation; rewrite (gaussian_integral_add f g Hf Hg).
  unfold Rdiv; ring.
Qed.

Lemma gaussian_expectation_sub f g :
  gaussian_integral_exists f -> gaussian_integral_exists g ->
  gaussian_expectation (fun x => f x - g x) = gaussian_expectation f - gaussian_expectation g.
Proof.
  intros Hf Hg; unfold gaussian_expectation; rewrite (gaussian_integral_sub f g Hf Hg).
  unfold Rdiv; ring.
Qed.

(* Constants. The integrability of the kernel is a hypothesis of the first
   three lemmas; gaussian_expectation_of_constant discharges it with
   gaussian_kernel_integrable. *)
Lemma gaussian_has_integral_constant c :
  whole_line_integrable gaussian_kernel ->
  gaussian_has_integral (fun _ => c) (c * gaussian_mass).
Proof.
  move=> Hk; rewrite /gaussian_has_integral /whole_line_has_integral.
  split.
  - exact: (fubini_integrable_scale setT _ c measurableT Hk).
  - by rewrite /gaussian_mass (fubini_integral_scale_l _ c Hk).
Qed.

Lemma gaussian_integral_constant c :
  whole_line_integrable gaussian_kernel ->
  gaussian_integral (fun _ => c) = c * gaussian_mass.
Proof.
  intro Hk; apply gaussian_integral_unique; apply gaussian_has_integral_constant.
  exact Hk.
Qed.

Lemma gaussian_expectation_constant c :
  whole_line_integrable gaussian_kernel ->
  gaussian_mass <> 0 -> gaussian_expectation (fun _ => c) = c.
Proof.
  intros Hk Hm; unfold gaussian_expectation; rewrite (gaussian_integral_constant c Hk).
  field; exact Hm.
Qed.

Theorem gaussian_expectation_of_constant c : gaussian_expectation (fun _ => c) = c.
Proof.
  apply gaussian_expectation_constant; [exact gaussian_kernel_integrable|].
  pose proof gaussian_mass_positive; lra.
Qed.

Lemma gaussian_integral_exists_scale f c :
  gaussian_integral_exists f -> gaussian_integral_exists (fun x => c * f x).
Proof.
  move=> Hf.
  exact: (proj1 (gaussian_has_integral_scale f _ c (gaussian_integral_correct f Hf))).
Qed.

Lemma gaussian_integral_exists_add f g :
  gaussian_integral_exists f -> gaussian_integral_exists g ->
  gaussian_integral_exists (fun x => f x + g x).
Proof.
  move=> Hf Hg.
  exact: (proj1 (gaussian_has_integral_add f g _ _
    (gaussian_integral_correct f Hf) (gaussian_integral_correct g Hg))).
Qed.

Lemma gaussian_integral_exists_sub f g :
  gaussian_integral_exists f -> gaussian_integral_exists g ->
  gaussian_integral_exists (fun x => f x - g x).
Proof.
  move=> Hf Hg.
  exact: (proj1 (gaussian_has_integral_sub f g _ _
    (gaussian_integral_correct f Hf) (gaussian_integral_correct g Hg))).
Qed.

Lemma gaussian_has_integral_nonnegative f l :
  (forall x, 0 <= f x) -> gaussian_has_integral f l -> 0 <= l.
Proof.
  move=> Hf [_ Hl].
  rewrite -Hl /whole_line_integral.
  apply/RleP; apply: Rintegral_ge0 => x _.
  apply/RleP; apply Rmult_le_pos; [apply Hf|left; apply exp_pos].
Qed.

Theorem gaussian_expectation_nonnegative f :
  gaussian_integral_exists f -> (forall x, 0 <= f x) ->
  0 <= gaussian_expectation f.
Proof.
  intros Hf Hpos; unfold gaussian_expectation.
  apply Rdiv_le_0_compat.
  - exact (gaussian_has_integral_nonnegative f (gaussian_integral f)
      Hpos (gaussian_integral_correct f Hf)).
  - exact gaussian_mass_positive.
Qed.

Theorem gaussian_expectation_monotone f g :
  gaussian_integral_exists f -> gaussian_integral_exists g ->
  (forall x, f x <= g x) -> gaussian_expectation f <= gaussian_expectation g.
Proof.
  intros Hf Hg Hfg.
  assert (H : 0 <= gaussian_expectation (fun x => g x - f x)).
  { apply gaussian_expectation_nonnegative.
    - apply gaussian_integral_exists_sub; assumption.
    - intro x; specialize (Hfg x); lra. }
  rewrite (gaussian_expectation_sub g f Hg Hf) in H; lra.
Qed.

Theorem gaussian_expectation_absolute_bound f :
  gaussian_integral_exists f -> gaussian_absolutely_integrable f ->
  Rabs (gaussian_expectation f) <= gaussian_expectation (fun x => Rabs (f x)).
Proof.
  intros Hf Habs.
  have H := fubini_Rintegral_abs_le setT (fun x => f x * gaussian_kernel x)
    measurableT Hf.
  have E : (fun y => Rabs (f y * gaussian_kernel y)) =
      (fun y => Rabs (f y) * gaussian_kernel y).
  { apply/funext => y.
    have Hk0 : gaussian_kernel y >= 0 by left; apply exp_pos.
    by rewrite Rabs_mult (Rabs_right _ Hk0). }
  rewrite E in H.
  change (Rabs (gaussian_integral f) <= gaussian_integral (fun x => Rabs (f x))) in H.
  pose proof gaussian_mass_positive as HM.
  unfold gaussian_expectation, Rdiv.
  have HM0 : gaussian_mass >= 0 by lra.
  rewrite Rabs_mult Rabs_inv (Rabs_right _ HM0).
  apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact HM|exact H].
Qed.

Lemma gaussian_has_integral_exists f l :
  gaussian_has_integral f l -> gaussian_integral_exists f.
Proof. by move=> [Hi _]. Qed.

Lemma gaussian_integral_exists_constant c :
  gaussian_integral_exists (fun _ => c).
Proof.
  exact: (gaussian_has_integral_exists _ _
    (gaussian_has_integral_constant c gaussian_kernel_integrable)).
Qed.
