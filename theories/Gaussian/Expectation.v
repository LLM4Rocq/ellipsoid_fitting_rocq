(* Linearity and order properties of the Gaussian integral and expectation
   on the line (GaussianDefinitions). gaussian_has_integral f l says that
   f * gaussian_kernel is Lebesgue integrable on the line with integral l;
   gaussian_integral_exists f is the integrability alone. The module
   proves the uniqueness of the value, rules for scaling, sums and
   constants (gaussian_expectation_of_constant: the expectation of c is c),
   and gaussian_expectation_nonnegative, gaussian_expectation_monotone and
   gaussian_expectation_absolute_bound, |E f| <= E |f|. The hypothesis
   gaussian_absolutely_integrable f of the last one is not used: it
   follows from gaussian_integral_exists f.

   Each rule is the corresponding rule of MathComp-Analysis for the
   Lebesgue integral (integrableZl, integrableD, RintegralZl, RintegralD,
   Rintegral_ge0, le_Rintegral, le_normr_Rintegral), applied to
   x |-> f x * gaussian_kernel x; the constants use the integrability of
   the kernel and the positivity of its mass (Gaussian.Mass). *)

From Stdlib Require Import Reals Lra.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import Gaussian.Kernel Gaussian.Mass.
From mathcomp Require Import measurable_realfun.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_integral_unique f l :
  gaussian_has_integral f l -> gaussian_integral f = l.
Proof. by move=> [_ Hl]. Qed.

Lemma gaussian_integral_correct f :
  gaussian_integral_exists f -> gaussian_has_integral f (gaussian_integral f).
Proof. by move=> Hf; split. Qed.

Lemma gaussian_has_integral_exists f l :
  gaussian_has_integral f l -> gaussian_integral_exists f.
Proof. by move=> [Hi _]. Qed.

(* Scaling. *)
Lemma gaussian_integral_exists_scale f c :
  gaussian_integral_exists f -> gaussian_integral_exists (fun x => c * f x).
Proof.
move=> Hf.
apply: (eq_integrable measurableT _ _ _ (integrableZl measurableT c Hf)).
by move=> x _ /=; rewrite -EFinM Rmult_assoc.
Qed.

Lemma gaussian_has_integral_scale f l c :
  gaussian_has_integral f l ->
  gaussian_has_integral (fun x => c * f x) (c * l).
Proof.
move=> [Hi <-]; split; first exact: gaussian_integral_exists_scale.
rewrite /gaussian_integral /whole_line_integral.
under eq_Rintegral do rewrite Rmult_assoc RmultE.
by rewrite (RintegralZl _ measurableT Hi) RmultE.
Qed.

Lemma gaussian_expectation_scale f c :
  gaussian_integral_exists f ->
  gaussian_expectation (fun x => c * f x) = c * gaussian_expectation f.
Proof.
move=> Hf; rewrite /gaussian_expectation.
rewrite (gaussian_integral_unique _ _
  (gaussian_has_integral_scale _ _ c (gaussian_integral_correct f Hf))).
unfold Rdiv; ring.
Qed.

(* Sums. *)
Lemma gaussian_integral_exists_add f g :
  gaussian_integral_exists f -> gaussian_integral_exists g ->
  gaussian_integral_exists (fun x => f x + g x).
Proof.
move=> Hf Hg.
apply: (eq_integrable measurableT _ _ _ (integrableD measurableT Hf Hg)).
by move=> x _ /=; rewrite -EFinD Rmult_plus_distr_r.
Qed.

Lemma gaussian_expectation_add f g :
  gaussian_integral_exists f -> gaussian_integral_exists g ->
  gaussian_expectation (fun x => f x + g x) =
  gaussian_expectation f + gaussian_expectation g.
Proof.
move=> Hf Hg; rewrite /gaussian_expectation /gaussian_integral /whole_line_integral.
under eq_Rintegral do rewrite Rmult_plus_distr_r RplusE.
by rewrite (RintegralD measurableT Hf Hg) !RdivE mulrDl.
Qed.

(* Constants. *)
Lemma gaussian_integral_exists_constant c :
  gaussian_integral_exists (fun _ => c).
Proof.
apply: (eq_integrable measurableT _ _ _
  (integrableZl measurableT c gaussian_kernel_integrable)).
by move=> x _ /=; rewrite -EFinM.
Qed.

Theorem gaussian_expectation_of_constant c : gaussian_expectation (fun _ => c) = c.
Proof.
have := gaussian_mass_positive.
rewrite /gaussian_expectation /gaussian_integral /gaussian_mass /whole_line_integral.
move=> HM; under eq_Rintegral do rewrite /= RmultE.
rewrite (RintegralZl _ measurableT gaussian_kernel_integrable) RdivE mulfK //.
by rewrite lt0r_neq0 //; apply/RltP.
Qed.

(* Order. *)
Theorem gaussian_expectation_nonnegative f :
  gaussian_integral_exists f -> (forall x, 0 <= f x) ->
  0 <= gaussian_expectation f.
Proof.
move=> Hf Hpos; apply: Rdiv_le_0_compat; last exact: gaussian_mass_positive.
apply/RleP; apply: Rintegral_ge0 => x _; apply/RleP.
apply: Rmult_le_pos; [exact: Hpos | exact: Rlt_le (gaussian_kernel_positive x)].
Qed.

Theorem gaussian_expectation_monotone f g :
  gaussian_integral_exists f -> gaussian_integral_exists g ->
  (forall x, f x <= g x) -> gaussian_expectation f <= gaussian_expectation g.
Proof.
move=> Hf Hg Hfg; have HM := gaussian_mass_positive.
apply: Rmult_le_compat_r; first exact: Rlt_le (Rinv_0_lt_compat _ HM).
apply/RleP; apply: le_Rintegral => // x _; apply/RleP.
apply: Rmult_le_compat_r; [exact: Rlt_le (gaussian_kernel_positive x) | exact: Hfg].
Qed.

Theorem gaussian_expectation_absolute_bound f :
  gaussian_integral_exists f -> gaussian_absolutely_integrable f ->
  Rabs (gaussian_expectation f) <= gaussian_expectation (fun x => Rabs (f x)).
Proof.
move=> Hf _; have HM := gaussian_mass_positive.
rewrite /gaussian_expectation (Rabs_div _ _ (Rgt_not_eq _ _ HM)).
rewrite (Rabs_pos_eq gaussian_mass (Rlt_le _ _ HM)).
apply: Rmult_le_compat_r; first exact: Rlt_le (Rinv_0_lt_compat _ HM).
rewrite /gaussian_integral /whole_line_integral.
have := le_normr_Rintegral measurableT Hf; rewrite -RabsE => /RleP /Rle_trans; apply.
right; apply: eq_Rintegral => x _ /=.
by rewrite -RabsE Rabs_mult (Rabs_pos_eq _ (Rlt_le _ _ (gaussian_kernel_positive x))).
Qed.
