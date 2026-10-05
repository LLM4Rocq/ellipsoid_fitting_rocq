(* Port of theories/GaussianAdmissible.v from Coquelicot to MathComp-Analysis.

   Every lemma, theorem and corollary of the original keeps its name and its
   arguments, in the same order, and no statement gains or loses a
   hypothesis. The statements use the vocabulary of
   AnalysisIntegralDefinitions:
   - continuous f x becomes {for x, continuous f} (difference 5 of
     analysis/README.md), with the binder written x : R, as in the
     restated challenges;
   - is_RInt_gen h (Rbar_locally m_infty) (Rbar_locally p_infty) l becomes
     whole_line_has_integral h l, and
     ex_RInt_gen h (Rbar_locally m_infty) (Rbar_locally p_infty) becomes
     whole_line_integrable h, the Lebesgue integral over the line
     (difference 4 of analysis/README.md).
   The arithmetic in every statement is Stdlib's, as in the original.

   Addition on nat. With ssreflect loaded, p+p would elaborate to ssrnat's
   addn p p. The statements write (p+p)%coq_nat, which is Stdlib's
   Nat.add p p, as in the original and as in the restated challenge
   ellipsoid_gaussian_parameter (analysis/challenges). The two are
   convertible.

   Meaning. Every integrand here is a continuous function bounded in
   absolute value by a polynomial times the Gaussian kernel. Such a function
   is Borel measurable and absolutely integrable, so the Lebesgue and the
   improper Riemann readings both hold and give the same value. With the
   Lebesgue integral the second conclusion of
   gaussian_polynomial_integrals_exist follows from the first; it is kept.
   The two conclusions of gaussian_polynomial_integrals_exist are, by
   conversion, gaussian_integral_exists f and
   gaussian_absolutely_integrable f of the ported GaussianDefinitions, as
   they were in the original.

   What changes in the proofs. gaussian_polynomial_majorant_integral builds
   the integral of C * (2 + x^(p+p)) * gaussian_kernel x from the mass of the
   kernel (gaussian_kernel_mass_integral of GaussianMass) and the raw moment
   (gaussian_raw_moments of GaussianMoments) with MathComp's integrableD and
   RintegralD, and fubini_integrable_scale and fubini_integral_scale_l of
   GaussianFubiniLebesgue, in place of Coquelicot's is_RInt_gen_scal,
   is_RInt_gen_plus and is_RInt_gen_ext. The continuity arguments use
   continuous_mult, continuous_plus and continuous_const of the bridge. The
   domination lemmas are those of the ported ImproperDomination.

   The original imported Classical_Prop but did not use it. This port does
   not import it, and the assumptions of the module are the seven axioms of
   analysis/README.md. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianKernel GaussianMass GaussianMoments
  GaussianSteinPolynomial ImproperBounds ImproperDomination.
From EllipsoidFitting Require Import GaussianFubiniLebesgue.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_even_power_majorant x p :
  Rabs x ^ p <= 1 + x ^ (p+p)%coq_nat.
Proof.
  rewrite RPow_abs pow_add.
  destruct (Rle_dec 0 (x^p)) as [Hpos|Hneg].
  - rewrite (Rabs_pos_eq _ Hpos); nra.
  - rewrite Rabs_left; [lra | nra].
Qed.

Lemma gaussian_polynomial_majorant_integral C p :
  whole_line_has_integral
    (fun x => C * (2 + x ^ (p+p)%coq_nat) * gaussian_kernel x)
    (C * (2 + moment_factor (p+p)%coq_nat) * gaussian_mass).
Proof.
  destruct gaussian_kernel_mass_integral as [Hk Hkv].
  destruct (gaussian_raw_moments gaussian_mass gaussian_kernel_mass_integral
    (p+p)%coq_nat) as [Hp Hpv].
  have H2 := fubini_integrable_scale setT gaussian_kernel 2 measurableT Hk.
  have Hs : whole_line_integrable
      (fun x => 2 * gaussian_kernel x + x ^ (p+p)%coq_nat * gaussian_kernel x).
  { apply: (eq_integrable measurableT _ _ _ (integrableD measurableT H2 Hp)).
    by move=> y _ /=; rewrite -EFinD -RplusE. }
  have Hsv : whole_line_integral
      (fun x => 2 * gaussian_kernel x + x ^ (p+p)%coq_nat * gaussian_kernel x) =
    2 * gaussian_mass + moment_factor (p+p)%coq_nat * gaussian_mass.
  { rewrite /whole_line_integral (RintegralD measurableT H2 Hp).
    change (whole_line_integral (fun y => 2 * gaussian_kernel y) +
      whole_line_integral (fun x => x ^ (p+p)%coq_nat * gaussian_kernel x) =
      2 * gaussian_mass + moment_factor (p+p)%coq_nat * gaussian_mass)%R.
    rewrite (fubini_integral_scale_l gaussian_kernel 2 Hk) Hpv -RplusE.
    by unfold gaussian_mass. }
  have E : (fun x => C * (2 + x ^ (p+p)%coq_nat) * gaussian_kernel x) =
      (fun x => C * (2 * gaussian_kernel x +
        x ^ (p+p)%coq_nat * gaussian_kernel x)).
  { apply/funext => x; ring. }
  rewrite /whole_line_has_integral E.
  split.
  - exact: (fubini_integrable_scale setT _ C measurableT Hs).
  - rewrite (fubini_integral_scale_l _ C Hs) Hsv; ring.
Qed.

Theorem gaussian_polynomial_integrals_exist (f : R -> R) C p :
  (forall x : R, {for x, continuous f}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  whole_line_integrable (fun x => f x * gaussian_kernel x) /\
  whole_line_integrable (fun x => Rabs (f x) * gaussian_kernel x).
Proof.
  intros HC Hb.
  pose proof (gaussian_polynomial_constant_nonnegative f C p Hb) as HCnonneg.
  set (g := fun x => C * (2 + x^(p+p)%coq_nat) * gaussian_kernel x).
  assert (HG : forall x : R, {for x, continuous g}).
  { intro x; unfold g; apply (continuous_mult R).
    - apply (continuous_mult R).
      + apply (continuous_const R).
      + apply (continuous_plus R).
        * apply (continuous_const R).
        * apply gaussian_power_continuous.
    - apply gaussian_kernel_continuous. }
  assert (HF : forall x : R, {for x, continuous (fun t => f t * gaussian_kernel t)}).
  { intro x; apply (continuous_mult R); [apply HC | apply gaussian_kernel_continuous]. }
  assert (Hbound : forall x, Rabs (f x * gaussian_kernel x) <= g x).
  { intro x.
    pose proof (gaussian_kernel_positive x) as Hk.
    rewrite Rabs_mult (Rabs_pos_eq (gaussian_kernel x) (Rlt_le _ _ Hk)).
    unfold g; apply Rmult_le_compat_r; [apply Rlt_le; exact Hk | ].
    eapply Rle_trans; [apply Hb | ].
    pose proof (gaussian_even_power_majorant x p); nra. }
  assert (HI : whole_line_integrable g).
  { exact (proj1 (gaussian_polynomial_majorant_integral C p)). }
  split.
  - exact (continuous_improper_dominated_integrable _ g HF HG Hbound HI).
  - have E : (fun x => Rabs (f x) * gaussian_kernel x) =
        (fun x => Rabs (f x * gaussian_kernel x)).
    { apply/funext => x.
      pose proof (gaussian_kernel_positive x) as Hk.
      by rewrite Rabs_mult (Rabs_pos_eq (gaussian_kernel x) (Rlt_le _ _ Hk)). }
    rewrite E.
    exact (continuous_improper_dominated_absolute_integrable _ g HF HG Hbound HI).
Qed.

Corollary gaussian_polynomial_integrable (f : R -> R) C p :
  (forall x : R, {for x, continuous f}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  whole_line_integrable (fun x => f x * gaussian_kernel x).
Proof. intros HC Hb; exact (proj1 (gaussian_polynomial_integrals_exist f C p HC Hb)). Qed.

Corollary gaussian_polynomial_absolute_integrable (f : R -> R) C p :
  (forall x : R, {for x, continuous f}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  whole_line_integrable (fun x => Rabs (f x) * gaussian_kernel x).
Proof. intros HC Hb; exact (proj2 (gaussian_polynomial_integrals_exist f C p HC Hb)). Qed.
