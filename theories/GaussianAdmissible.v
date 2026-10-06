(* Integrability against the Gaussian kernel of continuous functions of
   polynomial growth. If f is continuous and
   Rabs (f x) <= C * (1 + Rabs x ^ p) for all x, then
   f x * gaussian_kernel x and Rabs (f x) * gaussian_kernel x are
   integrable on the line (gaussian_polynomial_integrals_exist): these are
   gaussian_integral_exists f and gaussian_absolutely_integrable f of
   GaussianDefinitions. The integrals are Lebesgue integrals, so the second
   conclusion also follows from the first.

   The proof dominates f x * gaussian_kernel x by
   C * (2 + x ^ (p + p)) * gaussian_kernel x (gaussian_even_power_majorant),
   whose integral over the line is computed from gaussian_mass and the even
   moment moment_factor (p + p) (gaussian_polynomial_majorant_integral).
   The statements write (p+p)%coq_nat, Stdlib's Nat.add, because with
   ssreflect loaded p+p would be ssrnat's addn. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge.
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
