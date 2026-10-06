(* Truncation of Gaussian integrals to a symmetric interval [-A, A]
   (gaussian_cutoff_integral and gaussian_cutoff_expectation of
   Gaussian.CutoffDefinitions), for a continuous f with |f| <= C * g and a
   continuous g integrable against the kernel. Then f is integrable
   (gaussian_majorant_integrability); for A >= 0 its truncation error is
   at most C times that of g (gaussian_raw_cutoff_error_bound,
   gaussian_normalized_cutoff_error_bound); the truncated integral tends
   to the integral as A tends to +oo (gaussian_cutoff_integral_limit), and
   the truncated expectations converge uniformly over such f
   (gaussian_uniform_cutoff_convergence). Integrals over the line are
   Lebesgue integrals, which require absolute integrability. *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.CutoffDefinitions Gaussian.Kernel Gaussian.Mass Gaussian.Expectation
  Analysis.SegmentIntegralBounds Analysis.WholeLineDomination
  Analysis.LineIntegralCutoff.
From EllipsoidFitting Require Import Analysis.RectangleFubini
  Analysis.ParameterIntegrals.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_weighted_continuous (f : R -> R) :
  (forall x : R, {for x, continuous f}) ->
  forall x : R, {for x, continuous (fun t => f t * gaussian_kernel t)}.
Proof.
  intros HC x; apply (continuous_mult R);
    [apply HC | apply gaussian_kernel_continuous].
Qed.

Lemma gaussian_weighted_abs_domination (f g : R -> R) C :
  (forall x, Rabs (f x) <= C * g x) ->
  forall x, Rabs (f x * gaussian_kernel x) <= C * (g x * gaussian_kernel x).
Proof.
  intros Hb x.
  rewrite Rabs_mult (Rabs_pos_eq (gaussian_kernel x)
    (Rlt_le _ _ (gaussian_kernel_positive x))).
  specialize (Hb x); pose proof (gaussian_kernel_positive x); nra.
Qed.

Theorem gaussian_majorant_integrability (f g : R -> R) C :
  (forall x : R, {for x, continuous f}) -> (forall x : R, {for x, continuous g}) ->
  (forall x, Rabs (f x) <= C * g x) ->
  gaussian_integral_exists g ->
  gaussian_integral_exists f /\ gaussian_absolutely_integrable f.
Proof.
  intros HC HG Hb HIg.
  pose proof (gaussian_weighted_continuous f HC) as HF.
  assert (HCG : forall x : R,
    {for x, continuous (fun t => C * (g t * gaussian_kernel t))}).
  { intro x; apply (continuous_mult R);
      [apply (continuous_const R) | apply gaussian_weighted_continuous; exact HG]. }
  assert (HCGI : whole_line_integrable (fun x => C * (g x * gaussian_kernel x))).
  { exact (fubini_integrable_scale setT (fun x => g x * gaussian_kernel x) C
      measurableT HIg). }
  pose proof (gaussian_weighted_abs_domination f g C Hb) as Hbound.
  split.
  - exact (continuous_improper_dominated_integrable _ _ HF HCG Hbound HCGI).
  - unfold gaussian_absolutely_integrable, gaussian_integral_exists.
    have E : (fun x => Rabs (f x) * gaussian_kernel x) =
        (fun x => Rabs (f x * gaussian_kernel x)).
    { apply/funext => x.
      rewrite Rabs_mult (Rabs_pos_eq (gaussian_kernel x)
        (Rlt_le _ _ (gaussian_kernel_positive x))).
      reflexivity. }
    rewrite E.
    exact (continuous_improper_dominated_absolute_integrable _ _ HF HCG Hbound HCGI).
Qed.

Theorem gaussian_raw_cutoff_error_bound (f g : R -> R) C A :
  0 <= A ->
  (forall x : R, {for x, continuous f}) -> (forall x : R, {for x, continuous g}) ->
  (forall x, Rabs (f x) <= C * g x) ->
  gaussian_integral_exists g ->
  Rabs (gaussian_integral f - gaussian_cutoff_integral f A) <=
    C * (gaussian_integral g - gaussian_cutoff_integral g A).
Proof.
  intros HA HC HG Hb HIg.
  pose proof (proj1 (gaussian_majorant_integrability f g C HC HG Hb HIg)) as HIf.
  pose proof (gaussian_weighted_continuous f HC) as HF.
  pose proof (gaussian_weighted_continuous g HG) as HGw.
  assert (HCG : forall x : R,
    {for x, continuous (fun t => C * (g t * gaussian_kernel t))}).
  { intro x; apply (continuous_mult R); [apply (continuous_const R) | apply HGw]. }
  assert (HCint : whole_line_has_integral
    (fun x => C * (g x * gaussian_kernel x)) (C * gaussian_integral g)).
  { split.
    - exact (fubini_integrable_scale setT (fun x => g x * gaussian_kernel x) C
        measurableT HIg).
    - exact (fubini_integral_scale_l (fun x => g x * gaussian_kernel x) C HIg). }
  pose proof (continuous_improper_interval_error_bound
    (fun x => f x * gaussian_kernel x) (fun x => C * (g x * gaussian_kernel x))
    (gaussian_integral f) (C * gaussian_integral g) (-A) A
    HF HCG (gaussian_weighted_abs_domination f g C Hb)
    (gaussian_integral_correct f HIf) HCint ltac:(lra)) as H.
  change (Rabs (gaussian_integral f - gaussian_cutoff_integral f A) <=
    C * gaussian_integral g -
      oriented_integral (fun x => C * (g x * gaussian_kernel x)) (-A) A) in H.
  pose proof (rectangle_oriented_scal (fun x => g x * gaussian_kernel x)
    (-A) A C (continuous_finite_integrable _ HGw (-A) A)) as HS.
  change (oriented_integral (fun x => C * (g x * gaussian_kernel x)) (-A) A =
    C * gaussian_cutoff_integral g A) in HS.
  rewrite HS in H; unfold gaussian_cutoff_integral in *; nra.
Qed.

Theorem gaussian_normalized_cutoff_error_bound (f g : R -> R) C A :
  0 <= A ->
  (forall x : R, {for x, continuous f}) -> (forall x : R, {for x, continuous g}) ->
  (forall x, Rabs (f x) <= C * g x) ->
  gaussian_integral_exists g ->
  Rabs (gaussian_expectation f - gaussian_cutoff_expectation f A) <=
    gaussian_cutoff_error_majorant g C A.
Proof.
  intros HA HC HG Hb HIg.
  pose proof (gaussian_raw_cutoff_error_bound f g C A HA HC HG Hb HIg) as H.
  pose proof gaussian_mass_positive as HM.
  unfold gaussian_expectation, gaussian_cutoff_expectation,
    gaussian_cutoff_error_majorant.
  replace (gaussian_integral f / gaussian_mass -
      gaussian_cutoff_integral f A / gaussian_mass)
    with ((gaussian_integral f - gaussian_cutoff_integral f A) * / gaussian_mass)
    by (unfold Rdiv; ring).
  rewrite Rabs_mult Rabs_inv (Rabs_pos_eq gaussian_mass (Rlt_le _ _ HM)).
  replace (C / gaussian_mass *
      (gaussian_integral g - gaussian_cutoff_integral g A)) with
    ((C * (gaussian_integral g - gaussian_cutoff_integral g A)) * / gaussian_mass)
    by (unfold Rdiv; ring).
  apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; exact HM | exact H].
Qed.

Theorem gaussian_cutoff_integral_limit (f : R -> R) :
  gaussian_integral_exists f ->
  (gaussian_cutoff_integral f A @[A --> +oo%R] --> gaussian_integral f)%classic.
Proof.
  intro HI.
  exact (improper_symmetric_cutoff_limit (fun x => f x * gaussian_kernel x)
    (gaussian_integral f) (gaussian_integral_correct f HI)).
Qed.

Theorem gaussian_cutoff_majorant_limit (g : R -> R) C :
  gaussian_integral_exists g ->
  (gaussian_cutoff_error_majorant g C A @[A --> +oo%R] --> 0)%classic.
Proof.
  intro HIg.
  have HL := gaussian_cutoff_integral_limit g HIg.
  move/cvg_Reals_pinfty: HL => HL.
  apply/cvg_Reals_pinfty => eps Heps.
  pose proof (Rabs_pos (C / gaussian_mass)) as HK.
  assert (He : 0 < eps / (Rabs (C / gaussian_mass) + 1)).
  { apply Rdiv_lt_0_compat; lra. }
  destruct (HL _ He) as [M HM].
  exists M => x Hx.
  specialize (HM x Hx).
  unfold gaussian_cutoff_error_majorant.
  rewrite Rminus_0_r Rabs_mult.
  rewrite Rabs_minus_sym in HM.
  assert (Heq : eps / (Rabs (C / gaussian_mass) + 1) *
    (Rabs (C / gaussian_mass) + 1) = eps) by (field; lra).
  pose proof (Rmult_le_compat_l (Rabs (C / gaussian_mass)) _ _ HK
    (Rlt_le _ _ HM)).
  nra.
Qed.

Theorem gaussian_uniform_cutoff_convergence (g : R -> R) C :
  (forall x : R, {for x, continuous g}) -> gaussian_integral_exists g ->
  forall eps : posreal, exists B, 0 <= B /\
  forall A, B < A -> forall f : R -> R,
  (forall x : R, {for x, continuous f}) ->
  (forall x, Rabs (f x) <= C * g x) ->
  Rabs (gaussian_expectation f - gaussian_cutoff_expectation f A) < eps.
Proof.
  intros HG HIg eps.
  pose proof (gaussian_cutoff_majorant_limit g C HIg) as HL.
  move/cvg_Reals_pinfty: HL => HL.
  destruct (HL eps (cond_pos eps)) as [b Hb].
  exists (Rmax 0 b); split; [apply Rmax_l |].
  intros A HA f HC Hbound.
  assert (HbA : b < A) by (pose proof (Rmax_r 0 b); lra).
  assert (HA0 : 0 <= A) by (pose proof (Rmax_l 0 b); lra).
  specialize (Hb A HbA); rewrite Rminus_0_r in Hb.
  pose proof (gaussian_normalized_cutoff_error_bound f g C A HA0 HC HG Hbound HIg).
  pose proof (Rle_abs (gaussian_cutoff_error_majorant g C A)); lra.
Qed.
