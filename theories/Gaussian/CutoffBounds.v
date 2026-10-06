(* Bounds on the truncated Gaussian expectation
   gaussian_cutoff_expectation f A, the integral of f x * gaussian_kernel x
   over [-A, A] divided by gaussian_mass. If f is continuous, 0 <= A and
   Rabs (f x) <= C on [-A, A], then
   Rabs (gaussian_cutoff_expectation f A) <= C (gaussian_cutoff_local_bound),
   because the integral of the kernel over [-A, A] is at most gaussian_mass
   (improper_nonnegative_interval_bound). Applied to f - g, this bounds the
   difference of two truncated expectations
   (gaussian_cutoff_local_difference). The continuity hypotheses write the
   binder as x : R, so that Rocq does not infer a MathComp carrier for x. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions Gaussian.Kernel
  Gaussian.Mass Gaussian.Expectation Gaussian.CutoffDefinitions
  Analysis.SegmentIntegralBounds Analysis.LineIntegralCutoff Gaussian.Cutoff
  Gaussian.RectangleCutoff.
From EllipsoidFitting Require Import Analysis.ParameterIntegrals.
Import ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_cutoff_local_bound (f : R -> R) A C :
  0 <= A -> 0 <= C -> (forall x : R, {for x, continuous f}) ->
  (forall x, Rabs x <= A -> Rabs (f x) <= C) ->
  Rabs (gaussian_cutoff_expectation f A) <= C.
Proof.
  intros HA HC Hf Hb.
  assert (Hraw : Rabs (oriented_integral (fun x => f x*gaussian_kernel x) (-A) A) <=
    C*oriented_integral gaussian_kernel (-A) A).
  { rewrite (fubini_oriented_symmetric _ _ HA) (fubini_oriented_symmetric _ _ HA).
    apply: fubini_Rintegral_bound.
    - exact: measurable_itv.
    - apply: fubini_segment_integrable => //.
      exact: (gaussian_weighted_continuous f Hf).
    - apply: fubini_segment_integrable => //.
      exact: gaussian_kernel_continuous.
    - move=> y; rewrite /= in_itv /= => /andP [/RleP Hy1 /RleP Hy2].
      rewrite Rabs_mult (Rabs_pos_eq (gaussian_kernel y)
        (Rlt_le _ _ (gaussian_kernel_positive y))).
      apply Rmult_le_compat_r; [apply Rlt_le, gaussian_kernel_positive |].
      apply Hb, Rabs_le; lra. }
  pose proof (improper_nonnegative_interval_bound gaussian_kernel gaussian_mass
    gaussian_kernel_continuous (fun x => Rlt_le _ _ (gaussian_kernel_positive x))
    gaussian_kernel_mass_integral (-A) A ltac:(lra)) as Hmass.
  assert (Htotal : Rabs (gaussian_cutoff_integral f A) <= C*gaussian_mass).
  { unfold gaussian_cutoff_integral; eapply Rle_trans; [exact Hraw|].
    apply Rmult_le_compat_l; assumption. }
  pose proof gaussian_mass_positive as HM.
  unfold gaussian_cutoff_expectation, Rdiv.
  rewrite Rabs_mult Rabs_inv (Rabs_pos_eq gaussian_mass (Rlt_le _ _ HM)).
  apply (Rmult_le_reg_r gaussian_mass); [exact HM|].
  replace (Rabs (gaussian_cutoff_integral f A) * / gaussian_mass * gaussian_mass)
    with (Rabs (gaussian_cutoff_integral f A)) by (field; lra).
  exact Htotal.
Qed.

Lemma gaussian_cutoff_local_difference (f g : R -> R) A C :
  0 <= A -> 0 <= C ->
  (forall x : R, {for x, continuous f}) -> (forall x : R, {for x, continuous g}) ->
  (forall x, Rabs x <= A -> Rabs (f x-g x) <= C) ->
  Rabs (gaussian_cutoff_expectation f A-gaussian_cutoff_expectation g A) <= C.
Proof.
  intros HA HC Hf Hg Hb.
  rewrite <- (gaussian_cutoff_expectation_sub f g A Hf Hg).
  apply gaussian_cutoff_local_bound; try assumption.
  intro x; exact (continuous_minus R f g x (Hf x) (Hg x)).
Qed.
