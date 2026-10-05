(* Port of theories/GaussianCoordinateCutoff.v from Coquelicot to
   MathComp-Analysis.

   Both lemmas keep their names and their arguments, in the same order, and
   no statement gains or loses a hypothesis. Coquelicot's continuous f x
   becomes {for x, continuous f}, as in the vocabulary table of the port.
   The bound variable in front of a continuity hypothesis is written x : R,
   as in the ported GaussianCutoff, so that Rocq does not infer a MathComp
   carrier for it. The arithmetic in every statement is Stdlib's, as in the
   original.

   Meaning. gaussian_cutoff_expectation f A follows the ported
   GaussianCutoffDefinitions: it is oriented_integral of
   x |-> f x * gaussian_kernel x from -A to A, divided by gaussian_mass
   (difference 3 of analysis/README.md). For a continuous f and 0 <= A it is
   the Lebesgue integral over [-A, A] of a continuous function, whose value
   is the Riemann integral of the original. So both statements say what the
   originals said.

   What changes in the proofs. The bound on the integral over [-A, A] comes
   from fubini_Rintegral_bound of GaussianFubiniLebesgue, which asks for the
   pointwise bound only on the segment, in place of Coquelicot's
   norm_RInt_le. The integrability of the two integrands on the segment
   comes from fubini_segment_integrable, and fubini_oriented_symmetric turns
   the oriented integrals into integrals over [-A, A]. The bound of the
   integral of the kernel over [-A, A] by gaussian_mass is
   improper_nonnegative_interval_bound, as in the original. The continuity
   of f - g is continuous_minus of the bridge. The Coquelicot imports
   (Coquelicot, Compactness) and FunctionalExtensionality, which the
   original did not use, are dropped. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianKernel GaussianMass GaussianExpectation
  GaussianCutoffDefinitions ImproperBounds ImproperCutoff GaussianCutoff GaussianRectangle.
From EllipsoidFitting Require Import GaussianFubiniLebesgue.
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
