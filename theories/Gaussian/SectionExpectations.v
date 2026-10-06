(* A bound on a Gaussian expectation from a majorant:
   |E[f]| <= c * E[h] when f and h are continuous, |f| <= c * h, and h is
   integrable against the Gaussian kernel
   (gaussian_expectation_majorant_bound). The expectations are Lebesgue
   integrals over the line. *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.CutoffDefinitions Gaussian.Kernel Gaussian.Mass Gaussian.Expectation
  Analysis.SegmentIntegralBounds Analysis.WholeLineDomination
  Analysis.LineIntegralCutoff Gaussian.Cutoff Analysis.RectangleFubini.
From EllipsoidFitting Require Import Analysis.ParameterIntegrals.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_expectation_majorant_bound (f h : R -> R) (c : R) :
  (forall x : R, {for x, continuous f}) -> (forall x : R, {for x, continuous h}) ->
  (forall x, Rabs (f x) <= c * h x) ->
  gaussian_integral_exists h ->
  Rabs (gaussian_expectation f) <= c * gaussian_expectation h.
Proof.
  intros HC HH Hb HIh.
  destruct (gaussian_majorant_integrability f h c HC HH Hb HIh) as [HIf HAIf].
  eapply Rle_trans; [apply gaussian_expectation_absolute_bound; assumption|].
  rewrite <- (gaussian_expectation_scale h c HIh).
  apply gaussian_expectation_monotone; [exact HAIf| |exact Hb].
  apply gaussian_integral_exists_scale; exact HIh.
Qed.
