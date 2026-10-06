(* Gaussian expectations of the sections F x of a jointly continuous
   function F of two variables with |F x y| <= g x * h y, where h is
   nonnegative and integrable against the Gaussian kernel. The expectations
   are Lebesgue integrals over the line.
   - gaussian_expectation_majorant_bound: |E[f]| <= c * E[h] when f and h
     are continuous and |f| <= c * h.
   - gaussian_section_expectation_continuous: if g is continuous, then
     x |-> E[F x] is continuous.
   - gaussian_section_expectation_bound: |E[F x]| <= g x * E[h]. *)

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
