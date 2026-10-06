(* The Gaussian expectation cut off to the segment [-A, A] is additive: for
   f and g continuous, gaussian_cutoff_expectation (f - g) A is the
   difference of the cut off expectations of f and g
   (gaussian_cutoff_expectation_sub). The cut off expectation is an
   oriented integral of a continuous function over the segment. *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.CutoffDefinitions Gaussian.Kernel Gaussian.Mass Gaussian.Expectation
  Analysis.SegmentIntegralBounds Analysis.WholeLineDomination
  Analysis.LineIntegralCutoff Gaussian.Cutoff Analysis.RectangleFubini.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_cutoff_expectation_sub (f g : R -> R) A :
  (forall x : R, {for x, continuous f}) -> (forall x : R, {for x, continuous g}) ->
  gaussian_cutoff_expectation (fun x => f x - g x) A =
  gaussian_cutoff_expectation f A - gaussian_cutoff_expectation g A.
Proof.
  intros HC HG. unfold gaussian_cutoff_expectation, gaussian_cutoff_integral.
  replace (oriented_integral (fun x => (f x - g x) * gaussian_kernel x) (-A) A) with
    (oriented_integral (fun x => f x * gaussian_kernel x - g x * gaussian_kernel x) (-A) A).
  2:{ apply rectangle_oriented_ext; intros x Hx; ring. }
  pose proof (rectangle_oriented_minus
    (fun x => f x * gaussian_kernel x) (fun x => g x * gaussian_kernel x) (-A) A
    (continuous_finite_integrable _ (gaussian_weighted_continuous f HC) (-A) A)
    (continuous_finite_integrable _ (gaussian_weighted_continuous g HG) (-A) A)) as HS.
  rewrite HS.
  unfold Rdiv; ring.
Qed.
