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
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianCutoffDefinitions GaussianKernel
  GaussianMass GaussianExpectation ImproperBounds ImproperDomination ImproperCutoff
  GaussianCutoff RectangleFubini.
From EllipsoidFitting Require Import GaussianFubiniLebesgue.
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

(* Dominated convergence: whole_line_parameter_continuous_weighted of
   GaussianFubiniLebesgue, with the kernel as the weight, makes the integral
   continuous; the expectation divides it by gaussian_mass. The continuity
   hypothesis on h (HH) is not used. *)
Lemma gaussian_section_expectation_continuous (F : R -> R -> R) (g h : R -> R)
    (a : R) :
  (forall x y, continuity_2d_pt F x y) ->
  (forall x : R, {for x, continuous g}) -> (forall y : R, {for y, continuous h}) ->
  (forall y, 0 <= h y) ->
  (forall x y, Rabs (F x y) <= g x * h y) ->
  gaussian_integral_exists h ->
  {for a, continuous (fun x => gaussian_expectation (F x))}.
Proof.
  intros HC HG HH Hh Hb HIh.
  have Hk : continuous gaussian_kernel := gaussian_kernel_continuous.
  have Hk0 : forall y, 0 <= gaussian_kernel y.
  { intro y; exact (Rlt_le _ _ (gaussian_kernel_positive y)). }
  have Hint := whole_line_parameter_continuous_weighted F g h gaussian_kernel
    HC HG Hk HIh Hh Hk0 Hb a.
  unfold gaussian_expectation, gaussian_integral, Rdiv.
  apply (continuous_mult R); [exact Hint | apply (continuous_const R)].
Qed.

Lemma gaussian_section_expectation_bound (F : R -> R -> R) (g h : R -> R) :
  (forall x y, continuity_2d_pt F x y) ->
  (forall y : R, {for y, continuous h}) ->
  (forall x y, Rabs (F x y) <= g x * h y) ->
  gaussian_integral_exists h ->
  forall x, Rabs (gaussian_expectation (F x)) <= g x * gaussian_expectation h.
Proof.
  intros HC HH Hb HIh x.
  apply (gaussian_expectation_majorant_bound (F x) h (g x)); try assumption.
  - intro y; apply rectangle_continuous_slice_right, HC.
  - apply Hb.
Qed.
