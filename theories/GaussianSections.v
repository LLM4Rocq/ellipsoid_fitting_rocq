(* Port of theories/GaussianSections.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order, and no statement gains or loses a hypothesis. The statements use
   the vocabulary of AnalysisIntegralDefinitions and of the bridge:
   - Coquelicot's pointwise continuous f x becomes MathComp's
     {for x, continuous f} (difference 5 of analysis/README.md). The bound
     variable in front of such a hypothesis is written x : R (or y : R), as
     in the ports of GaussianCutoff and of RectangleFubini and in the
     restated challenge ellipsoid_gaussian_fubini, so that Rocq does not
     infer a MathComp carrier for it. For the same reason every function and
     point argument is given its type R -> R -> R, R -> R or R; the
     original left them to inference. The inferred carrier unfolds to R, so
     this changes the text and not the meaning.
   - continuity_2d_pt keeps its name. It is the definition of
     AnalysisIntegralDefinitions, joint continuity at (x, y) for the product
     topology of R * R, which says the same thing as Coquelicot's.
   The arithmetic in every statement is Stdlib's, as in the original.

   Meaning. gaussian_integral_exists, gaussian_absolutely_integrable,
   gaussian_expectation and gaussian_cutoff_expectation follow the ported
   GaussianDefinitions and GaussianCutoffDefinitions: the integral over the
   line is the Lebesgue integral (difference 4 of analysis/README.md) and the
   cutoff integral is oriented_integral over [-A, A] (difference 3). The
   statements about expectations and integrability concern a continuous or
   jointly continuous function dominated by c * h, or by g x * h y, with h
   integrable against the kernel, so each one is the Lebesgue counterpart of
   the original. The cutoff expectation in
   gaussian_parameter_cutoff_continuous integrates a continuous function on
   a segment, where the Lebesgue and Riemann values agree. The two joint
   continuity lemmas involve no integral and say the same as the original.

   What changes in the proofs.
   - gaussian_joint_continuous_right is proved from continuity_1d_2d_pt_comp
     and continuity_2d_pt_id2 of RectangleFubini, in place of Coquelicot's
     continuous_comp with continuous_snd.
   - gaussian_section_expectation_continuous no longer goes through the
     uniform convergence of the cutoff expectations and an epsilon-delta
     argument. Its proof applies whole_line_parameter_continuous_weighted of
     GaussianFubiniLebesgue, with the Gaussian kernel as the weight: that
     lemma is MathComp's continuity_under_integral (dominated convergence),
     dominated on ]x - 1, x + 1[ by a bound of g there times h. The
     expectation is that integral divided by gaussian_mass. The continuity
     hypothesis on h is kept but no longer used, so that the calls of the
     importers keep their shape.
   - The other proofs are the original ones, with the ported lemmas of
     GaussianExpectation, GaussianCutoff and RectangleFubini. *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
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

(* The proof uses whole_line_parameter_continuous_weighted of
   GaussianFubiniLebesgue with the kernel as the weight; see the header.
   The hypothesis HH is not used. *)
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
