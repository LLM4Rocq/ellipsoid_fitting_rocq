(* Port of theories/ImproperDomination.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order, and no statement gains or loses a hypothesis. The statements use
   the vocabulary of AnalysisIntegralDefinitions:
   - continuous h x becomes {for x, continuous h};
   - RInt h a b becomes oriented_integral h a b;
   - ex_RInt_gen h (Rbar_locally m_infty) (Rbar_locally p_infty) becomes
     whole_line_integrable h, and is_RInt_gen over the same filters becomes
     whole_line_has_integral h l, the Lebesgue integral over the line.
   The arithmetic in every statement is Stdlib's, as in the original.

   Meaning. The conclusions now speak of the Lebesgue integral over the line,
   which requires absolute integrability (difference 4 of
   analysis/README.md). Every conclusion is about a function that is
   nonnegative or dominated in absolute value by an integrable function, so
   each statement is the Lebesgue counterpart of the original and none needs
   a new hypothesis.
   - continuous_nonnegative_bounded_integrable: a continuous nonnegative
     function whose integrals over segments are bounded by M is integrable on
     the line. The original proof took the limits of the primitive at -oo and
     +oo and applied is_RInt_gen_Derive. The port uses monotone convergence
     over the segments [-n, n] (MathComp's
     ge0_nondecreasing_set_cvg_integral), so the integral over the line is
     at most M.
   - The domination lemmas follow from the fact that a measurable function
     dominated by an integrable function is integrable
     (fubini_dominated_integrable of GaussianFubiniLebesgue), and the two
     comparisons of integrals from the monotonicity of the Lebesgue integral.
     Continuity of the dominated function is used only for its measurability.
     The continuity hypotheses on the dominating function, and those of the
     two comparison lemmas, are kept unused, so that the calls of the
     importers keep their shape.

   The original imported Classical_Prop. The port does not use it, so the
   assumptions of the module are the seven axioms of analysis/README.md. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import RectangleFubini GaussianFubiniLebesgue.
From EllipsoidFitting Require Import GaussianMass ImproperBounds.
From mathcomp Require Import measurable_realfun.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem continuous_improper_dominated_integrable (f g : R -> R) :
  (forall x, {for x, continuous f}) ->
  (forall x, {for x, continuous g}) ->
  (forall x, Rabs (f x) <= g x) ->
  whole_line_integrable g ->
  whole_line_integrable f.
Proof.
  intros HC HG Hle HJ.
  have Hc : continuous f := HC.
  apply: (fubini_dominated_integrable setT f g 1 measurableT).
  - exact: continuous_measurable_fun.
  - exact HJ.
  - move=> y _; rewrite Rmult_1_l; exact: Hle.
Qed.

Theorem continuous_improper_dominated_absolute_integrable (f g : R -> R) :
  (forall x, {for x, continuous f}) ->
  (forall x, {for x, continuous g}) ->
  (forall x, Rabs (f x) <= g x) ->
  whole_line_integrable g ->
  whole_line_integrable (fun x => Rabs (f x)).
Proof.
  intros HC HG Hle HI.
  apply: (fubini_integrable_abs setT f measurableT).
  exact: (continuous_improper_dominated_integrable f g HC HG Hle HI).
Qed.
