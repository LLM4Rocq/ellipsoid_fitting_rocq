(* Domination on the whole real line. A continuous f with |f| <= g, for g
   integrable on the line, is integrable on the line
   (continuous_improper_dominated_integrable), and so is |f|
   (continuous_improper_dominated_absolute_integrable). The integral over
   the line is the Lebesgue integral, which requires absolute
   integrability. The continuity of f gives its measurability; the
   continuity hypothesis on g is not used. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import Analysis.RectangleFubini
  Analysis.ParameterIntegrals.
From EllipsoidFitting Require Import Gaussian.Line.Mass
  Analysis.SegmentIntegralBounds.
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
