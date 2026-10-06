(* Segment integrals of a nonnegative function are bounded by its integral
   over the line. If g is nonnegative with Lebesgue integral J over the
   line (whole_line_has_integral g J), its oriented integral over a segment
   [a, b] with a <= b is less than J + eps for every eps > 0
   (improper_nonnegative_interval_bound_eps) and at most J
   (improper_nonnegative_interval_bound). A continuous function is
   integrable on every segment (continuous_finite_integrable).
   The two bounds do not use their continuity hypothesis: the proof
   compares the integral over [a, b] with the integral over the line
   (fubini_segment_le_whole_line). *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import Analysis.RectangleFubini
  Analysis.ParameterIntegrals.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma continuous_finite_integrable (g : R -> R) :
  (forall x, {for x, continuous g}) -> forall a b, segment_integrable g a b.
Proof.
  intros HC a b; exact: rectangle_continuous_segment_integrable.
Qed.

Lemma improper_nonnegative_interval_bound_eps (g : R -> R) J :
  (forall x, {for x, continuous g}) ->
  (forall x, 0 <= g x) ->
  whole_line_has_integral g J ->
  forall a b (eps : posreal), a <= b -> oriented_integral g a b < J + eps.
Proof.
  intros HC Hg [HI HJ] a b eps Hab.
  have Hseg : oriented_integral g a b = Rintegral lebesgue_measure `[a, b] g.
  { rewrite /oriented_integral; case: Rle_dec => // h; exfalso; lra. }
  have Hle := fubini_segment_le_whole_line g `[a, b] (measurable_itv _) Hg HI.
  pose proof (cond_pos eps).
  rewrite Hseg; rewrite HJ in Hle; lra.
Qed.

Lemma improper_nonnegative_interval_bound (g : R -> R) J :
  (forall x, {for x, continuous g}) ->
  (forall x, 0 <= g x) ->
  whole_line_has_integral g J ->
  forall a b, a <= b -> oriented_integral g a b <= J.
Proof.
  intros HC Hg HJ a b Hab.
  destruct (Rle_dec (oriented_integral g a b) J) as [Hle | Hgt]; [exact Hle | ].
  assert (He : 0 < (oriented_integral g a b - J) / 2) by lra.
  pose proof (improper_nonnegative_interval_bound_eps g J HC Hg HJ a b
    (mkposreal _ He) Hab) as H; simpl in H; lra.
Qed.
