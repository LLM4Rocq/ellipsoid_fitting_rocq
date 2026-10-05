(* Port of theories/ImproperBounds.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order, and no statement gains or loses a hypothesis. The statements use
   the vocabulary of AnalysisIntegralDefinitions: Coquelicot's
   continuous g x becomes {for x, continuous g}, ex_RInt g a b becomes
   segment_integrable g a b, RInt g a b becomes oriented_integral g a b, and
   is_RInt_gen g (Rbar_locally m_infty) (Rbar_locally p_infty) J becomes
   whole_line_has_integral g J, the Lebesgue integral over the line.

   With the Lebesgue integral the three bounds hold without the continuity
   hypothesis: the integral of a nonnegative integrable function over a
   segment is at most its integral over the line, and the latter is
   nonnegative. The hypothesis is kept, unused, so that the calls of the
   importers keep their shape. The original proofs went through the
   definition of the improper Riemann integral as a limit over growing
   segments; the port uses fubini_segment_le_whole_line of
   GaussianFubiniLebesgue instead. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import RectangleFubini GaussianFubiniLebesgue.
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
