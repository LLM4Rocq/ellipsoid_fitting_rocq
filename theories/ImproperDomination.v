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

Lemma continuous_nonnegative_primitive_increasing (h : R -> R) :
  (forall x, {for x, continuous h}) ->
  (forall x, 0 <= h x) ->
  forall a x y, x <= y -> oriented_integral h a x <= oriented_integral h a y.
Proof.
  intros HC Hnonneg a x y Hxy.
  pose proof (continuous_finite_integrable h HC) as HI.
  rewrite -(rectangle_oriented_chasles h a x y (HI a x) (HI x y)).
  pose proof (gaussian_mass_oriented_ge0 h x y Hxy (fun t _ => Hnonneg t)).
  lra.
Qed.

(* The integral of h over [-n, n] is at most M, and by monotone convergence
   it tends to the integral of h over the line, which is therefore finite. *)
Lemma continuous_nonnegative_bounded_integrable (h : R -> R) M :
  (forall x, {for x, continuous h}) ->
  (forall x, 0 <= h x) ->
  (forall a b, a <= b -> oriented_integral h a b <= M) ->
  whole_line_integrable h.
Proof.
  intros HC Hnonneg Hb.
  have Hc : continuous h := HC.
  have mh : measurable_fun (setT : set (measurableTypeR R)) (EFin \o h).
  { apply/measurable_EFinP; exact: continuous_measurable_fun. }
  pose D (n : nat) : set R := `[(- (n%:R : R))%R, (n%:R : R)%R].
  have mD : forall n, measurable (D n : set (measurableTypeR R)).
  { move=> n; exact: measurable_itv. }
  have nd : nondecreasing_seq D.
  { apply/nondecreasing_seqP => n; apply/subsetPset => x.
    rewrite /D /= !in_itv /= => /andP [H1 H2]; apply/andP; split.
    - apply: (Order.POrderTheory.le_trans _ H1).
      by rewrite lerN2 ler_nat leqnSn.
    - apply: (Order.POrderTheory.le_trans H2).
      by rewrite ler_nat leqnSn. }
  have mhD : forall n,
      measurable_fun (D n : set (measurableTypeR R)) (EFin \o h).
  { move=> n; exact: measurable_funTS mh. }
  have h0 : forall n x, D n x -> (0 <= (EFin \o h) x)%E.
  { move=> n x _; rewrite /= lee_fin; apply/RleP; exact: Hnonneg. }
  have key := @ge0_nondecreasing_set_cvg_integral _ (measurableTypeR R) R
    D (EFin \o h) lebesgue_measure nd mD mhD h0.
  have HU : \bigcup_n D n = setT := bigcup_itvT true false.
  rewrite HU in key.
  have Hn : forall n,
      (\int[lebesgue_measure]_(x in D n) (EFin \o h) x <= M%:E)%E.
  { move=> n.
    have Hn0 : 0 <= (n%:R : R)%R by apply/RleP; exact: ler0n.
    have iD : lebesgue_measure.-integrable (D n) (EFin \o h).
    { exact: (fubini_segment_integrable h (n%:R)%R Hn0 Hc). }
    rewrite -(fineK (integrable_fin_num (mD n) iD)) lee_fin.
    apply/RleP.
    change (Rintegral lebesgue_measure `[(- (n%:R : R))%R, (n%:R : R)%R] h
      <= M).
    rewrite -(fubini_oriented_symmetric h (n%:R)%R Hn0).
    apply: Hb; lra. }
  have Hle : (\int[lebesgue_measure]_(x in setT) (EFin \o h) x <= M%:E)%E.
  { apply: (cvge_to_le key); apply: nearW => n; exact: Hn n. }
  apply/integrableP; split; first exact: mh.
  have -> : (\int[lebesgue_measure]_(x in setT) `|(EFin \o h) x|)%E =
      (\int[lebesgue_measure]_(x in setT) (EFin \o h) x)%E.
  { apply: eq_integral => x _; rewrite gee0_abs //= lee_fin.
    apply/RleP; exact: Hnonneg. }
  exact: (Order.POrderTheory.le_lt_trans Hle (ltry _)).
Qed.

Theorem continuous_nonnegative_dominated_integrable (h g : R -> R) :
  (forall x, {for x, continuous h}) ->
  (forall x, {for x, continuous g}) ->
  (forall x, 0 <= h x <= g x) ->
  whole_line_integrable g ->
  whole_line_integrable h.
Proof.
  intros HC HG Hle HJ.
  have Hc : continuous h := HC.
  apply: (fubini_dominated_integrable setT h g 1 measurableT).
  - exact: continuous_measurable_fun.
  - exact HJ.
  - move=> y _; specialize (Hle y).
    rewrite Rmult_1_l Rabs_pos_eq; lra.
Qed.

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

Theorem continuous_improper_integral_le (f g : R -> R) I J :
  (forall x, {for x, continuous f}) ->
  (forall x, {for x, continuous g}) ->
  (forall x, f x <= g x) ->
  whole_line_has_integral f I ->
  whole_line_has_integral g J ->
  I <= J.
Proof.
  intros HC HG Hle [HIf HfI] [HIg HgJ].
  rewrite -HfI -HgJ /whole_line_integral.
  apply/RleP; apply: (le_Rintegral measurableT HIf HIg).
  move=> x _; apply/RleP; exact: Hle.
Qed.

Theorem continuous_improper_integral_abs_bound (f g : R -> R) I J :
  (forall x, {for x, continuous f}) ->
  (forall x, {for x, continuous g}) ->
  (forall x, Rabs (f x) <= g x) ->
  whole_line_has_integral f I ->
  whole_line_has_integral g J ->
  Rabs I <= J.
Proof.
  intros HC HG Hle [HIf HfI] [HIg HgJ].
  have Hb : forall y, (setT : set R) y -> Rabs (f y) <= 1 * g y.
  { move=> y _; rewrite Rmult_1_l; exact: Hle. }
  have H := fubini_Rintegral_bound setT f g 1 measurableT HIf HIg Hb.
  rewrite Rmult_1_l in H.
  rewrite -HfI -HgJ; exact H.
Qed.
