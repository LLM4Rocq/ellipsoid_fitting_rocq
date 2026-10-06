(* Cutoffs of integrals over the line to segments. The integrals over the
   line are Lebesgue integrals (whole_line_has_integral), which require
   absolute integrability.
   - improper_cutoff_interval_error_bound: if f and g have integrals If and
     Ig over the line and |f| <= g, then for a <= b,
     |If - oriented_integral f a b| <= Ig - oriented_integral g a b. The
     left side is the absolute value of the integral of f off [a, b]
     (improper_cutoff_whole_line_split), at most the integral of g there.
     continuous_improper_interval_error_bound states the same bound with
     continuity hypotheses, which its proof does not use.
   - improper_symmetric_cutoff_limit: oriented_integral f (- A) A tends to
     the integral of f over the line as A tends to +oo. The proof applies
     the error bound to f and |f|, with fubini_cutoff_cvg of
     Analysis.ParameterIntegrals (the integral of |f| over [-n, n] tends to its
     integral over the line) and the monotonicity of the integral of |f|
     over growing segments (improper_cutoff_subset_le). *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import Analysis.RectangleFubini
  Analysis.ParameterIntegrals.
From EllipsoidFitting Require Import Analysis.SegmentIntegralBounds.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* The oriented integral on a segment with ordered end points is the
   Lebesgue integral on the closed segment. *)
Lemma improper_cutoff_segment (h : R -> R) a b : a <= b ->
  oriented_integral h a b = Rintegral lebesgue_measure `[a, b] h.
Proof.
move=> hab; rewrite /oriented_integral; case: Rle_dec => // h'; exfalso; lra.
Qed.

(* The integral over the line minus the integral over a measurable set D is
   the integral over the complement of D. *)
Lemma improper_cutoff_whole_line_split (h : R -> R) (D : set R) :
  measurable (D : set (measurableTypeR R)) -> whole_line_integrable h ->
  whole_line_integral h - Rintegral lebesgue_measure D h =
  Rintegral lebesgue_measure (~` D) h.
Proof.
move=> mD hi.
have hU : lebesgue_measure.-integrable (D `|` ~` D) (EFin \o h)
  by rewrite setUv.
have hdisj : [disjoint D & ~` D] by apply/disj_set2P; exact: setICr.
rewrite /whole_line_integral -(setUv D).
rewrite (Rintegral_setU mD (measurableC mD) hU hdisj) -RplusE.
exact: Rplus_minus_l.
Qed.

(* The error bound of continuous_improper_interval_error_bound, without the
   continuity hypotheses, which the Lebesgue integral does not need. *)
Lemma improper_cutoff_interval_error_bound f g If Ig a b :
  whole_line_has_integral f If -> whole_line_has_integral g Ig ->
  (forall x, Rabs (f x) <= g x) -> a <= b ->
  Rabs (If - oriented_integral f a b) <= Ig - oriented_integral g a b.
Proof.
move=> [Hfi HfI] [Hgi HgI] Hbound Hab.
have mD : measurable (`[a, b] : set (measurableTypeR R))
  by exact: measurable_itv.
have mC := measurableC mD.
rewrite !(improper_cutoff_segment _ _ _ Hab) -HfI -HgI.
rewrite (improper_cutoff_whole_line_split f _ mD Hfi).
rewrite (improper_cutoff_whole_line_split g _ mD Hgi).
have H := fubini_Rintegral_bound (~` `[a, b]) f g 1 mC
  (integrableS measurableT mC (subsetT _) Hfi)
  (integrableS measurableT mC (subsetT _) Hgi)
  (fun y _ => ltac:(rewrite Rmult_1_l; exact: Hbound)).
by rewrite Rmult_1_l in H.
Qed.

Theorem continuous_improper_interval_error_bound f g If Ig a b :
  (forall x, {for x, continuous f}) -> (forall x, {for x, continuous g}) ->
  (forall x, Rabs (f x) <= g x) ->
  whole_line_has_integral f If ->
  whole_line_has_integral g Ig ->
  a <= b -> Rabs (If - oriented_integral f a b) <=
    Ig - oriented_integral g a b.
Proof.
intros HC HG Hbound HIf HIg Hab.
exact (improper_cutoff_interval_error_bound f g If Ig a b HIf HIg Hbound Hab).
Qed.

(* The integral of a nonnegative function over a measurable subset D of a
   measurable set E is at most its integral over E. *)
Lemma improper_cutoff_subset_le (h : R -> R) (D E : set R) :
  measurable (D : set (measurableTypeR R)) ->
  measurable (E : set (measurableTypeR R)) -> D `<=` E ->
  (forall x, 0 <= h x) -> lebesgue_measure.-integrable E (EFin \o h) ->
  Rintegral lebesgue_measure D h <= Rintegral lebesgue_measure E h.
Proof.
move=> mD mE DE h0 hi.
have mED : measurable (E `\` D : set (measurableTypeR R))
  by exact: measurableD.
have hU : lebesgue_measure.-integrable (D `|` (E `\` D)) (EFin \o h)
  by rewrite setDUK.
have hdisj : [disjoint D & E `\` D] by apply/disj_set2P; exact: setDIK.
rewrite -(setDUK DE) (Rintegral_setU mD mED hU hdisj).
apply/RleP; rewrite lerDl.
by apply: Rintegral_ge0 => x _; apply/RleP; exact: h0.
Qed.

Theorem improper_symmetric_cutoff_limit f J :
  whole_line_has_integral f J ->
  (oriented_integral f (- A) A @[A --> +oo%R] --> J)%classic.
Proof.
move=> [Hi HJ].
pose g := fun x => Rabs (f x).
have Hg : whole_line_integrable g := fubini_integrable_abs setT f measurableT Hi.
have Hcvg := fubini_cutoff_cvg g Hg.
apply/cvg_Reals_pinfty => eps Heps.
have [N _ HN] := (cvgrPdist_lt _ _).1 Hcvg eps (introT RltP Heps).
exists (INR N) => x Hx.
have HN0 := pos_INR N.
have Hxx : - x <= x by lra.
have Hb := improper_cutoff_interval_error_bound f g J (whole_line_integral g)
  (- x) x (conj Hi HJ) (conj Hg erefl) (fun y => Rle_refl _) Hxx.
have Hmono : Rintegral lebesgue_measure `[- INR N, INR N] g <=
    oriented_integral g (- x) x.
  rewrite (improper_cutoff_segment _ _ _ Hxx).
  apply: improper_cutoff_subset_le.
  - exact: measurable_itv.
  - exact: measurable_itv.
  - move=> y /=; rewrite !in_itv /= => /andP[/RleP h1 /RleP h2].
    by apply/andP; split; apply/RleP; rewrite -?RoppE; lra.
  - by move=> y; exact: Rabs_pos.
  - apply: integrableS Hg => //; exact: measurable_itv.
have HNN := HN N (leqnn N).
move/RltP: HNN; rewrite -RminusE -RabsE => HNN.
rewrite Rabs_minus_sym.
have := Rle_abs (whole_line_integral g -
  Rintegral lebesgue_measure `[- INR N, INR N] g).
lra.
Qed.
