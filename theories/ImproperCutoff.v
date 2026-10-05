(* Port of theories/ImproperCutoff.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order, and no statement gains or loses a hypothesis. The statements use
   the vocabulary of AnalysisIntegralDefinitions: Coquelicot's
   continuous f x becomes {for x, continuous f}, RInt f a b becomes
   oriented_integral f a b, and
   is_RInt_gen f (Rbar_locally m_infty) (Rbar_locally p_infty) If becomes
   whole_line_has_integral f If, the Lebesgue integral over the line
   (difference 4 of analysis/README.md). In improper_symmetric_cutoff_limit,
   Coquelicot's is_lim (fun A => RInt f (-A) A) p_infty J becomes
   (oriented_integral f (- A) A @[A --> +oo%R] --> J)%classic, the limit of
   MathComp at +oo.

   continuous_finite_integral_abs_bound and
   continuous_enclosing_interval_error_bound are about integrals on
   segments. Continuity gives the integrability of f and g on the segments,
   as in the original, and the proofs follow the original through
   fubini_Rintegral_bound of GaussianFubiniLebesgue and the Chasles relation
   rectangle_oriented_chasles of RectangleFubini.

   For continuous_improper_interval_error_bound_eps and
   continuous_improper_interval_error_bound the continuity hypotheses are
   kept, unused, so that the calls of the importers keep their shape. With
   the Lebesgue integral, whole_line_has_integral already gives the
   integrability of f and g, and the bound follows directly: If minus the
   integral of f over [a, b] is the integral of f over the complement of
   [a, b], whose absolute value is at most the integral of g there, which is
   Ig minus the integral of g over [a, b]. That is the new lemma
   improper_cutoff_interval_error_bound, which needs no continuity. The
   original proofs went instead through the definition of the improper
   Riemann integral as a limit over growing segments, with an eps of room.

   improper_symmetric_cutoff_limit is proved from that bound applied to f
   and Rabs \o f, and from fubini_cutoff_cvg of GaussianFubiniLebesgue (the
   integral over [-n, n] of an integrable function tends to its integral
   over the line), together with the monotonicity of the integral of the
   nonnegative function Rabs \o f over growing segments. Like the original,
   it has no continuity hypothesis.

   New lemmas, used in the proofs above: improper_cutoff_segment,
   improper_cutoff_continuous_integrable, improper_cutoff_whole_line_split,
   improper_cutoff_interval_error_bound and improper_cutoff_subset_le. *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import RectangleFubini GaussianFubiniLebesgue.
From EllipsoidFitting Require Import ImproperBounds.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* The oriented integral on a segment with ordered end points is the
   Lebesgue integral on the closed segment. *)
Lemma improper_cutoff_segment (h : R -> R) a b : a <= b ->
  oriented_integral h a b = Rintegral lebesgue_measure `[a, b] h.
Proof.
move=> hab; rewrite /oriented_integral; case: Rle_dec => // h'; exfalso; lra.
Qed.

(* A continuous function is integrable on every closed segment. *)
Lemma improper_cutoff_continuous_integrable (h : R -> R) a b :
  (forall x, {for x, continuous h}) ->
  lebesgue_measure.-integrable `[a, b] (EFin \o h).
Proof.
move=> hc; apply: continuous_compact_integrable; first exact: segment_compact.
exact/continuous_subspaceT.
Qed.

Lemma continuous_finite_integral_abs_bound f g a b :
  (forall x, {for x, continuous f}) -> (forall x, {for x, continuous g}) ->
  (forall x, Rabs (f x) <= g x) -> a <= b ->
  Rabs (oriented_integral f a b) <= oriented_integral g a b.
Proof.
intros HC HG Hbound Hab.
rewrite !(improper_cutoff_segment _ _ _ Hab).
have H := fubini_Rintegral_bound `[a, b] f g 1 (measurable_itv _)
  (improper_cutoff_continuous_integrable f a b HC)
  (improper_cutoff_continuous_integrable g a b HG)
  (fun y _ => ltac:(rewrite Rmult_1_l; exact: Hbound)).
by rewrite Rmult_1_l in H.
Qed.

Lemma continuous_enclosing_interval_error_bound f g u a b v :
  (forall x, {for x, continuous f}) -> (forall x, {for x, continuous g}) ->
  (forall x, Rabs (f x) <= g x) -> u <= a -> a <= b -> b <= v ->
  Rabs (oriented_integral f u v - oriented_integral f a b) <=
    oriented_integral g u v - oriented_integral g a b.
Proof.
intros HC HG Hbound Hua Hab Hbv.
pose proof (continuous_finite_integrable f HC) as HF.
pose proof (continuous_finite_integrable g HG) as HGf.
assert (Hf : oriented_integral f u v - oriented_integral f a b =
  oriented_integral f u a + oriented_integral f b v).
{ rewrite -(rectangle_oriented_chasles f u b v (HF u b) (HF b v)).
  rewrite -(rectangle_oriented_chasles f u a b (HF u a) (HF a b)).
  ring. }
assert (Hg : oriented_integral g u v - oriented_integral g a b =
  oriented_integral g u a + oriented_integral g b v).
{ rewrite -(rectangle_oriented_chasles g u b v (HGf u b) (HGf b v)).
  rewrite -(rectangle_oriented_chasles g u a b (HGf u a) (HGf a b)).
  ring. }
rewrite Hf Hg.
eapply Rle_trans; [apply Rabs_triang |].
pose proof (continuous_finite_integral_abs_bound f g u a HC HG Hbound Hua).
pose proof (continuous_finite_integral_abs_bound f g b v HC HG Hbound Hbv); lra.
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

Lemma continuous_improper_interval_error_bound_eps f g If Ig a b
    (eps : posreal) :
  (forall x, {for x, continuous f}) -> (forall x, {for x, continuous g}) ->
  (forall x, Rabs (f x) <= g x) ->
  whole_line_has_integral f If ->
  whole_line_has_integral g Ig ->
  a <= b -> Rabs (If - oriented_integral f a b) <
    Ig - oriented_integral g a b + 2 * eps.
Proof.
intros HC HG Hbound HIf HIg Hab.
pose proof (improper_cutoff_interval_error_bound f g If Ig a b
  HIf HIg Hbound Hab) as H.
pose proof (cond_pos eps); lra.
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
