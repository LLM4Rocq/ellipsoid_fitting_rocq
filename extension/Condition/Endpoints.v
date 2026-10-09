(* The endpoint behavior of the condition-number curve, at Stdlib's R: item
   R4 of phase 9 (notes/optional-items-plan.md; the Gaussian note
   notes/gaussian-condition-number-theorem.md, section 5). It proves
   condition_endpoints_statement of ConditionEndpoints, on the frozen
   condition_alpha and condition_star of ConditionDefinitions, with m and v
   the upper moments of the semicircle law nu on [-sqrt 2, sqrt 2]
   (threshold_law), as in Condition/Curve.v.

   Results.
   - curve_m0: m(0) = mu0 = 2 sqrt 2 / (3 pi), by the fundamental theorem
     of calculus for x sqrt(2 - x^2).
   - curve_m_expand: 0 <= m(t) - mu0 + t/2 <= (sqrt 2 / pi) t^2 for
     0 <= t. By tent_identity, m(t) + m(-t) - 2 m(0) is the integral of
     the tent max(t - |x|, 0), and m(-t) = m(t) + t; the tent lies between
     0 and t 1{|x| <= t}, and the density is at most sqrt 2 / pi.
   - Near C = 1, with u = C - 1. curve_energyE: by v(-t) + v(t) = 1/2 + t^2,
     the clip energy is 1/2 - g(t) with g(t) = v(t) - v(C t) - t^2, so
     alpha_C = g(t_C) >= g(t) for t >= 0. The Taylor bound of v and
     curve_m_expand bound g(t) = 2 u t m(t) - t^2 + O(u^2 t^2).
     condition_alpha_lower: at t = mu0 u / C, alpha_C >= mu0 u t - u^2 t^2.
     condition_t_near_one: t_C <= 2 mu0 u for u < 1/2, since at
     t = 2 mu0 u, m(-t) >= mu0 C > C m(C t).
     condition_alpha_upper: alpha_C <= mu0 u t + (16 (sqrt 2 / pi) mu0^3
     + 4 mu0^2) u^4 with the same t. Since mu0 u t = mu0^2 u^2 / C and
     mu0^2 = 8 / (9 pi^2), this gives (11) with the constant
     16 (sqrt 2 / pi) mu0^3 + 5 mu0^2 (condition_alpha_near_oneP).
   - (34). cubic_inverse: if |b^2 - u^2 (1 - u)| <= K u^4 with u <= 1/2,
     b <= 1/8 and K u^2 <= 1/4, then |u - (b + b^2 / 2)| <= 2 (16 K + 3) b^3,
     by F(u) - F(v) = (u - v) (u + v - (u^2 + u v + v^2)) for
     F(u) = u^2 (1 - u) and v = b + b^2 / 2. condition_star_near_zeroP
     applies it at u = C_star(alpha) - 1 and b = sqrt alpha / mu0, after
     C_star(alpha) - 1 is made small through the monotonicity of
     C |-> alpha_C (condition_starP).
   - As C -> oo: C t_C -> sqrt 2, since C m(C t_C) = m(-t_C) is bounded
     and m is positive below sqrt 2; then
     C (1/4 - alpha_C) = 2 mu0 C t_C + O(C t_C^2) + C v(C t_C), and
     v(w) <= (sqrt 2 - w) m(w), so C (1/4 - alpha_C) -> 2 sqrt 2 mu0
     = 8 / (3 pi) (condition_alpha_near_infinityP). (35) follows since
     C_star(alpha) -> oo as alpha -> 1/4 (condition_star_near_quarterP).
   - condition_endpoints: condition_endpoints_statement. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability normal_distribution.
From mathcomp Require Import sequences trigo realfun derive ftc.
From GaussianAnalysis.probability Require Import semicircle_law variational.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality Require Import ConditionEndpoints.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.
From EllipsoidUniversality.Condition Require Import Curve.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation m := (upper_moment threshold_law 1).
Local Notation s := (upper_moment threshold_law 2).
Local Notation sq2 := (Num.sqrt 2%:R : R).
Local Notation mu0 := (2%:R * Num.sqrt 2%:R / (3%:R * pi)).

(* A calculus fact, over any realType: int_0^(sqrt c) x sqrt(c - x^2) dx
   = c sqrt c / 3, with the antiderivative -(c - x^2)^(3/2) / 3. *)
Section x_sqrt.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).

Lemma is_derive_x_sqrt (c x : R) : x ^+ 2 < c ->
  is_derive x 1
    (fun y : R => - ((c - y ^+ 2) * Num.sqrt (c - y ^+ 2)) / 3%:R)
    (x * Num.sqrt (c - x ^+ 2)).
Proof.
move=> xc.
have p0 : 0 < c - x ^+ 2 by rewrite subr_gt0.
have hp : is_derive x 1 (fun y : R => c - y ^+ 2) (- (2%:R * x)).
  apply: is_derive_eq.
  by rewrite add0r mul1r /GRing.scale /= mulr1 -mulr2n mulr_natl.
have hs := is_derive1_sqrt p0.
have hq := @is_derive1_comp R Num.sqrt (fun y : R => c - y ^+ 2) x _ _ hs hp.
have hm := is_deriveM hp hq.
have hZ := is_deriveZ (- 3%:R^-1) hm.
have -> : (fun y : R => - ((c - y ^+ 2) * Num.sqrt (c - y ^+ 2)) / 3%:R) =
    (fun y : R => - 3%:R^-1 * ((c - y ^+ 2) * Num.sqrt (c - y ^+ 2))).
  by apply/funext => y; field.
apply: (is_derive_eq hZ).
rewrite /GRing.scale /=.
set q := Num.sqrt (c - x ^+ 2).
have q0 : q != 0 by rewrite gt_eqF // sqrtr_gt0.
have hq2 : c - x ^+ 2 = q * q by rewrite -expr2 sqr_sqrtr // ltW.
rewrite hq2.
by field.
Qed.

Lemma Rintegral_x_sqrt (c : R) : 0 < c ->
  \int[mu]_(x in `[0, Num.sqrt c]) (x * Num.sqrt (c - x ^+ 2)) =
  c * Num.sqrt c / 3%:R.
Proof.
move=> c0.
have sc0 : 0 < Num.sqrt c by rewrite sqrtr_gt0.
pose F (y : R) := - ((c - y ^+ 2) * Num.sqrt (c - y ^+ 2)) / 3%:R.
pose f (y : R) := y * Num.sqrt (c - y ^+ 2).
have csq : continuous (fun y : R => Num.sqrt (c - y ^+ 2)).
  move=> y; apply: continuous_comp; last exact: sqrt_continuous.
  by apply: continuousB; [exact: cvg_cst|exact: (@continuousM _ _ id id)].
have cf : continuous f.
  move=> y; rewrite /f.
  exact: (@continuousM _ _ id (fun z : R => Num.sqrt (c - z ^+ 2)) y
    (@cvg_id _ _) (csq y)).
have cp : continuous (fun y : R => c - y ^+ 2).
  move=> y; apply: (@continuousB _ _ _ (fun=> c) (fun z : R => z ^+ 2)).
    exact: cvg_cst.
  exact: exprn_continuous.
have cF : continuous F.
  move=> y; rewrite /F.
  apply: (@continuousM _ _ (fun z : R => - ((c - z ^+ 2) * Num.sqrt (c - z ^+ 2)))
    (fun=> 3%:R^-1)); last exact: cvg_cst.
  apply: continuousN.
  exact: (@continuousM _ _ (fun z : R => c - z ^+ 2)
    (fun z : R => Num.sqrt (c - z ^+ 2)) y (cp y) (csq y)).
have dF y : 0 < y -> y < Num.sqrt c -> is_derive y 1 F (f y).
  move=> y0 yc; apply: is_derive_x_sqrt.
  have : y ^+ 2 < Num.sqrt c ^+ 2 by rewrite ltr_pXn2r // ?nnegrE ltW.
  by rewrite sqr_sqrtr // ltW.
have E : (\int[mu]_(x in `[0%R, Num.sqrt c]) (f x)%:E =
    (F (Num.sqrt c))%:E - (F 0)%:E)%E.
  apply: continuous_FTC2 => //.
  - by apply: continuous_subspaceT => x; exact: cf.
  - split.
    + move=> y; rewrite in_itv /= => /andP[y0 yc].
      exact: (@ex_derive _ _ _ _ _ _ _ (dF y y0 yc)).
    + by apply: cvg_at_right_filter; exact: cF.
    + by apply: cvg_at_left_filter; exact: cF.
  - move=> y; rewrite in_itv /= => /andP[y0 yc].
    by rewrite derive1E (@derive_val _ _ _ _ _ _ _ (dF y y0 yc)).
rewrite /Rintegral E -EFinB /= /F sqr_sqrtr ?(ltW c0) // subrr mul0r oppr0.
rewrite mul0r expr0n /= subr0.
by field.
Qed.

Lemma Rintegral_x_sqrtZ (c k : R) : 0 < c ->
  \int[mu]_(x in `[0, Num.sqrt c]) (k * (x * Num.sqrt (c - x ^+ 2))) =
  k * (c * Num.sqrt c / 3%:R).
Proof.
move=> c0; rewrite RintegralZl.
- exact: measurable_itv.
- apply: continuous_compact_integrable; first exact: segment_compact.
  apply: continuous_subspaceT => x.
  apply: (@continuousM _ _ id (fun z : R => Num.sqrt (c - z ^+ 2)) x
    (@cvg_id _ _)).
  apply: continuous_comp; last exact: sqrt_continuous.
  by apply: continuousB; [exact: cvg_cst|exact: (@continuousM _ _ id id)].
- by rewrite Rintegral_x_sqrt.
Qed.

End x_sqrt.

Section endpoints.

(* 1. m(0) and m near 0. *)


Lemma curve_m0 : m 0 = mu0.
Proof.
have q0 := curve_sq2_gt0.
have q0' : sq2 != 0 by rewrite gt_eqF.
rewrite /upper_moment (Rintegral_semicircle q0').
  exact: (threshold_integrable_continuous (fun x : R => Num.max (x - 0) 0 ^+ 1)
    (continuous_upper_part _ _)).
rewrite gtr0_norm //.
(* the integral over [- sqrt 2, 0[ vanishes, the one over [0, sqrt 2] is
   int_0^(sqrt 2) x sqrt(2 - x^2) / pi *)
pose g := fun x : R => maxr (x - 0) 0 ^+ 1 * semicircle_pdf sq2 x.
have cg : continuous g.
  move=> x; apply: (@continuousM _ _ (fun y : R => maxr (y - 0) 0 ^+ 1)
    (semicircle_pdf sq2)); first exact: continuous_upper_part.
  exact: continuous_semicircle_pdf.
have U : `[- sq2, sq2]%classic = `[- sq2, 0[%classic `|` `[0, sq2]%classic.
  by apply: itv_bndbnd_setU; rewrite bnd_simp ?oppr_le0 ltW.
have ig : (@lebesgue_measure R).-integrable
    (`[- sq2, 0[%classic `|` `[0, sq2]%classic) (EFin \o g).
  rewrite -U; apply: continuous_compact_integrable; first exact: segment_compact.
  by apply: continuous_subspaceT => x; exact: cg.
have disj : [disjoint `[- sq2, 0[%classic & `[0, sq2]%classic].
  apply/disj_setPS => x [/=]; rewrite !in_itv /= => /andP[_ h1] /andP[h2 _].
  by move: (lt_le_trans h1 h2); rewrite ltxx.
rewrite -/g U Rintegral_setU //; try exact: measurable_itv.
have -> : \int[lebesgue_measure]_(x in `[- sq2, 0[)
    (maxr (x - 0) 0 ^+ 1 * semicircle_pdf sq2 x) = 0.
  transitivity (\int[lebesgue_measure]_(x in `[- sq2, 0[) (0 : R)).
    apply: eq_Rintegral => x; rewrite inE /= in_itv /= => /andP[_ x0].
    by rewrite subr0 max_r ?(ltW x0) // expr1 mul0r.
  by rewrite /Rintegral integral0.
have sq : sq2 ^+ 2 = 2%:R by rewrite sqr_sqrtr // ler0n.
have pi0 : pi != 0 :> R by rewrite gt_eqF // pi_gt0.
transitivity (0 + \int[lebesgue_measure]_(x in `[0, sq2])
    (pi^-1 * (x * Num.sqrt (2%:R - x ^+ 2)))).
  congr (_ + _); apply: eq_Rintegral => x.
  rewrite inE /= in_itv /= => /andP[x0 _].
  rewrite subr0 max_l // expr1 semicircle_pdfE // sq.
  by move: (pi : R) pi0 => p p0; field.
rewrite add0r (@Rintegral_x_sqrtZ R 2%:R) ?ltr0n //.
by move: (pi : R) pi0 => p p0; field.
Qed.

(* (x - t)_+ + (x + t)_+ - 2 x_+ = (t - |x|)_+ for t >= 0. *)
Lemma tent_identity (t x : R) : 0 <= t ->
  Num.max (x - t) 0 + Num.max (x + t) 0 - 2%:R * Num.max x 0 =
  Num.max (t - `|x|) 0.
Proof.
move=> t0.
have [x0|x0] := leP 0 x.
- rewrite (ger0_norm x0).
  have h1 : 0 <= x + t by rewrite addr_ge0.
  rewrite (max_l h1).
  have [xt|xt] := leP t x.
  + have h2 : 0 <= x - t by rewrite subr_ge0.
    have h3 : t - x <= 0 by rewrite subr_le0.
    rewrite (max_l h2) (max_r h3).
    by rewrite mulr2n mulrDl mul1r; ring.
  + have h2 : x - t <= 0 by rewrite subr_le0 ltW.
    have h3 : 0 <= t - x by rewrite subr_ge0 ltW.
    rewrite (max_r h2) (max_l h3).
    by rewrite mulr2n mulrDl mul1r; ring.
- rewrite (ltr0_norm x0) opprK mulr0 subr0.
  have h1 : x - t <= 0 by rewrite subr_le0; apply: le_trans t0; exact: ltW.
  rewrite (max_r h1) add0r.
  have [xt|xt] := leP (- t) x.
  + have h2 : 0 <= x + t by rewrite -lerBlDr sub0r.
    have h3 : 0 <= t + x by rewrite addrC.
    by rewrite (max_l h2) (max_l h3) addrC.
  + have h2 : x + t <= 0 by rewrite -lerBrDr sub0r ltW.
    have h3 : t + x <= 0 by rewrite addrC.
    by rewrite (max_r h2) (max_r h3).
Qed.

Lemma curve_m_expand (t : R) : 0 <= t ->
  0 <= m t - mu0 + t / 2%:R <= sq2 / pi * t ^+ 2.
Proof.
move=> t0; have q0 := curve_sq2_gt0; rewrite -curve_m0.
have hsym := upper_moment1_sym threshold_law2 threshold_law_sym t.
have i1 : threshold_law.-integrable [set: R]
    (EFin \o (fun x : R => Num.max (x - t) 0 ^+ 1)).
  exact: (threshold_integrable_continuous _ (continuous_upper_part _ _)).
have i2 : threshold_law.-integrable [set: R]
    (EFin \o (fun x : R => Num.max (x - - t) 0 ^+ 1)).
  exact: (threshold_integrable_continuous _ (continuous_upper_part _ _)).
have i3 : threshold_law.-integrable [set: R]
    (EFin \o (fun x : R => Num.max (x - 0) 0 ^+ 1)).
  exact: (threshold_integrable_continuous _ (continuous_upper_part _ _)).
have iD : threshold_law.-integrable [set: R]
    (EFin \o (fun x : R => Num.max (x - t) 0 ^+ 1 + Num.max (x - - t) 0 ^+ 1)).
  have := integrableD measurableT i1 i2.
  by apply: eq_integrable => // x _; rewrite /= EFinD.
have iZ : threshold_law.-integrable [set: R]
    (EFin \o (fun x : R => 2%:R * Num.max (x - 0) 0 ^+ 1)).
  have := integrableZl measurableT 2%:R i3.
  by apply: eq_integrable => // x _; rewrite /= EFinM.
(* J = m(t) + m(-t) - 2 m(0) is the integral of the tent max(t - |x|, 0). *)
have hJ : m t + m (- t) - 2%:R * m 0 =
    \int[threshold_law]_x Num.max (t - `|x|) 0.
  rewrite /upper_moment -(RintegralD measurableT i1 i2).
  rewrite -(RintegralZl 2%:R measurableT i3) -(RintegralB measurableT iD iZ).
  by apply: eq_Rintegral => x _; rewrite !expr1 subr0 opprK tent_identity.
have pi0 : 0 < pi :> R by exact: pi_gt0.
(* The density is at most sqrt 2 / pi, so P[-t, t] <= 2 t sqrt 2 / pi. *)
have pdf_le (x : R) : semicircle_pdf sq2 x <= sq2 / pi.
  rewrite semicircle_pdfE ?gt_eqF // sqr_sqrtr ?ler0n //.
  have -> : 2%:R / (pi * 2%:R) = pi^-1 :> R.
    by rewrite invfM mulrCA divff ?mulr1 // pnatr_eq0.
  rewrite [X in _ <= X]mulrC; apply: ler_wpM2l; first by rewrite invr_ge0 ltW.
  by apply: ler_wsqrtr; rewrite lerBlDr lerDl sqr_ge0.
have PA : (threshold_law `[(- t)%R, t%R] <= (sq2 / pi * (t + t))%:E)%E.
  rewrite /= /semicircle_prob.
  apply: (@le_trans _ _
    (\int[@lebesgue_measure R]_(x in `[(- t)%R, t%R]) (cst (sq2 / pi)%:E x))%E).
    apply: ge0_le_integral => //.
    - by move=> x _; rewrite lee_fin semicircle_pdf_ge0.
    - apply/measurable_EFinP; apply: measurable_funTS.
      exact: measurable_semicircle_pdf.
    - by move=> x _; rewrite lee_fin pdf_le.
  rewrite integral_cst //.
  change ((sq2 / pi)%:E * (@lebesgue_measure R) `[(- t)%R, t%R]
    <= (sq2 / pi * (t + t))%:E)%E.
  rewrite lebesgue_measure_itv /=.
  case: ifPn => _; first by rewrite -EFinD -EFinM opprK.
  rewrite mule0 lee_fin; apply: mulr_ge0; last exact: addr_ge0.
  by apply: divr_ge0; exact: ltW.
(* The tent is at most t 1_[-t, t]. *)
have hA := @measurable_itv R (Interval (BLeft (- t)) (BRight t)).
have iA : threshold_law.-integrable [set: R]
    (EFin \o numfun.indic (`[(- t)%R, t%R])).
  exact: (integrable_indic threshold_law hA).
have iI : threshold_law.-integrable [set: R]
    (EFin \o (fun x : R => t * numfun.indic (`[(- t)%R, t%R]) x)).
  have := integrableZl measurableT t (integrable_indic threshold_law hA).
  by apply: eq_integrable => // x _; rewrite /= EFinM.
have iT : threshold_law.-integrable [set: R]
    (EFin \o (fun x : R => Num.max (t - `|x|) 0)).
  have := integrableB measurableT iD iZ.
  apply: eq_integrable => // x _.
  by rewrite /= -EFinB !expr1 subr0 opprK tent_identity.
have hJ1 : \int[threshold_law]_x Num.max (t - `|x|) 0 <=
    \int[threshold_law]_x (t * numfun.indic (`[(- t)%R, t%R]) x).
  apply: le_Rintegral => // x _.
  rewrite numfun.indicE.
  have [xi|xn] := boolP (x \in (`[(- t)%R, t%R] : set R)).
    by rewrite mulr1 ge_max t0 andbT gerBl normr_ge0.
  rewrite mulr0 ge_max lexx andbT subr_le0.
  have : ~ (`|x| <= t).
    by move=> h; move/negP: xn; apply; rewrite inE /= in_itv /= -ler_norml.
  by move=> /negP; rewrite -ltNge => /ltW.
have hJ2 : \int[threshold_law]_x (t * numfun.indic (`[(- t)%R, t%R]) x) =
    t * fine (threshold_law `[(- t)%R, t%R]).
  rewrite (RintegralZl t measurableT iA).
  by rewrite /Rintegral integral_indic // setIT.
have hP : fine (threshold_law `[(- t)%R, t%R]) <= sq2 / pi * (t + t).
  by rewrite -lee_fin fineK ?fin_num_measure.
have hJ0 : 0 <= \int[threshold_law]_x Num.max (t - `|x|) 0.
  by apply: Rintegral_ge0 => x _; rewrite le_max lexx orbT.
have e2 : t * (sq2 / pi * (t + t)) = 2%:R * (sq2 / pi * t ^+ 2) by ring.
have hJ3 : \int[threshold_law]_x Num.max (t - `|x|) 0 <=
    2%:R * (sq2 / pi * t ^+ 2).
  by rewrite -e2; apply: (le_trans hJ1); rewrite hJ2; exact: ler_wpM2l.
move: hJ hJ0 hJ3 hsym.
move: (\int[threshold_law]_x Num.max (t - `|x|) 0) => J.
move: (sq2 / pi * t ^+ 2) (m t) (m (- t)) (m 0) => c a b z.
move=> hJ hJ0 hJ3 hsym; clear -hJ hJ0 hJ3 hsym.
by apply/andP; split; lra.
Qed.

(* 2. Near C = 1. *)

Lemma condition_t_near_one : exists u1 : R, 0 < u1 /\
  forall C : R, 1 < C -> C < 1 + u1 -> condition_t C <= 2%:R * mu0 * (C - 1).
Proof.
exists 2%:R^-1; split; first by rewrite invr_gt0 ltr0n.
move=> C C1 Cu.
have C0 : 0 < C := lt_trans ltr01 C1.
have q0 := curve_sq2_gt0.
have pi0 : 0 < pi :> R by exact: pi_gt0.
have pi2 : 2%:R <= pi :> R by exact: pi_ge2.
have sq : sq2 * sq2 = 2%:R by rewrite -expr2 sqr_sqrtr // ler0n.
(* (sqrt 2 / pi) mu0 = 4 / (3 pi^2) <= 1/3 *)
have PM : sq2 / pi * mu0 <= 3%:R^-1.
  have hp := lt0r_neq0 pi0.
  have e : sq2 / pi * mu0 = 2%:R * (sq2 * sq2) / 3%:R * (pi^-1 * pi^-1).
    by move: (pi : R) hp => p hp; field.
  rewrite e sq.
  have ip0 : 0 < pi^-1 :> R by rewrite invr_gt0.
  have ip2 : pi^-1 <= 2%:R^-1 :> R by rewrite lef_pV2 ?posrE ?ltr0n.
  move: ip0 ip2; move: (pi^-1 : R) => ip ip0 ip2.
  by clear -ip0 ip2; nra.
have mu00 : 0 < mu0 :> R.
  by rewrite -curve_m0; apply: curve_m_gt0; exact: curve_sq2_gt0.
have [_ _ lo _] := condition_t_spec _ C1.
have u0 : 0 < C - 1 by rewrite subr_gt0.
have t00 : 0 < 2%:R * mu0 * (C - 1).
  by apply: mulr_gt0 => //; apply: mulr_gt0 => //; exact: ltr0n.
(* If t0 = 2 mu0 (C - 1) < t_C, then m(-t0) <= C m(C t0); but
   m(-t0) >= mu0 C and C m(C t0) < mu0 C by curve_m_expand. *)
move: t00 lo; set t0 := 2%:R * mu0 * (C - 1) => t00 lo.
rewrite leNgt; apply/negP => tlt.
have hle := lo t0 (ltW t00) tlt.
have hsym := upper_moment1_sym threshold_law2 threshold_law_sym t0.
have /andP[a1 _] := curve_m_expand t0 (ltW t00).
have Ct00 : 0 < C * t0 by rewrite mulr_gt0.
have /andP[_ a2] := curve_m_expand (C * t0) (ltW Ct00).
have ht0 : t0 = 2%:R * mu0 * (C - 1) by [].
clearbody t0.
have cc0 : 0 < C * (C - 1) by rewrite mulr_gt0.
have cc : C * (C - 1) < 3%:R / 4%:R.
  have h1 : C - 1 < 2%:R^-1 by rewrite ltrBlDl.
  have h2 : C * (C - 1) <= C * 2%:R^-1 by rewrite ler_wpM2l // ltW.
  apply: le_lt_trans h2 _.
  have -> : 3%:R / 4%:R = 3%:R / 2%:R * 2%:R^-1 :> R by field.
  rewrite ltr_pM2r ?invr_gt0 ?ltr0n //.
  by apply: lt_le_trans Cu _; rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
have k : sq2 / pi * (C * t0) < 2%:R^-1.
  have e : sq2 / pi * (C * t0) = 2%:R * (C * (C - 1)) * (sq2 / pi * mu0).
    by rewrite ht0; ring.
  rewrite e.
  have PM0 : 0 <= sq2 / pi * mu0.
    by apply: mulr_ge0; [apply: divr_ge0; exact: ltW | exact: ltW].
  move: PM PM0 cc cc0; move: (sq2 / pi * mu0) (C * (C - 1)) => p c PM PM0 cc cc0.
  by clear -PM PM0 cc cc0; nra.
have key : sq2 / pi * (C * t0) ^+ 2 < C * t0 / 2%:R.
  have -> : sq2 / pi * (C * t0) ^+ 2 = (C * t0) * (sq2 / pi * (C * t0)) by ring.
  by rewrite ltr_pM2l.
have a3 := ler_wpM2l (ltW C0) a2.
have a4 : C * (sq2 / pi * (C * t0) ^+ 2) < C * (C * t0 / 2%:R).
  by rewrite ltr_pM2l.
move: hle hsym a1 a3 a4 ht0.
move: (m (- t0)) (m t0) (m (C * t0)) => M1 Mt MC.
move: (sq2 / pi * (C * t0) ^+ 2) => Q.
move=> hle hsym a1 a3 a4 ht0.
clear -hle hsym a1 a3 a4 ht0 C0.
move: (mu0 : R) ht0 a1 a3 => M ht0 a1 a3.
have a3' : C * (MC - M + C * t0 / 2%:R) <= C * Q := a3.
by clear a3; lra.
Qed.

(* The clip energy is 1/2 minus g(t) = v(t) - v(C t) - t^2. *)
Lemma curve_energyE (C t : R) :
  clip_energy threshold_law C t = 2%:R^-1 + t ^+ 2 - s t + s (C * t).
Proof.
rewrite /clip_energy.
have := upper_moment2_sym threshold_law2 threshold_law_sym t.
rewrite threshold_second.
move: (s (- t)) (s t) (s (C * t)) => a b c h.
by rewrite -h; ring.
Qed.

(* The lower bound at t = mu0 u / C: alpha_C >= mu0 u t - u^2 t^2. *)
Lemma condition_alpha_lower (C : R) : 1 < C ->
  mu0 * (C - 1) * (mu0 * (C - 1) / C) - (C - 1) ^+ 2 * (mu0 * (C - 1) / C) ^+ 2
  <= condition_alpha C.
Proof.
move=> C1; have C0 : 0 < C := lt_trans ltr01 C1.
have u0 : 0 < C - 1 by rewrite subr_gt0.
have mu00 : 0 < mu0 :> R.
  by rewrite -curve_m0; apply: curve_m_gt0; exact: curve_sq2_gt0.
have ts0 : 0 <= mu0 * (C - 1) / C.
  by apply: divr_ge0; [apply: mulr_ge0; exact: ltW | exact: ltW].
have tsC : mu0 * (C - 1) / C * C = mu0 * (C - 1) by rewrite divfK // gt_eqF.
move: ts0 tsC; set ts := mu0 * (C - 1) / C => ts0 tsC.
rewrite condition_alphaE //.
have V := clip_value_le threshold_law C ts0.
rewrite curve_energyE in V.
have T := upper_moment2_taylor threshold_law2 ts ((C - 1) * ts).
have e : ts + (C - 1) * ts = C * ts by ring.
rewrite e in T; have T' := le_trans (ler_norm _) T.
have /andP[a1 _] := curve_m_expand ts ts0.
have b : 0 <= (C - 1) * ts * (m ts - mu0 + ts / 2%:R).
  by apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: ltW.
have h2 : C * ts ^+ 2 = mu0 * (C - 1) * ts.
  by rewrite -tsC; ring.
clearbody ts; move: V T' b h2.
move: (clip_value threshold_law C) (s ts) (s (C * ts)) (m ts) => V0 a c p.
move: (mu0 : R) => M V T' b h2.
by clear -V T' b h2; lra.
Qed.

(* The upper bound at t_C <= 2 mu0 u:
   alpha_C <= mu0 u t + (16 (sqrt 2 / pi) mu0^3 + 4 mu0^2) u^4. *)
Lemma condition_alpha_upper (C : R) : 1 < C ->
  condition_t C <= 2%:R * mu0 * (C - 1) ->
  condition_alpha C <= mu0 * (C - 1) * (mu0 * (C - 1) / C) +
    (16%:R * (sq2 / pi) * mu0 ^+ 3 + 4%:R * mu0 ^+ 2) * (C - 1) ^+ 4.
Proof.
move=> C1 tC.
have C0 : 0 < C := lt_trans ltr01 C1.
have u0 : 0 < C - 1 by rewrite subr_gt0.
have q0 := curve_sq2_gt0.
have pi0 : 0 < pi :> R by exact: pi_gt0.
have P0 : 0 <= sq2 / pi by apply: divr_ge0; exact: ltW.
have mu00 : 0 < mu0 :> R.
  by rewrite -curve_m0; apply: curve_m_gt0; exact: curve_sq2_gt0.
have [t0 _ VE] := condition_t_attained _ C1.
rewrite condition_alphaE // VE curve_energyE.
move: t0 tC; set tau := condition_t C => t0 tC.
have T := upper_moment2_taylor threshold_law2 tau ((C - 1) * tau).
have e : tau + (C - 1) * tau = C * tau by ring.
rewrite e in T.
have T' : - (((C - 1) * tau) ^+ 2) <=
    s (C * tau) - s tau + 2%:R * ((C - 1) * tau) * m tau.
  by move: T; rewrite ler_norml => /andP[].
have /andP[_ a2] := curve_m_expand tau t0.
have b : (C - 1) * tau * (m tau - mu0 + tau / 2%:R) <=
    (C - 1) * tau * (sq2 / pi * tau ^+ 2).
  by apply: ler_wpM2l => //; apply: mulr_ge0 => //; exact: ltW.
(* tau <= 2 mu0 u bounds the cubic and quadratic error terms. *)
have tM0 : 0 <= 2%:R * mu0 * (C - 1).
  by apply: mulr_ge0; [apply: mulr_ge0 => //; exact: ltW | exact: ltW].
have k3 : tau ^+ 3 <= (2%:R * mu0 * (C - 1)) ^+ 3 by rewrite lerXn2r ?nnegrE.
have k2 : tau ^+ 2 <= (2%:R * mu0 * (C - 1)) ^+ 2 by rewrite lerXn2r ?nnegrE.
have k3' : (C - 1) * (sq2 / pi) * tau ^+ 3 <=
    (C - 1) * (sq2 / pi) * (2%:R * mu0 * (C - 1)) ^+ 3.
  by apply: ler_wpM2l => //; apply: mulr_ge0 => //; exact: ltW.
have k2' : (C - 1) ^+ 2 * tau ^+ 2 <=
    (C - 1) ^+ 2 * (2%:R * mu0 * (C - 1)) ^+ 2.
  by apply: ler_wpM2l => //; exact: sqr_ge0.
(* 2 mu0 u tau - C tau^2 <= mu0 u ts, with C ts = mu0 u. *)
have ts0 : 0 <= mu0 * (C - 1) / C.
  by apply: divr_ge0; [apply: mulr_ge0; exact: ltW | exact: ltW].
have tsC : mu0 * (C - 1) / C * C = mu0 * (C - 1) by rewrite divfK // gt_eqF.
move: ts0 tsC; set ts := mu0 * (C - 1) / C => ts0 tsC.
have sq_ts : 0 <= C * (tau - ts) ^+ 2.
  by apply: mulr_ge0; [exact: ltW | exact: sqr_ge0].
have h3 : C * ts * tau = mu0 * (C - 1) * tau by rewrite -tsC; ring.
have h4 : C * ts ^+ 2 = mu0 * (C - 1) * ts by rewrite -tsC; ring.
clearbody ts tau.
move: T' a2 b k3' k2' h3 h4 sq_ts.
move: (s tau) (s (C * tau)) (m tau) => a c p.
move: (sq2 / pi) (mu0 : R) => P M.
move=> T' a2 b k3' k2' h3 h4 sq_ts.
by clear -T' b k3' k2' h3 h4 sq_ts; lra.
Qed.

Lemma condition_alpha_near_oneP : condition_alpha_near_one.
Proof.
have [u1 [u10 hu1]] := condition_t_near_one.
have q0 := curve_sq2_gt0.
have pi0 : 0 < pi :> R by exact: pi_gt0.
have P0 : 0 <= sq2 / pi by apply: divr_ge0; exact: ltW.
have mu00 : 0 < mu0 :> R.
  by rewrite -curve_m0; apply: curve_m_gt0; exact: curve_sq2_gt0.
exists (16%:R * (sq2 / pi) * mu0 ^+ 3 + 5%:R * mu0 ^+ 2), u1.
split.
  apply: ltr_wpDl; last by apply: mulr_gt0; [exact: ltr0n | exact: exprn_gt0].
  apply: mulr_ge0; last by apply: exprn_ge0; exact: ltW.
  by apply: mulr_ge0 => //; exact: ler0n.
split => // C C1 Cu.
have C0 : 0 < C := lt_trans ltr01 C1.
have u0 : 0 < C - 1 by rewrite subr_gt0.
have lo := condition_alpha_lower C C1.
have up := condition_alpha_upper C C1 (hu1 C C1 Cu).
(* mu0^2 = 8 / (9 pi^2) *)
have e8 : 8%:R / (9%:R * pi ^+ 2) = mu0 ^+ 2 :> R.
  have sq : sq2 * sq2 = 2%:R by rewrite -expr2 sqr_sqrtr // ler0n.
  have hp := lt0r_neq0 pi0.
  have -> : mu0 ^+ 2 = 4%:R * (sq2 * sq2) / (9%:R * pi ^+ 2) :> R.
    by move: (pi : R) hp => p hp; field.
  by rewrite sq; congr (_ / _); rewrite -natrM.
rewrite e8.
(* With ts = mu0 u / C and X = mu0 u ts = mu0^2 u^2 / C, the target is
   mu0^2 u^2 (1 - u) = X - X u^2, and 0 <= X u^2 <= mu0^2 u^4. *)
have ts0 : 0 <= mu0 * (C - 1) / C.
  by apply: divr_ge0; [apply: mulr_ge0; exact: ltW | exact: ltW].
have tsC : mu0 * (C - 1) / C * C = mu0 * (C - 1) by rewrite divfK // gt_eqF.
move: lo up ts0 tsC; set ts := mu0 * (C - 1) / C => lo up ts0 tsC.
have hXC : mu0 * (C - 1) * ts * C = mu0 ^+ 2 * (C - 1) ^+ 2.
  by rewrite -mulrA tsC; ring.
have tsu : ts <= mu0 * (C - 1).
  by rewrite -tsC ler_peMr //; exact: ltW.
have hts : (C - 1) ^+ 2 * ts ^+ 2 <= mu0 ^+ 2 * (C - 1) ^+ 4.
  have h : ts ^+ 2 <= (mu0 * (C - 1)) ^+ 2.
    by rewrite lerXn2r ?nnegrE //; apply: mulr_ge0; exact: ltW.
  have h' := ler_wpM2l (sqr_ge0 (C - 1)) h.
  by apply: (le_trans h'); rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
have X0 : 0 <= mu0 * (C - 1) * ts.
  by apply: mulr_ge0 => //; apply: mulr_ge0; exact: ltW.
have XM : mu0 * (C - 1) * ts <= mu0 ^+ 2 * (C - 1) ^+ 2.
  by rewrite -hXC ler_peMr //; exact: ltW.
have hXu1 : 0 <= mu0 * (C - 1) * ts * (C - 1) ^+ 2.
  by apply: mulr_ge0 => //; exact: sqr_ge0.
have hXu2 : mu0 * (C - 1) * ts * (C - 1) ^+ 2 <= mu0 ^+ 2 * (C - 1) ^+ 4.
  have h := ler_wpM2r (sqr_ge0 (C - 1)) XM.
  by apply: (le_trans h); rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
have hY : mu0 ^+ 2 * (C - 1) ^+ 2 * (1 - (C - 1)) =
    mu0 * (C - 1) * ts - mu0 * (C - 1) * ts * (C - 1) ^+ 2.
  by rewrite -hXC; ring.
rewrite hY; clearbody ts.
have hK : 0 <= 16%:R * (sq2 / pi) * mu0 ^+ 3 * (C - 1) ^+ 4.
  apply: mulr_ge0; last by apply: exprn_ge0; exact: ltW.
  apply: mulr_ge0; last by apply: exprn_ge0; exact: ltW.
  by apply: mulr_ge0 => //; exact: ler0n.
have hZ : 0 <= mu0 ^+ 2 * (C - 1) ^+ 4.
  by apply: mulr_ge0; apply: exprn_ge0; exact: ltW.
move: lo up hts hXu1 hXu2 hK hZ.
move: (condition_alpha C) (mu0 * (C - 1) * ts)
  (mu0 * (C - 1) * ts * (C - 1) ^+ 2) => A X Xu.
move: (16%:R * (sq2 / pi) * mu0 ^+ 3) => K1.
move=> lo up hts hXu1 hXu2 hK hZ.
rewrite ler_norml; apply/andP; split.
  by clear -lo hts hXu1 hK hZ; lra.
by clear -up hXu2 hK hZ; lra.
Qed.

(* The inversion of beta^2 = u^2 (1 - u) + O(u^4): u = beta + beta^2 / 2
   + O(beta^3), through F(u) - F(v) = (u - v) (u + v - (u^2 + u v + v^2))
   with F(u) = u^2 (1 - u) and v = beta + beta^2 / 2. *)
Lemma cubic_inverse (K b u : R) : 0 <= K -> 0 < b -> b <= 8%:R^-1 ->
  0 < u -> u <= 2%:R^-1 -> K * u ^+ 2 <= 4%:R^-1 ->
  `|b ^+ 2 - u ^+ 2 * (1 - u)| <= K * u ^+ 4 ->
  `|u - (b + b ^+ 2 / 2%:R)| <= 2%:R * (16%:R * K + 3%:R) * b ^+ 3.
Proof.
move=> K0 b0 b8 u0 u2 Ku hF.
move: hF; rewrite ler_norml => /andP[hF1 hF2].
(* u <= 2 b, since b^2 >= u^2 / 2 - u^2 / 4 *)
have Ku4 : K * u ^+ 4 <= u ^+ 2 / 4%:R.
  have -> : K * u ^+ 4 = (K * u ^+ 2) * u ^+ 2 by ring.
  have := ler_wpM2r (sqr_ge0 u) Ku.
  move=> h; apply: (le_trans h).
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
have Fu : u ^+ 2 / 2%:R <= u ^+ 2 * (1 - u).
  have : 0 <= u ^+ 2 * (2%:R^-1 - u).
    by apply: mulr_ge0; [exact: sqr_ge0 | rewrite subr_ge0].
  move=> h; rewrite -subr_ge0; apply: (le_trans h).
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
have hub : u ^+ 2 <= (2%:R * b) ^+ 2.
  move: hF1 Ku4 Fu; move: (K * u ^+ 4) (u ^+ 2 * (1 - u)) => A B.
  by move=> hF1 Ku4 Fu; rewrite exprMn; lra.
have u2b : u <= 2%:R * b.
  have b2 : 0 <= 2%:R * b by apply: mulr_ge0; [exact: ler0n | exact: ltW].
  by move: hub; rewrite ler_pXn2r // nnegrE ?ltW.
(* F(v) = b^2 - (5/4) b^4 - (3/4) b^5 - (1/8) b^6 *)
have b1 : b <= 1 by apply: (le_trans b8); rewrite invf_le1 ?ler1n ?ltr0n.
have Fv : (b + b ^+ 2 / 2%:R) ^+ 2 * (1 - (b + b ^+ 2 / 2%:R)) - b ^+ 2 =
    - (5%:R / 4%:R * b ^+ 4 + 3%:R / 4%:R * b ^+ 5 + 8%:R^-1 * b ^+ 6).
  by field.
have b54 : b ^+ 5 <= b ^+ 4 by rewrite exprSr ger_pMr ?exprn_gt0.
have b64 : b ^+ 6 <= b ^+ 4.
  have e6 : b ^+ 6 = b ^+ 4 * (b * b) by ring.
  rewrite e6 -[X in _ <= X](mulr1 (b ^+ 4)) ler_pM2l ?exprn_gt0 //.
  by apply: mulr_ile1 => //; exact: ltW.
have u4 : u ^+ 4 <= 16%:R * b ^+ 4.
  have h : u ^+ 4 <= (2%:R * b) ^+ 4.
    apply: lerXn2r => //; rewrite nnegrE; first exact: ltW.
    by apply: mulr_ge0; [exact: ler0n | exact: ltW].
  have e : (2%:R * b) ^+ 4 = 16%:R * b ^+ 4 by ring.
  by rewrite -e.
have Ku16 : K * u ^+ 4 <= 16%:R * K * b ^+ 4.
  have e : 16%:R * K * b ^+ 4 = K * (16%:R * b ^+ 4) by ring.
  by rewrite e; apply: ler_wpM2l.
(* |F(u) - F(v)| <= (16 K + 3) b^4 *)
set v := b + b ^+ 2 / 2%:R.
have b4 : 0 <= b ^+ 4 by apply: exprn_ge0; exact: ltW.
have b5 : 0 <= b ^+ 5 by apply: exprn_ge0; exact: ltW.
have b6 : 0 <= b ^+ 6 by apply: exprn_ge0; exact: ltW.
have dF : `|u ^+ 2 * (1 - u) - v ^+ 2 * (1 - v)| <=
    (16%:R * K + 3%:R) * b ^+ 4.
  move: hF1 hF2 Fv Ku16 b54 b64.
  move: (u ^+ 2 * (1 - u)) (v ^+ 2 * (1 - v)) => A B.
  move=> hF1 hF2 Fv Ku16 b54 b64.
  by rewrite ler_norml; apply/andP; split; lra.
(* the factor u + v - (u^2 + u v + v^2) is at least b / 2 *)
have b2 : 0 <= b ^+ 2 / 2%:R by apply: divr_ge0; [exact: sqr_ge0 | exact: ler0n].
have bv : b <= v by rewrite /v lerDl.
have vb : v <= 2%:R * b.
  rewrite /v; have : b ^+ 2 / 2%:R <= b.
    rewrite ler_pdivrMr ?ltr0n // expr2 ler_pM2l //.
    by apply: (le_trans b1); rewrite ler1n.
  by move=> h; lra.
have huv : 0 <= u * v.
  by apply: mulr_ge0; [exact: ltW | apply: (le_trans (ltW b0))].
have s12 : u + v <= 2%:R^-1.
  have : 4%:R * b <= 2%:R^-1.
    have -> : 2%:R^-1 = 4%:R * 8%:R^-1 :> R by field.
    by rewrite ler_pM2l ?ltr0n.
  by move=> h; lra.
have s0 : 0 <= u + v.
  by apply: addr_ge0; [exact: ltW | apply: (le_trans (ltW b0))].
have hs2 : (u + v) ^+ 2 <= (u + v) / 2%:R.
  by rewrite expr2 ler_wpM2l //; apply: (le_trans s12).
have G : b / 2%:R <= u + v - (u ^+ 2 + u * v + v ^+ 2).
  have e : (u + v) ^+ 2 = u ^+ 2 + u * v + v ^+ 2 + u * v by ring.
  by rewrite e in hs2; lra.
have fact : u ^+ 2 * (1 - u) - v ^+ 2 * (1 - v) =
    (u - v) * (u + v - (u ^+ 2 + u * v + v ^+ 2)) by ring.
rewrite fact normrM in dF.
have G0 : 0 <= u + v - (u ^+ 2 + u * v + v ^+ 2).
  by apply: le_trans G; apply: divr_ge0; [exact: ltW | exact: ler0n].
rewrite (ger0_norm G0) in dF.
have h1 : `|u - v| * (b / 2%:R) <=
    `|u - v| * (u + v - (u ^+ 2 + u * v + v ^+ 2)).
  by apply: ler_wpM2l.
have h2 := le_trans h1 dF.
have e : (16%:R * K + 3%:R) * b ^+ 4 =
    2%:R * (16%:R * K + 3%:R) * b ^+ 3 * (b / 2%:R) by field.
by rewrite e ler_pM2r ?divr_gt0 ?ltr0n // in h2.
Qed.

Lemma condition_star_near_zeroP : condition_star_near_zero.
Proof.
have [K [u0 [K0 [u00 hK]]]] := condition_alpha_near_oneP.
have q0 := curve_sq2_gt0.
have pi0 : 0 < pi :> R by exact: pi_gt0.
have hp := lt0r_neq0 pi0.
have hq := lt0r_neq0 q0.
have sq : sq2 * sq2 = 2%:R by rewrite -expr2 sqr_sqrtr // ler0n.
have mu00 : 0 < mu0 :> R.
  by rewrite -curve_m0; apply: curve_m_gt0; exact: curve_sq2_gt0.
have mu_le : mu0 <= sq2.
  by rewrite -curve_m0; apply: curve_m_le; rewrite oppr_le0 ltW.
have e8 : 8%:R / (9%:R * pi ^+ 2) = mu0 ^+ 2 :> R.
  have -> : mu0 ^+ 2 = 4%:R * (sq2 * sq2) / (9%:R * pi ^+ 2) :> R.
    by move: (pi : R) hp => p hp; field.
  by rewrite sq; congr (_ / _); rewrite -natrM.
(* the coefficients of (34) are 1 / mu0 and 1 / (2 mu0^2) *)
have e1 : 3%:R * pi / (2%:R * sq2) = mu0^-1 :> R.
  by move: (pi : R) hp => p hp; field.
have e2 : 9%:R * pi ^+ 2 / 16%:R = (2%:R * mu0 ^+ 2)^-1 :> R.
  by rewrite -e8; move: (pi : R) hp => p hp; field.
(* alpha_C > 0 for 1 < C < 2, by condition_alpha_lower *)
have apos (C : R) : 1 < C -> C < 2%:R -> 0 < condition_alpha C.
  move=> C1 C2; have lo := condition_alpha_lower C C1.
  apply: lt_le_trans lo.
  have C0 : 0 < C := lt_trans ltr01 C1.
  have u0' : 0 < C - 1 by rewrite subr_gt0.
  have u1 : C - 1 < 1 by rewrite ltrBlDl.
  have ts0 : 0 < mu0 * (C - 1) / C by rewrite divr_gt0 // mulr_gt0.
  have tsC : mu0 * (C - 1) / C * C = mu0 * (C - 1) by rewrite divfK // gt_eqF.
  move: ts0 tsC; set ts := mu0 * (C - 1) / C => ts0 tsC.
  have tsM : ts < mu0.
    rewrite -(ltr_pM2r C0) tsC; rewrite ltr_pM2l //; exact: lt_trans u1 C1.
  have uts : (C - 1) * ts < mu0.
    by apply: le_lt_trans tsM; rewrite ler_piMl // ltW.
  have -> : mu0 * (C - 1) * ts - (C - 1) ^+ 2 * ts ^+ 2 =
      ((C - 1) * ts) * (mu0 - (C - 1) * ts) by ring.
  by apply: mulr_gt0; [exact: mulr_gt0 | rewrite subr_gt0].
have M2 : mu0 ^+ 2 <= 2%:R :> R.
  have : mu0 ^+ 2 <= sq2 ^+ 2 by rewrite lerXn2r // nnegrE ltW.
  by rewrite sqr_sqrtr ?ler0n.
rewrite /condition_star_near_zero e1 e2; clear e1 e2.
move: mu00 mu_le M2 e8; move: (mu0 : R) => M mu00 mu_le M2 e8.
have M20 : 0 < M ^+ 2 by exact: exprn_gt0.
(* the constants: K' = K / mu0^2, u2 small, a0 = min(alpha_(1 + u2), mu0^2 / 64) *)
pose K' := K / M ^+ 2.
have K'0 : 0 <= K' by apply: divr_ge0; exact: ltW.
pose u2 := Num.min (u0 / 2%:R) (Num.min 4%:R^-1 (4%:R * (K' + 1))^-1).
have K'1 : 0 < 4%:R * (K' + 1).
  by apply: mulr_gt0; [exact: ltr0n | exact: ltr_wpDl].
have u20 : 0 < u2.
  rewrite /u2 !lt_min divr_gt0 ?ltr0n // invr_gt0 ltr0n /=.
  by rewrite invr_gt0.
have u2u0 : u2 < u0.
  have h : u2 <= u0 / 2%:R by rewrite /u2 ge_min lexx.
  apply: le_lt_trans h _.
  by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
have u24 : u2 <= 4%:R^-1 by rewrite /u2 !ge_min lexx /= orbT.
have u2K : u2 <= (4%:R * (K' + 1))^-1 by rewrite /u2 !ge_min lexx /= !orbT.
have C2 : 1 + u2 < 2%:R.
  have : u2 < 1 by apply: le_lt_trans u24 _; rewrite invf_lt1 ?ltr0n ?ltr1n.
  by move=> h; lra.
have a20 : 0 < condition_alpha (1 + u2) by apply: apos => //; rewrite ltrDl.
pose a0 := Num.min (condition_alpha (1 + u2)) (M ^+ 2 / 64%:R).
have a00 : 0 < a0 by rewrite /a0 lt_min a20 /= divr_gt0 ?ltr0n.
exists (2%:R * (16%:R * K' + 3%:R) / M ^+ 3), a0.
split.
  apply: divr_gt0; last exact: exprn_gt0.
  apply: mulr_gt0; first exact: ltr0n.
  by apply: ltr_wpDl; [apply: mulr_ge0 => //; exact: ler0n | exact: ltr0n].
split => // alpha al0 ala.
have aA : alpha < condition_alpha (1 + u2).
  by apply: lt_le_trans ala _; rewrite /a0 ge_min lexx.
have aM : alpha < M ^+ 2 / 64%:R.
  by apply: lt_le_trans ala _; rewrite /a0 ge_min lexx orbT.
have a4 : alpha < 4%:R^-1.
  move: aM M2; move: (M ^+ 2) => Q aM M2.
  by clear -aM M2; lra.
(* C_star(alpha) < 1 + u2, by the monotonicity of C |-> alpha_C *)
have [st1 stE below above] := condition_starP alpha al0 a4.
have Cs_lt : condition_star alpha < 1 + u2.
  rewrite ltNge; apply/negP; rewrite le_eqVlt => /orP[/eqP h | h].
    have e : condition_alpha (1 + u2) = alpha.
      by rewrite -stE; congr condition_alpha; exact: h.
    by move: aA; rewrite e ltxx.
  have h' : condition_alpha (1 + u2) < alpha.
    by apply: below h; rewrite ltrDl.
  by move: (lt_trans aA h'); rewrite ltxx.
have Cs0 : condition_star alpha < 1 + u0.
  by apply: lt_trans Cs_lt _; rewrite ltrD2l.
(* (11) at C_star(alpha) = 1 + u *)
have hu := hK _ st1 Cs0.
rewrite stE e8 in hu.
move: st1 Cs_lt hu; set Cs := condition_star alpha => st1 Cs_lt hu.
have uE : Cs = 1 + (Cs - 1) by ring.
rewrite uE; move: st1 Cs_lt hu; rewrite {1 2}uE.
move: (Cs - 1) => u; rewrite ltrDl => u0' Cs_lt hu.
have uu2 : u < u2 by move: Cs_lt; rewrite ltrD2l.
(* beta = sqrt alpha / mu0 *)
have saa : Num.sqrt alpha ^+ 2 = alpha by rewrite sqr_sqrtr // ltW.
have sa0 : 0 < Num.sqrt alpha by rewrite sqrtr_gt0.
move: saa sa0; move: (Num.sqrt alpha) => S saa sa0.
rewrite -saa in hu aM *.
have hM := lt0r_neq0 mu00.
have bE : M^-1 * S = S / M by rewrite mulrC.
have b2E : (2%:R * M ^+ 2)^-1 * S ^+ 2 = (S / M) ^+ 2 / 2%:R.
  by rewrite expr_div_n; field.
have b3E : 2%:R * (16%:R * K' + 3%:R) / M ^+ 3 * S ^+ 2 * S =
    2%:R * (16%:R * K' + 3%:R) * (S / M) ^+ 3.
  by rewrite expr_div_n; field.
rewrite bE b2E b3E.
have -> : 1 + u - (1 + S / M + (S / M) ^+ 2 / 2%:R) =
    u - (S / M + (S / M) ^+ 2 / 2%:R) by ring.
have b0 : 0 < S / M by rewrite divr_gt0.
have hb : `|(S / M) ^+ 2 - u ^+ 2 * (1 - u)| <= K' * u ^+ 4.
  have e : S ^+ 2 - M ^+ 2 * u ^+ 2 * (1 - u) =
      M ^+ 2 * ((S / M) ^+ 2 - u ^+ 2 * (1 - u)).
    by rewrite expr_div_n; field.
  rewrite e normrM (gtr0_norm M20) in hu.
  have e' : K' * u ^+ 4 = K * u ^+ 4 / M ^+ 2 by rewrite /K'; field.
  by rewrite e' ler_pdivlMr // mulrC.
have b8 : S / M <= 8%:R^-1.
  rewrite ler_pdivrMr // mulrC.
  have h : S ^+ 2 <= (8%:R^-1 * M) ^+ 2.
    rewrite exprMn; apply: ltW; apply: (lt_le_trans aM).
    by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
  have hm : 0 <= 8%:R^-1 * M.
    by apply: mulr_ge0; [rewrite invr_ge0 ler0n | exact: ltW].
  move: h; rewrite ler_pXn2r ?nnegrE ?(ltW sa0) // => h.
  by rewrite mulrC.
have uhalf : u <= 2%:R^-1.
  apply: le_trans (ltW uu2) _; apply: (le_trans u24).
  by rewrite lef_pV2 ?posrE ?ltr0n // ler_nat.
have h1 : (K' + 1) * u <= 4%:R^-1.
  have h : (K' + 1) * u <= (K' + 1) * (4%:R * (K' + 1))^-1.
    by apply: ler_wpM2l; [exact: addr_ge0 | exact: le_trans (ltW uu2) u2K].
  apply: (le_trans h); rewrite le_eqVlt; apply/orP; left; apply/eqP.
  have hk : K' + 1 != 0 by rewrite gt_eqF // ltr_wpDl.
  by rewrite invfM mulrCA divff ?mulr1.
have Ku : K' * u ^+ 2 <= 4%:R^-1.
  have hk : K' * u ^+ 2 <= (K' + 1) * u * u.
    rewrite expr2 mulrA; apply: ler_wpM2r; first exact: ltW.
    by apply: ler_wpM2r; [exact: ltW | rewrite lerDl].
  apply: (le_trans hk); apply: le_trans (ler_wpM2r (ltW u0') h1) _.
  rewrite -[X in _ <= X]mulr1 ler_wpM2l ?invr_ge0 ?ler0n //.
  by apply: (le_trans uhalf); rewrite invf_le1 ?ltr0n ?ler1n.
exact: cubic_inverse K'0 b0 b8 u0' uhalf Ku hb.
Qed.

(* 3. As C -> oo. *)

Lemma curve_s_edge (w : R) : w <= sq2 -> s w <= (sq2 - w) * m w.
Proof.
move=> hw.
have /andP[_ h] := upper_moment2_lipschitz threshold_law2 hw.
have s0 : s sq2 = 0 by rewrite -universality_sE universality_s_out.
rewrite s0 subr0 (curve_m_out sq2) // addr0 in h.
exact: h.
Qed.

Lemma condition_t_near_edge (e : R) : 0 < e ->
  exists C0 : R, 1 < C0 /\ forall C : R, C0 <= C -> sq2 - e <= C * condition_t C.
Proof.
move=> e0.
have q0 := curve_sq2_gt0.
have tpos C : 1 < C -> 0 <= C * condition_t C.
  move=> C1; have [t0 _ _ _] := condition_t_spec _ C1.
  by rewrite mulr_ge0 // ltW // (lt_trans ltr01 C1).
have [es|es] := leP sq2 e.
  exists 2%:R; split; first by rewrite ltr1n.
  move=> C C2; have C1 : 1 < C by apply: lt_le_trans C2; rewrite ltr1n.
  have := tpos C C1; move: (C * condition_t C) => x hx.
  by apply: le_trans hx; rewrite subr_le0.
(* m (C t_C) <= m (- t_C) / C <= sqrt 2 / C, while m (sqrt 2 - e) > 0 *)
pose p := m (sq2 - e).
have p0 : 0 < p by apply: curve_m_gt0; rewrite ltrBlDr ltrDl.
exists (Num.max 2%:R (sq2 / p + 1)); split.
  by rewrite lt_max ltr1n.
move=> C hC.
have C2 : 2%:R <= C by apply: le_trans hC; rewrite le_max lexx.
have Cp : sq2 / p + 1 <= C by apply: le_trans hC; rewrite le_max lexx orbT.
have C1 : 1 < C by apply: lt_le_trans C2; rewrite ltr1n.
have C0 : 0 < C := lt_trans ltr01 C1.
have [t0 tlt lo hi] := condition_t_spec _ C1.
have h1 := hi _ (lexx _).
have tq : condition_t C <= sq2.
  apply: le_trans (ltW tlt) _.
  by rewrite ler_pdivrMr // ler_peMr // ltW.
have h2 : m (- condition_t C) <= sq2 by apply: curve_m_le; rewrite lerN2.
rewrite leNgt; apply/negP => hlt.
have /andP[h3 _] := curve_m_lip _ _ (ltW hlt).
have h4 : C * p <= sq2.
  apply: le_trans h2; apply: le_trans h1; rewrite ler_wpM2l ?(ltW C0) //.
  by rewrite -subr_ge0.
have : sq2 / p + 1 <= sq2 / p.
  by apply: le_trans Cp _; rewrite ler_pdivlMr.
lra.
Qed.

Lemma condition_alpha_near_infinityP : condition_alpha_near_infinity.
Proof.
move=> eps e0.
have q0 := curve_sq2_gt0.
have sq : sq2 * sq2 = 2%:R by rewrite -expr2 sqr_sqrtr // ler0n.
have q2 : sq2 <= 2%:R.
  rewrite leNgt; apply/negP => h.
  have : 2%:R * 2%:R < sq2 * sq2 by apply: ltr_pM => //; rewrite ler0n.
  by rewrite sq; lra.
have mu_le : m 0 <= sq2 by apply: curve_m_le; rewrite oppr_le0 ltW.
have mu_ge0 : 0 <= m 0 by exact: upper_moment_ge0.
rewrite curve_m0 in mu_le mu_ge0.
pose e := eps / 12%:R.
have e0' : 0 < e by rewrite divr_gt0 // ltr0n.
have [C0 [C01 hC0]] := condition_t_near_edge _ e0'.
exists (Num.max C0 (4%:R / eps + 1)); split; first by rewrite lt_max C01.
move=> C hC.
have CC0 : C0 <= C by apply: le_trans hC; rewrite le_max lexx.
have Ce : 4%:R / eps + 1 <= C by apply: le_trans hC; rewrite le_max lexx orbT.
have C1 : 1 < C := lt_le_trans C01 CC0.
have C0' : 0 < C := lt_trans ltr01 C1.
have [t0 tlt lo hi] := condition_t_spec _ C1.
have hedge := hC0 C CC0.
have Ct : C * condition_t C <= sq2 by rewrite mulrC -ler_pdivlMr // ltW.
have tq : condition_t C <= sq2 / C := ltW tlt.
have aE : condition_alpha C =
    2%:R^-1 - s (- condition_t C) - s (C * condition_t C).
  by rewrite /condition_alpha !universality_sE.
(* v(-t) = 1/4 + 2 mu0 t + O(t^2), and v(C t) <= (sqrt 2 - C t) m(C t) *)
have T := upper_moment2_taylor threshold_law2 0 (- condition_t C).
rewrite add0r curve_m0 curve_s0 in T.
have hs := curve_s_edge _ Ct.
have hs0 : 0 <= s (C * condition_t C) by exact: upper_moment_ge0.
have h1 := hi _ (lexx _).
have h2 : m (- condition_t C) <= sq2.
  apply: curve_m_le; rewrite lerN2; apply: le_trans tq _.
  by rewrite ler_pdivrMr // ler_peMr // ltW.
have hm0 : 0 <= m (C * condition_t C) by exact: upper_moment_ge0.
have pi0 : pi != 0 :> R by rewrite gt_eqF // pi_gt0.
have e8 : 8%:R / (3%:R * pi) = 2%:R * m 0 * sq2.
  rewrite curve_m0; move: (pi : R) pi0 => p p0; move: (sq2) sq => q sq.
  have -> : 2%:R * (2%:R * q / (3%:R * p)) * q = 4%:R * (q * q) / (3%:R * p).
    by field.
  by rewrite sq; field.
have hCs : C * s (C * condition_t C) <= (sq2 - C * condition_t C) * sq2.
  apply: le_trans (_ : C * ((sq2 - C * condition_t C) * m (C * condition_t C))
                       <= _).
    by rewrite ler_wpM2l // ltW.
  rewrite mulrCA; apply: ler_wpM2l; first by rewrite subr_ge0.
  exact: le_trans h1 h2.
have hCt2 : C * condition_t C ^+ 2 <= 2%:R / C.
  have -> : C * condition_t C ^+ 2 = (C * condition_t C) * condition_t C.
    by rewrite expr2 mulrA.
  apply: le_trans (_ : sq2 * (sq2 / C) <= _).
    by apply: ler_pM => //; [rewrite mulr_ge0 // ltW | exact: ltW].
  by rewrite mulrA sq.
have h6 : 2%:R / C <= eps / 2%:R.
  rewrite ler_pdivrMr // mulrC -ler_pdivrMr ?divr_gt0 ?ltr0n //.
  apply: le_trans (_ : 4%:R / eps <= _); last first.
    by apply: le_trans Ce; rewrite lerDl.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  have ep : eps != 0 by rewrite gt_eqF.
  by field.
rewrite aE e8 curve_m0.
move: T hCt2 hCs hs0 hedge Ct mu_le mu_ge0 q2 h6.
set t := condition_t C; set X := s (- t); set Y := s (C * t).
move: mu0 => M.
clearbody t X Y.
move=> T hCt2 hCs hs0 hedge Ct mu_le mu_ge0 q2 h6.
rewrite sqrrN in T.
have h3 : `|C * (X - 4^-1 - 2%:R * t * M)| <= 2%:R / C.
  rewrite normrM gtr0_norm //; apply: le_trans hCt2.
  apply: ler_wpM2l; first exact: ltW.
  have -> : X - 4^-1 - 2%:R * t * M = X - 4^-1 + 2%:R * - t * M by ring.
  exact: T.
have eq : C * (4^-1 - (2^-1 - X - Y)) - 2%:R * M * sq2 =
    C * (X - 4^-1 - 2%:R * t * M) + C * Y - 2%:R * M * (sq2 - C * t).
  by field.
rewrite eq.
have h4 : (sq2 - C * t) * sq2 <= 2%:R * e.
  rewrite [2%:R * e]mulrC; apply: ler_pM => //; first by rewrite subr_ge0.
  by rewrite lerBlDr addrC -lerBlDr.
have h5 : 2%:R * M * (sq2 - C * t) <= 4%:R * e.
  have -> : 4%:R * e = (2%:R * 2%:R) * e by rewrite -natrM.
  apply: ler_pM; first by rewrite mulr_ge0 // ler0n.
    by rewrite subr_ge0.
    by apply: ler_wpM2l; [rewrite ler0n | exact: le_trans mu_le q2].
  by rewrite lerBlDr addrC -lerBlDr.
have h7 : 0 <= 2%:R * M * (sq2 - C * t).
  by rewrite !mulr_ge0 // ?ler0n // subr_ge0.
have hCY : 0 <= C * Y by rewrite mulr_ge0 // ltW.
have eE : e = eps / 12%:R by [].
move: h3; rewrite ler_norml => /andP[h3a h3b].
rewrite ler_norml.
move: h3a h3b hCs h4 h5 h7 hCY h6 eE.
set P := C * (X - _ - _); set Q := C * Y; set S := 2%:R * M * (sq2 - C * t).
set U := (sq2 - C * t) * sq2; set V := 2%:R / C.
clearbody P Q S U V e.
move=> h3a h3b hCs h4 h5 h7 hCY h6 eE.
clear -h3a h3b hCs h4 h5 h7 hCY h6 eE e0.
by apply/andP; split; lra.
Qed.

Lemma condition_star_near_quarterP : condition_star_near_quarter.
Proof.
move=> eps e0.
have [C1 [C11 hC1]] := condition_alpha_near_infinityP _ e0.
have a4 : condition_alpha C1 < 4%:R^-1.
  apply: lt_le_trans (condition_alpha_lt C1 (C1 + 1) C11 _) _.
    by rewrite ltrDl.
  by apply: condition_alpha_le4; apply: lt_trans C11 _; rewrite ltrDl.
(* for alpha > max (alpha_(C1), 1/8), C_star(alpha) >= C1 *)
pose M := Num.max (condition_alpha C1) 8%:R^-1.
have M4 : M < 4%:R^-1.
  by rewrite gt_max a4 /=; rewrite ltf_pV2 ?posrE ?ltr0n // ltr_nat.
exists (4%:R^-1 - M); split; first by rewrite subr_gt0.
move=> alpha ha a4'.
have hM : M < alpha by move: ha; rewrite opprB addrC subrK.
have hd1 : condition_alpha C1 < alpha by move: hM; rewrite gt_max => /andP[].
have a0 : 0 < alpha.
  move: hM; rewrite gt_max => /andP[_ h]; apply: lt_trans h.
  by rewrite invr_gt0 ltr0n.
have [st1 stE below above] := condition_starP alpha a0 a4'.
have hC : C1 <= condition_star alpha.
  rewrite leNgt; apply/negP => lt1.
  have := condition_alpha_lt _ _ st1 lt1.
  by rewrite stE => h; move: (lt_trans h hd1); rewrite ltxx.
by have := hC1 _ hC; rewrite stE mulrC.
Qed.

(* 4. The statement. *)

Theorem condition_endpoints : condition_endpoints_statement.
Proof.
split.
- exact: condition_alpha_near_oneP.
- exact: condition_alpha_near_infinityP.
- exact: condition_star_near_zeroP.
- exact: condition_star_near_quarterP.
Qed.

End endpoints.
