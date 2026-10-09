(* The Gaussian curve of the condition-number theorem, at Stdlib's R: item
   Q1 of phase 8 (notes/three-extensions-plan.md, sections 1.4 (a) and
   5.2). The definitions are those of ConditionDefinitions: t_C
   (condition_t), alpha_C (condition_alpha) and C_star (condition_star),
   with m and v the upper moments universality_m and universality_s of the
   semicircle law nu on [-sqrt 2, sqrt 2] (threshold_law of
   Gaussian/Threshold).

   Results.
   - condition_t_spec: for C > 1, 0 < t_C < sqrt 2 / C, and
     m(-t) - C m(C t), which is nondecreasing in t, is <= 0 on [0, t_C)
     and >= 0 on [t_C, +oo).
   - condition_alphaE: alpha_C = 1/2 - V(C), where
     V(C) = clip_value nu C is the infimum over t >= 0 of
     v(-t) + v(C t), the mean squared distance from X to [t, C t]
     (library/probability/variational.v); t_C is a minimizer, in the
     window [0, 3] (condition_t_attained).
   - condition_alpha_le4, condition_alpha_ge4, condition_alpha_near1:
     1/4 - 4 / C <= alpha_C <= 1/4 and alpha_C <= 4 (C - 1).
   - condition_alpha_lip, condition_alpha_lt: C |-> alpha_C is
     nondecreasing, 4-Lipschitz and strictly increasing on (1, +oo).
   - condition_alpha_left, condition_alpha_right: the C_- and C_+ of the
     two halves of the threshold.
   - condition_starP: for 0 < alpha < 1/4, C_star(alpha) > 1,
     alpha_(C_star) = alpha, alpha_C < alpha below C_star and alpha_C >
     alpha above it.

   No implicit function theorem is used: the regularity comes from the
   variational form alpha_C = 1/2 - V(C), V being an infimum of functions
   that are monotone and Lipschitz in C. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability normal_distribution.
From mathcomp Require Import sequences trigo realfun.
From GaussianAnalysis.probability Require Import semicircle_law variational.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation m := (upper_moment threshold_law 1).
Local Notation s := (upper_moment threshold_law 2).
Local Notation sq2 := (Num.sqrt 2%:R : R).

Section curve.

(* 1. The upper moments of the semicircle law. *)

Lemma curve_sq2_gt0 : 0 < sq2.
Proof. by rewrite sqrtr_gt0 ltr0n. Qed.

Lemma curve_m_lip (w1 w2 : R) : w1 <= w2 -> 0 <= m w1 - m w2 <= w2 - w1.
Proof. by move=> w12; exact: (upper_moment1_lipschitz threshold_law2 w12). Qed.

Lemma curve_m_gt0 (w : R) : w < sq2 -> 0 < m w.
Proof. by move=> ws; rewrite -universality_mE; exact: universality_m_gt0. Qed.

Lemma curve_m_out (w : R) : sq2 <= w -> m w = 0.
Proof. by move=> ws; rewrite -universality_mE; exact: universality_m_out. Qed.

Lemma curve_m_le (w : R) : - sq2 <= w -> m w <= sq2.
Proof.
move=> hw.
have e : m (- sq2) = sq2.
  by rewrite -universality_mE universality_m_sym universality_m_out ?add0r.
by have := curve_m_lip _ _ hw; rewrite e => /andP[h _]; lra.
Qed.

Lemma curve_s0 : s 0 = 4%:R^-1.
Proof.
have h := upper_moment2_sym threshold_law2 threshold_law_sym 0.
rewrite threshold_second oppr0 expr0n addr0 in h.
move: h; set a := upper_moment _ 2 0 => h.
have -> : a = (a + a) / 2%:R by field.
by rewrite h; field.
Qed.

Lemma curve_s_nincr (a b : R) : a <= b -> s b <= s a.
Proof.
move=> ab; have /andP[h _] := upper_moment2_lipschitz threshold_law2 ab.
by rewrite -subr_ge0.
Qed.

(* 2. t_C. *)

Lemma condition_t_spec (C : R) : 1 < C ->
  [/\ 0 < condition_t C, condition_t C < sq2 / C,
      forall t : R, 0 <= t -> t < condition_t C -> m (- t) <= C * m (C * t) &
      forall t : R, condition_t C <= t -> C * m (C * t) <= m (- t)].
Proof.
move=> C1.
have C0 : 0 < C := lt_trans ltr01 C1.
pose h (t : R) := m (- t) - C * m (C * t).
have hmono t t' : t <= t' -> h t <= h t'.
  move=> tt'; rewrite /h.
  have tt'' : - t' <= - t by rewrite lerN2.
  have /andP[a1 _] := curve_m_lip _ _ tt''.
  have /andP[a2 _] := curve_m_lip _ _ (ler_wpM2l (ltW C0) tt').
  have : 0 <= C * (m (C * t) - m (C * t')) by rewrite mulr_ge0 // ltW.
  move: a1 a2; set p := m (- t); set q := m (- t'); set u := m (C * t).
  set v := m (C * t').
  by move=> a1 a2 a3; rewrite mulrBr in a3; lra.
have hlip t t' : t <= t' -> h t' - h t <= (1 + C ^+ 2) * (t' - t).
  move=> tt'; rewrite /h.
  have tt'' : - t' <= - t by rewrite lerN2.
  have /andP[_ b1] := curve_m_lip _ _ tt''.
  have /andP[_ b2] := curve_m_lip _ _ (ler_wpM2l (ltW C0) tt').
  have b3 : C * (m (C * t) - m (C * t')) <= C * (C * t' - C * t).
    by rewrite ler_wpM2l // ltW.
  move: b1 b3; set p := m (- t); set q := m (- t'); set u := m (C * t).
  set v := m (C * t').
  move=> b1 b3; rewrite opprK in b1; rewrite mulrBr in b3.
  have e : C * (C * t' - C * t) = C ^+ 2 * (t' - t) by ring.
  by rewrite e in b3; nra.
have m0 : 0 < m 0 by apply: curve_m_gt0; exact: curve_sq2_gt0.
have h0 : h 0 < 0.
  rewrite /h oppr0 mulr0.
  have : m 0 < C * m 0 by rewrite ltr_pMl.
  by set q := m 0; lra.
have sC : 0 < sq2 / C by rewrite divr_gt0 // curve_sq2_gt0.
have hs : 0 < h (sq2 / C).
  have e : C * (sq2 / C) = sq2 by rewrite mulrC divfK // gt_eqF.
  rewrite /h e (curve_m_out sq2) // mulr0 subr0.
  by apply: curve_m_gt0; apply: lt_trans (curve_sq2_gt0); rewrite oppr_lt0.
pose T := [set t : R | 0 <= t <= sq2 / C /\ h t <= 0].
have tCE : condition_t C = sup T.
  rewrite /condition_t; congr sup; apply/seteqP.
  split => t /= [ht hm]; split => //.
    by rewrite /h subr_le0 -!universality_mE.
  by move: hm; rewrite /h subr_le0 -!universality_mE.
have T0 : T 0 by split; [rewrite lexx ltW | exact: ltW].
have Tub : ubound T (sq2 / C) by move=> t [/andP[_ ->]].
have hasT : has_sup T by split; [exists 0 | exists (sq2 / C)].
rewrite tCE.
have K0 : 0 < 1 + C ^+ 2 by rewrite ltr_pwDl // sqr_ge0.
have lo t : 0 <= t -> t < sup T -> h t <= 0.
  move=> t0 tt.
  have st : 0 < sup T - t by rewrite subr_gt0.
  have [e [/andP[e0 es] he] te] := sup_adherent st hasT.
  have tle : t <= e by move: te; rewrite opprB addrC subrK => /ltW.
  exact: le_trans (hmono _ _ tle) he.
(* sup T > 0: h is negative near 0 *)
pose t1 := Num.min (- h 0 / (2 * (1 + C ^+ 2))) (sq2 / C).
have t10 : 0 < t1.
  by rewrite lt_min sC andbT divr_gt0 // ?oppr_gt0 //; lra.
have Tt1 : T t1.
  split; first by rewrite (ltW t10) ge_min lexx orbT.
  have b : (1 + C ^+ 2) * t1 <= - h 0 / 2.
    have : t1 <= - h 0 / (2 * (1 + C ^+ 2)) by rewrite ge_min lexx.
    rewrite -(ler_pM2l K0) => hb; apply: le_trans hb _.
    have e : (1 + C ^+ 2) * (- h 0 / (2 * (1 + C ^+ 2))) = - h 0 / 2.
      by have hK := lt0r_neq0 K0; field.
    by rewrite e.
  by have := hlip 0 t1 (ltW t10); rewrite subr0; lra.
have tC0 : 0 < sup T := lt_le_trans t10 (sup_upper_bound hasT Tt1).
(* sup T < sqrt 2 / C: h is positive near sqrt 2 / C *)
pose dl := h (sq2 / C) / (1 + C ^+ 2).
have dl0 : 0 < dl by rewrite divr_gt0.
have Kdl : (1 + C ^+ 2) * dl = h (sq2 / C).
  by rewrite /dl mulrC divfK // gt_eqF.
have ub : ubound T (sq2 / C - dl).
  move=> t [/andP[t0 ts] ht]; rewrite leNgt; apply/negP => tl.
  have hl := hlip t (sq2 / C) ts.
  have : (1 + C ^+ 2) * (sq2 / C - t) < (1 + C ^+ 2) * dl.
    by rewrite ltr_pM2l //; lra.
  by rewrite Kdl; lra.
have tCs : sup T < sq2 / C by have := ge_sup (ex_intro _ 0 T0) ub; lra.
(* h >= 0 from sup T on *)
have hi t : sup T <= t -> 0 <= h t.
  move=> tt; rewrite leNgt; apply/negP => ht.
  have tlt : t < sq2 / C.
    by rewrite ltNge; apply/negP => st; have := hmono _ _ st; lra.
  pose t2 := Num.min (t + - h t / (2 * (1 + C ^+ 2))) (sq2 / C).
  have tt2 : t < t2.
    by rewrite lt_min tlt andbT ltrDl divr_gt0 // ?oppr_gt0 //; lra.
  have Tt2 : T t2.
    split.
      apply/andP; split; last by rewrite ge_min lexx orbT.
      by apply: le_trans (ltW tt2); apply: le_trans (ltW tC0) tt.
    have b : (1 + C ^+ 2) * (t2 - t) <= - h t / 2.
      have : t2 - t <= - h t / (2 * (1 + C ^+ 2)).
        by rewrite lerBlDl ge_min lexx.
      rewrite -(ler_pM2l K0) => hb; apply: le_trans hb _.
      have hK := lt0r_neq0 K0.
      have e : (1 + C ^+ 2) * (- h t / (2 * (1 + C ^+ 2))) = - h t / 2.
        by field.
      by rewrite e.
    have hl := hlip t t2 (ltW tt2).
    move: hl b ht; set u := h t2; set v := h t.
    set k := (1 + C ^+ 2) * (t2 - t).
    by move=> hl b ht; clear -hl b ht; lra.
  by have := sup_upper_bound hasT Tt2; move: tt tt2; clear; lra.
split => //.
- by move=> t t0 ttC; have := lo t t0 ttC; rewrite /h subr_le0.
- by move=> t tt; have := hi t tt; rewrite /h subr_ge0.
Qed.

(* 3. alpha_C = 1/2 - V(C). *)

(* t_C attains V(C) = clip_value threshold_law C, in the window [0, 3]. *)
Lemma condition_t_attained (C : R) : 1 < C ->
  [/\ 0 <= condition_t C, condition_t C <= 3%:R &
      clip_value threshold_law C = clip_energy threshold_law C (condition_t C)].
Proof.
move=> C1; have [t0 tlt lo hi] := condition_t_spec _ C1.
have C0 : 0 < C := lt_trans ltr01 C1.
split; first exact: ltW.
- apply: le_trans (ltW tlt) _.
  have q0 := curve_sq2_gt0.
  have sq : sq2 * sq2 = 2%:R by rewrite -expr2 sqr_sqrtr // ler0n.
  have h1 : sq2 / C <= sq2 by rewrite ler_pdivrMr // ler_peMr // ltW.
  apply: le_trans h1 _.
  move: q0 sq; set q := sq2; clearbody q.
  by move=> q0 sq; clear -q0 sq; nra.
- by rewrite (clip_value_attained threshold_law2 (ltW t0) lo hi).
Qed.

Theorem condition_alphaE (C : R) : 1 < C ->
  condition_alpha C = 2%:R^-1 - clip_value threshold_law C.
Proof.
move=> C1; have [t0 _ lo hi] := condition_t_spec _ C1.
rewrite (clip_value_attained threshold_law2 (ltW t0) lo hi) /clip_energy.
by rewrite /condition_alpha !universality_sE opprD addrA.
Qed.

Lemma condition_alpha_le4 (C : R) : 1 < C -> condition_alpha C <= 4%:R^-1.
Proof.
move=> C1; rewrite condition_alphaE //.
have : 4%:R^-1 <= clip_value threshold_law C.
  apply: clip_value_ge => t t0; rewrite /clip_energy -curve_s0.
  have h1 : s 0 <= s (- t) by apply: curve_s_nincr; rewrite oppr_le0.
  have h2 : 0 <= s (C * t) by exact: upper_moment_ge0.
  move: h1 h2; set a := s 0; set b := s (- t); set c := s (C * t).
  by clearbody a b c; move=> h1 h2; lra.
by set V := clip_value _ C; clearbody V; move=> h; lra.
Qed.

Lemma condition_alpha_ge4 (C : R) : 1 < C ->
  4%:R^-1 - 4%:R / C <= condition_alpha C.
Proof.
move=> C1; have C0 : 0 < C := lt_trans ltr01 C1.
have q0 := curve_sq2_gt0.
rewrite condition_alphaE //.
have t0 : 0 <= sq2 / C by rewrite divr_ge0 // ltW.
have tq : sq2 / C <= sq2 by rewrite ler_pdivrMr // ler_peMr // ltW.
have V := clip_value_le threshold_law C t0.
have e : C * (sq2 / C) = sq2 by rewrite mulrC divfK // gt_eqF.
rewrite /clip_energy e in V.
have s_out : s sq2 = 0 by rewrite -universality_sE universality_s_out.
have nt : - (sq2 / C) <= 0 by rewrite oppr_le0.
have /andP[_ L] := upper_moment2_lipschitz threshold_law2 nt.
have m1 : m (- (sq2 / C)) <= sq2 by apply: curve_m_le; rewrite lerN2.
have m2 : m 0 <= sq2 by apply: curve_m_le; rewrite oppr_le0 ltW.
have b : (0 - - (sq2 / C)) * (m (- (sq2 / C)) + m 0) <=
    sq2 / C * (2%:R * sq2).
  rewrite sub0r opprK; apply: ler_wpM2l => //.
  move: m1 m2; set p := m (- (sq2 / C)); set q := m 0.
  by clearbody p q; move=> m1 m2; clear -m1 m2; lra.
have e2 : sq2 / C * (2%:R * sq2) = 4%:R / C.
  have hC := lt0r_neq0 C0.
  have sq : sq2 * sq2 = 2%:R by rewrite -expr2 sqr_sqrtr // ler0n.
  have -> : sq2 / C * (2%:R * sq2) = 2%:R * (sq2 * sq2) / C by field.
  by rewrite sq; field.
rewrite s_out addr0 in V; rewrite curve_s0 in L.
move: V L b; rewrite e2.
set V0 := clip_value _ C; set P := s (- (sq2 / C)).
set Q := (0 - - (sq2 / C)) * _; set iC := 4%:R / C.
by clearbody V0 P Q iC; move=> V L b; clear -V L b; lra.
Qed.

(* V(C) - V(C') <= 4 (C' - C), through the minimizer t_(C') < sqrt 2. *)
Lemma curve_V_lip (C C' : R) : 1 <= C -> C <= C' -> 1 < C' ->
  clip_value threshold_law C - clip_value threshold_law C' <= 4%:R * (C' - C).
Proof.
move=> C1 CC C1'.
have C0 : 0 < C := lt_le_trans ltr01 C1.
have C0' : 0 < C' := lt_trans ltr01 C1'.
have q0 := curve_sq2_gt0.
have [t0 tlt lo hi] := condition_t_spec _ C1'.
rewrite (clip_value_attained threshold_law2 (ltW t0) lo hi).
set t := condition_t C' in t0 tlt lo hi *; clearbody t.
have V := clip_value_le threshold_law C (ltW t0).
have /andP[_ L] := clip_energy_C threshold_law2 (ltW t0) CC.
have tq : t <= sq2.
  apply: le_trans (ltW tlt) _.
  by rewrite ler_pdivrMr // ler_peMr // ltW.
have m1 : m (C * t) <= sq2.
  apply: curve_m_le; apply: le_trans (mulr_ge0 (ltW C0) (ltW t0)).
  by rewrite oppr_le0 ltW.
have m2 : m (C' * t) <= sq2.
  apply: curve_m_le; apply: le_trans (mulr_ge0 (ltW C0') (ltW t0)).
  by rewrite oppr_le0 ltW.
have d0 : 0 <= C' - C by rewrite subr_ge0.
have b1 : (C' - C) * t * (m (C * t) + m (C' * t)) <=
    (C' - C) * t * (2%:R * sq2).
  apply: ler_wpM2l; first by rewrite mulr_ge0 // ltW.
  move: m1 m2; set p := m (C * t); set q := m (C' * t).
  by clearbody p q; move=> m1 m2; clear -m1 m2; lra.
have b2 : (C' - C) * t * (2%:R * sq2) <= (C' - C) * sq2 * (2%:R * sq2).
  apply: ler_wpM2r; first by rewrite mulr_ge0 ?ler0n // ltW.
  exact: ler_wpM2l.
have e2 : (C' - C) * sq2 * (2%:R * sq2) = 4%:R * (C' - C).
  have sq : sq2 * sq2 = 2%:R by rewrite -expr2 sqr_sqrtr // ler0n.
  have -> : (C' - C) * sq2 * (2%:R * sq2) = 2%:R * (sq2 * sq2) * (C' - C).
    by ring.
  by rewrite sq; ring.
move: V L b1 b2; rewrite e2.
set V0 := clip_value _ C; set F := clip_energy _ C t.
set F' := clip_energy _ C' t; set Q := (C' - C) * t * (_ + _).
set Q' := (C' - C) * t * (2%:R * sq2).
by clearbody V0 F F' Q Q'; move=> V L b1 b2; clear -V L b1 b2; lra.
Qed.

Lemma condition_alpha_near1 (C : R) : 1 < C ->
  condition_alpha C <= 4%:R * (C - 1).
Proof.
move=> C1; rewrite condition_alphaE //.
have V1 : 2%:R^-1 <= clip_value threshold_law 1.
  apply: clip_value_ge => t t0; rewrite /clip_energy mul1r.
  have := upper_moment2_sym threshold_law2 threshold_law_sym t.
  by rewrite threshold_second => ->; rewrite lerDl sqr_ge0.
have := curve_V_lip _ C (lexx 1) (ltW C1) C1.
move: V1; set V0 := clip_value _ 1; set V := clip_value _ C.
by clearbody V0 V; move=> V1 h; lra.
Qed.

Lemma condition_alpha_lip (C C' : R) : 1 < C -> C <= C' ->
  0 <= condition_alpha C' - condition_alpha C <= 4%:R * (C' - C).
Proof.
move=> C1 CC; have C1' := lt_le_trans C1 CC.
rewrite !condition_alphaE //.
have h1 := clip_value_nincr threshold_law2 CC.
have h2 := curve_V_lip C C' (ltW C1) CC C1'.
move: h1 h2; set V := clip_value _ C; set V' := clip_value _ C'.
by clearbody V V'; move=> h1 h2; apply/andP; split; lra.
Qed.

(* v is strictly decreasing on (-oo, sqrt 2]. *)
Lemma curve_s_lt (a b : R) : a < b -> a < sq2 -> s b < s a.
Proof.
move=> ab aq.
have ma : 0 < m a := curve_m_gt0 a aq.
pose h := Num.min (b - a) (m a).
have h0 : 0 < h by rewrite lt_min subr_gt0 ab ma.
have hb : a + h <= b by rewrite -lerBrDl ge_min lexx.
have hm : h * h <= h * m a.
  by apply: ler_wpM2l; [exact: ltW | rewrite ge_min lexx orbT].
have hma : 0 < h * m a by rewrite mulr_gt0.
have T := upper_moment2_taylor threshold_law2 a h.
have T' := le_trans (ler_norm _) T.
have sb := curve_s_nincr _ _ hb.
rewrite expr2 in T'; clearbody h.
move: T' hm hma sb; set u := s (a + h); set v := s a; set w := s b.
set p := m a.
have -> : 2%:R * h * p = 2%:R * (h * p) by rewrite mulrA.
set q := h * p; set r := h * h.
by clearbody u v w p q r; move=> T' hm hma sb; lra.
Qed.

Lemma condition_alpha_lt (C C' : R) : 1 < C -> C < C' ->
  condition_alpha C < condition_alpha C'.
Proof.
move=> C1 CC; have C1' := lt_trans C1 CC.
have C0 : 0 < C := lt_trans ltr01 C1.
rewrite !condition_alphaE //.
have [t0 tlt lo hi] := condition_t_spec _ C1.
rewrite (clip_value_attained threshold_law2 (ltW t0) lo hi).
have V := clip_value_le threshold_law C' (ltW t0).
have Ct : C * condition_t C < sq2 by rewrite mulrC -ltr_pdivlMr.
have CCt : C * condition_t C < C' * condition_t C by rewrite ltr_pM2r.
have := curve_s_lt _ _ CCt Ct.
move: V; rewrite /clip_energy.
set V' := clip_value _ C'; set p := s (- _); set q := s (C * _).
set r := s (C' * _).
by clearbody V' p q r; move=> V h; lra.
Qed.

(* 4. The C_- and C_+ of the two halves of the threshold. *)

Lemma condition_alpha_left (C alpha : R) : 1 < C ->
  alpha < condition_alpha C ->
  exists2 Cm : R, 1 < Cm < C & alpha < condition_alpha Cm.
Proof.
move=> C1 aC.
pose Cm := Num.max (C - (condition_alpha C - alpha) / 8%:R) ((1 + C) / 2%:R).
have dm : C - (condition_alpha C - alpha) / 8%:R <= Cm by rewrite le_max lexx.
have hm : (1 + C) / 2%:R <= Cm by rewrite le_max lexx orbT.
have Cm1 : 1 < Cm by apply: lt_le_trans hm; lra.
have CmC : Cm < C.
  rewrite gt_max; apply/andP; split; last by lra.
  by rewrite ltrBlDr ltrDl divr_gt0 ?ltr0n // subr_gt0.
exists Cm; first by rewrite Cm1 CmC.
have /andP[_ L] := condition_alpha_lip Cm C Cm1 (ltW CmC).
clearbody Cm.
move: L dm aC; set a := condition_alpha C; set b := condition_alpha Cm.
by clearbody a b; move=> L dm aC; lra.
Qed.

Lemma condition_alpha_right (C alpha : R) : 1 < C ->
  condition_alpha C < alpha ->
  exists2 Cp : R, C < Cp & condition_alpha Cp < alpha.
Proof.
move=> C1 aC.
pose Cp := C + (alpha - condition_alpha C) / 8%:R.
have d0 : 0 < (alpha - condition_alpha C) / 8%:R.
  by rewrite divr_gt0 ?ltr0n // subr_gt0.
have CCp : C < Cp by rewrite ltrDl.
exists Cp; first exact: CCp.
have /andP[_ L] := condition_alpha_lip C Cp C1 (ltW CCp).
have e : Cp - C = (alpha - condition_alpha C) / 8%:R.
  by rewrite /Cp addrC addKr.
rewrite e in L; clearbody Cp.
move: L aC; set a := condition_alpha C; set b := condition_alpha Cp.
by clearbody a b; move=> L aC; lra.
Qed.

(* 5. C_star, the inverse of C |-> alpha_C on (0, 1/4). *)

Theorem condition_starP (alpha : R) : 0 < alpha -> alpha < 4%:R^-1 ->
  [/\ 1 < condition_star alpha,
      condition_alpha (condition_star alpha) = alpha,
      forall C : R, 1 < C -> C < condition_star alpha ->
        condition_alpha C < alpha &
      forall C : R, condition_star alpha < C -> alpha < condition_alpha C].
Proof.
move=> a0 a4.
pose S := [set C : R | 1 < C /\ alpha <= condition_alpha C].
have SE : condition_star alpha = inf S by [].
(* S is not empty: alpha_C >= 1/4 - 4 / C *)
pose C0 := 4%:R / (4%:R^-1 - alpha).
have d0 : 0 < 4%:R^-1 - alpha by rewrite subr_gt0.
have C0E : 4%:R / C0 = 4%:R^-1 - alpha.
  by rewrite /C0 invf_div mulrCA mulfV ?mulr1 // pnatr_eq0.
have C01 : 1 < C0 by rewrite /C0 ltr_pdivlMr // mul1r; lra.
have SC0 : S C0.
  split => //; have := condition_alpha_ge4 C0 C01; rewrite C0E.
  by set a := condition_alpha C0; clearbody a; move=> h; lra.
(* S lies above 1 + alpha / 4: alpha_C <= 4 (C - 1) *)
have lbS : lbound S (1 + alpha / 4%:R).
  move=> C [C1 aC]; have := condition_alpha_near1 C C1.
  by move: aC; set a := condition_alpha C; clearbody a; move=> aC h; lra.
have nS : S !=set0 by exists C0.
have hasS : has_inf S by split; [exact: nS | exists (1 + alpha / 4%:R)].
have st1 : 1 < condition_star alpha.
  rewrite SE; apply: lt_le_trans (lb_le_inf nS lbS).
  by rewrite ltrDl divr_gt0 // ltr0n.
have below C : 1 < C -> C < condition_star alpha -> condition_alpha C < alpha.
  move=> C1 Cs; rewrite ltNge; apply/negP => aC.
  have SC : S C by split.
  have := ge_inf (proj2 hasS) SC; rewrite -SE.
  by move: Cs; set c := condition_star alpha; clearbody c; move=> Cs h; lra.
have above C : condition_star alpha < C -> alpha < condition_alpha C.
  move=> sC.
  have e0 : 0 < C - inf S by rewrite subr_gt0 -SE.
  have [C' [C1' aC'] C'C] := inf_adherent e0 hasS.
  have CC : C' < C by move: C'C; rewrite addrC subrK.
  exact: le_lt_trans aC' (condition_alpha_lt C' C C1' CC).
split => //.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite leNgt; apply/negP => aS.
  have [Cm /andP[Cm1 CmS] aCm] := condition_alpha_left _ _ st1 aS.
  have := below Cm Cm1 CmS.
  by move: aCm; set a := condition_alpha Cm; clearbody a; move=> aCm h; lra.
rewrite leNgt; apply/negP => aS.
have [Cp sCp aCp] := condition_alpha_right _ _ st1 aS.
have := above Cp sCp.
by move: aCp; set a := condition_alpha Cp; clearbody a; move=> aCp h; lra.
Qed.

End curve.
