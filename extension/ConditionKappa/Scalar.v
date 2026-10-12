(* The root of the condition-number curve at fourth moment kappa, at
   Stdlib's R: item S1 of phase 11 (notes/phase11-plan.md, section 5; the
   math plan notes/general-fourth-moment-condition-plan.md, section 3, S1;
   lane C). The definitions are those of ConditionKappaDefinitions.

   Setting. m and v are universality_m and universality_s, the upper
   moments of the semicircle law nu on [-sqrt 2, sqrt 2] (threshold_law of
   Gaussian/Threshold). For kappa > 1 and C > 1, c = (kappa - 3) / 2 and
   r = c / (1 + c) = (kappa - 3) / (kappa - 1), so r < 1;
     L(u) = (u + r (C - 1)^2 m(u)) / C,    F(u) = m(-L(u)) - C m(u),
   the root u = sup {u in [0, sqrt 2] : F(u) <= 0} and ell = L(u).

   Results.
   - kappa_m_lt: m is strictly decreasing below sqrt 2: m(v) < m(u) for
     u < v and u < sqrt 2, since m(u) - m(v) >= (v - u) nu(]v, +oo[) and
     nu charges ]v, +oo[ for v < sqrt 2 (semicircle_prob_gt0).
   - condition_kappa_F_lt: F is strictly increasing on ]-oo, sqrt 2]. For
     u < v with b = m(u) - m(v) > 0: if L(u) <= L(v), F(v) - F(u) >= C b;
     otherwise, m being 1-Lipschitz, C (F(v) - F(u)) >= (v - u)
     + (C^2 - r (C - 1)^2) b > 0, since r (C - 1)^2 < (C - 1)^2 < C^2.
   - condition_kappa_F_lip: F(v) - F(u) <= K (v - u) for u <= v, with
     K = (1 + |r| (C - 1)^2) / C + C.
   - condition_kappa_F0, condition_kappa_Fsq2: F(0) < 0 < F(sqrt 2). At 0,
     m(-L(0)) <= m(0) if L(0) <= 0, and otherwise
     m(-L(0)) = m(L(0)) + L(0) <= m(0) + L(0) with L(0) < (C - 1) m(0); at
     sqrt 2, m(sqrt 2) = 0 < m(-sqrt 2 / C).
   - condition_kappa_u_spec: 0 < u < sqrt 2, F(u) = 0, and u is the only
     zero of F in [0, sqrt 2]. The least upper bound is handled as in
     condition_t_spec of Condition/Curve.v, with the monotonicity and the
     Lipschitz bound of F in place of continuity.
   - condition_kappa_ell_spec: -sqrt 2 < ell < u. First m(-ell) = C m(u)
     > 0. If ell >= u, then, since m decreases and m(-ell) = m(ell) + ell,
     C m(u) = m(ell) + ell <= m(u) + ell, so (C - 1) m(u) <= ell and
     C ell - u >= (C - 1) ell >= (C - 1)^2 m(u), against
     C ell - u = r (C - 1)^2 m(u), since r < 1 and m(u) > 0.
   - condition_kappa_root_holds: conjunct (a) of the curve statement,
     condition_kappa_root kappa, for kappa > 1. *)

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
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
From EllipsoidUniversality Require Import ConditionKappaCurveStatement.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation um := universality_m.
Local Notation sq2 := (Num.sqrt 2%:R : R).

(* 1. The upper moment m of the semicircle law. *)

Lemma kappa_sq2_gt0 : 0 < sq2.
Proof. by rewrite sqrtr_gt0 ltr0n. Qed.

Lemma kappa_m_lip (w1 w2 : R) : w1 <= w2 -> 0 <= um w1 - um w2 <= w2 - w1.
Proof.
move=> w12; rewrite !universality_mE.
exact: (upper_moment1_lipschitz threshold_law2 w12).
Qed.

Lemma kappa_m_sym (w : R) : um (- w)%R = um w + w.
Proof. by have := universality_m_sym w; rewrite RoppE. Qed.

(* m is strictly decreasing below sqrt 2. *)
Lemma kappa_m_lt (u v : R) : u < v -> u < sq2 -> um v < um u.
Proof.
move=> uv us.
have [vs|sv] := ltP v sq2; last first.
  by rewrite (universality_m_out _ sv); exact: universality_m_gt0.
have s2 : sq2 != 0 by rewrite gt_eqF // kappa_sq2_gt0.
have s2abs : `|sq2| = sq2 by rewrite ger0_norm // ltW // kappa_sq2_gt0.
pose A := `]v, +oo[%classic : set (measurableTypeR R).
have mA : measurable A by exact: measurable_itv.
have PA : (0 < threshold_law A)%E.
  by apply: (semicircle_prob_gt0 s2); rewrite s2abs.
have iA : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => numfun.indic A x : R)).
  exact: integrable_indic.
have EA : \int[threshold_law]_x (numfun.indic A x : R) = fine (threshold_law A).
  by rewrite /Rintegral integral_indic // setIT.
have muA : 0 < fine (threshold_law A).
  apply: fine_gt0; rewrite PA /=.
  exact: le_lt_trans (probability_le1 _ mA) (ltry 1).
have iZ : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => (v - u) * numfun.indic A x)).
  have -> : (EFin \o (fun x : measurableTypeR R =>
      (v - u) * numfun.indic A x)) =
      (fun x => (v - u)%:E * (EFin \o numfun.indic A) x)%E.
    by apply/funext => x /=; rewrite EFinM.
  by apply: integrableZl.
have iv := integrable_upper_pow threshold_law2 v (leqnSn 1).
have iu := integrable_upper_pow threshold_law2 u (leqnSn 1).
rewrite !universality_mE.
have key : upper_moment threshold_law 1 v + (v - u) * fine (threshold_law A) <=
    upper_moment threshold_law 1 u.
  rewrite -EA -RintegralZl // /upper_moment -RintegralD //.
  apply: le_Rintegral => //.
    have := integrableD measurableT iv iZ.
    by apply: eq_integrable => // x _ /=; rewrite EFinD.
  move=> x _; rewrite !expr1 /numfun.indic /=.
  case: (boolP (x \in A)) => xA.
    have xv : v < x by move: xA; rewrite inE /A /= in_itv /= andbT.
    rewrite mulr1.
    have -> : Num.max (x - v) 0 = x - v by apply/max_idPl; rewrite subr_ge0 ltW.
    have -> : Num.max (x - u) 0 = x - u.
      by apply/max_idPl; rewrite subr_ge0 ltW // (lt_trans uv xv).
    by rewrite addrA subrK.
  rewrite mulr0 addr0.
  have [xv|xv] := leP (x - v) 0; first by rewrite le_max lexx orbT.
  by rewrite le_max; apply/orP; left; rewrite lerD2l lerN2 ltW.
have : 0 < (v - u) * fine (threshold_law A) by rewrite mulr_gt0 // subr_gt0.
move: key.
move: (upper_moment threshold_law 1 v) (upper_moment threshold_law 1 u)
  ((v - u) * fine (threshold_law A)) => a b c.
lra.
Qed.

(* 2. The function F. *)

Lemma kappa_r_lt1 (kappa : R) : 1 < kappa -> (kappa - 3%:R) / (kappa - 1) < 1.
Proof. by move=> k1; rewrite ltr_pdivrMr ?subr_gt0 // mul1r; lra. Qed.

Lemma condition_kappa_LE (C kappa u : R) : 0 < C ->
  C * condition_kappa_L C kappa u =
  u + (kappa - 3%:R) / (kappa - 1) * (C - 1) ^+ 2 * um u.
Proof. by move=> C0; rewrite /condition_kappa_L mulrC divfK // gt_eqF. Qed.

(* F is strictly increasing on ]-oo, sqrt 2]. *)
Lemma condition_kappa_F_lt (C kappa u v : R) : 1 < C -> 1 < kappa ->
  u < v -> u < sq2 -> condition_kappa_F C kappa u < condition_kappa_F C kappa v.
Proof.
move=> C1 k1 uv us.
have C0 : 0 < C := lt_trans ltr01 C1.
have r1 := kappa_r_lt1 kappa k1.
have b0 : 0 < um u - um v by rewrite subr_gt0; exact: kappa_m_lt.
have hLu := condition_kappa_LE C kappa u C0.
have hLv := condition_kappa_LE C kappa v C0.
rewrite /condition_kappa_F.
move: r1 hLu hLv; set r := (kappa - 3%:R) / (kappa - 1) => r1 hLu hLv.
set Lu := condition_kappa_L C kappa u in hLu *.
set Lv := condition_kappa_L C kappa v in hLv *.
have Cb : 0 < C * (um u - um v) by rewrite mulr_gt0.
have [LuLv|LvLu] := leP Lu Lv.
  (* L(u) <= L(v): m(-L(v)) >= m(-L(u)) *)
  have LL : (- Lv)%R <= (- Lu)%R by rewrite lerN2.
  have /andP[h1 _] := kappa_m_lip _ _ LL.
  move: h1 Cb; rewrite mulrBr.
  move: (um (- Lv)%R) (um (- Lu)%R) (C * um u) (C * um v) => a b c e.
  lra.
(* L(v) < L(u): m is 1-Lipschitz and r (C - 1)^2 < C^2 *)
have LL : (- Lu)%R <= (- Lv)%R by rewrite lerN2 ltW.
have /andP[_ h1] := kappa_m_lip _ _ LL.
have k0 : 0 < (C - 1) ^+ 2 by rewrite exprn_gt0 // subr_gt0.
have kC : (C - 1) ^+ 2 < C ^+ 2.
  by rewrite ltrXn2r ?subr_ge0 ?(ltW C1) ?(ltW C0) // ltrBlDr ltrDl.
have rk : r * (C - 1) ^+ 2 < C ^+ 2.
  apply: le_lt_trans kC.
  by rewrite -[X in _ <= X]mul1r ler_wpM2r // ltW.
have hb : r * (C - 1) ^+ 2 * (um u - um v) < C ^+ 2 * (um u - um v).
  by rewrite ltr_pM2r.
have h2 : C * (um (- Lu)%R - um (- Lv)%R) <= C * Lu - C * Lv.
  by rewrite -mulrBr ler_wpM2l ?(ltW C0) //; move: h1; rewrite !opprK; lra.
have e : C * Lu - C * Lv = (u - v) + r * (C - 1) ^+ 2 * (um u - um v).
  by rewrite hLu hLv; ring.
have h3 : C * (um (- Lu)%R - um (- Lv)%R) < C * (C * (um u - um v)).
  rewrite mulrA -expr2.
  move: h2 e hb uv.
  move: (C * (um (- Lu)%R - um (- Lv)%R)) (C * Lu) (C * Lv)
    (r * (C - 1) ^+ 2 * (um u - um v)) (C ^+ 2 * (um u - um v)) => a b c e f.
  lra.
move: h3; rewrite ltr_pM2l // mulrBr.
clear e.
move: (um (- Lu)%R) (um (- Lv)%R) (C * um u) (C * um v) => a b c f.
lra.
Qed.

(* An upper Lipschitz bound for F. *)
Lemma condition_kappa_F_lip (C kappa u v : R) : 1 < C -> u <= v ->
  condition_kappa_F C kappa v - condition_kappa_F C kappa u <=
  ((1 + `|(kappa - 3%:R) / (kappa - 1)| * (C - 1) ^+ 2) / C + C) * (v - u).
Proof.
move=> C1 uv.
have C0 : 0 < C := lt_trans ltr01 C1.
have hLu := condition_kappa_LE C kappa u C0.
have hLv := condition_kappa_LE C kappa v C0.
rewrite /condition_kappa_F.
move: hLu hLv; set r := (kappa - 3%:R) / (kappa - 1) => hLu hLv.
set Lu := condition_kappa_L C kappa u in hLu *.
set Lv := condition_kappa_L C kappa v in hLv *.
have /andP[b0 b1] := kappa_m_lip u v uv.
have k0 : 0 <= (C - 1) ^+ 2 by exact: sqr_ge0.
have hr : - (r * (C - 1) ^+ 2 * (um u - um v)) <= `|r| * (C - 1) ^+ 2 * (v - u).
  apply: le_trans (ler_norm _) _.
  rewrite normrN normrM (ger0_norm b0) normrM (ger0_norm k0).
  by apply: ler_wpM2l => //; rewrite mulr_ge0.
have e : C * Lv - C * Lu = (v - u) - r * (C - 1) ^+ 2 * (um u - um v).
  by rewrite hLv hLu; ring.
(* C (m(-L(v)) - m(-L(u))) <= C |L(v) - L(u)| <= (1 + |r| (C - 1)^2) (v - u) *)
have hL : C * (um (- Lv)%R - um (- Lu)%R) <=
    (1 + `|r| * (C - 1) ^+ 2) * (v - u).
  have [LuLv|LvLu] := leP Lu Lv.
    have LL : (- Lv)%R <= (- Lu)%R by rewrite lerN2.
    have /andP[_ h1] := kappa_m_lip _ _ LL.
    have h2 : C * (um (- Lv)%R - um (- Lu)%R) <= C * Lv - C * Lu.
      by rewrite -mulrBr ler_wpM2l ?(ltW C0) //; move: h1; rewrite opprK; lra.
    rewrite mulrDl mul1r.
    move: h2 e hr.
    move: (C * (um (- Lv)%R - um (- Lu)%R)) (C * Lv) (C * Lu)
      (r * (C - 1) ^+ 2 * (um u - um v)) (`|r| * (C - 1) ^+ 2 * (v - u)).
    move=> a b c f g; lra.
  have LL : (- Lu)%R <= (- Lv)%R by rewrite lerN2 ltW.
  have /andP[h1 _] := kappa_m_lip _ _ LL.
  apply: (@le_trans _ _ 0).
    by rewrite pmulr_rle0 // subr_le0; move: h1; rewrite subr_ge0.
  by rewrite mulr_ge0 // ?subr_ge0 // addr_ge0 // mulr_ge0.
have hL' : um (- Lv)%R - um (- Lu)%R <=
    (1 + `|r| * (C - 1) ^+ 2) / C * (v - u).
  by rewrite mulrAC ler_pdivlMr // mulrC.
have hC : C * (um u - um v) <= C * (v - u) by rewrite ler_wpM2l // ltW.
rewrite mulrDl.
move: hL' hC; rewrite !mulrBr.
move: (um (- Lv)%R) (um (- Lu)%R) ((1 + `|r| * (C - 1) ^+ 2) / C * (v - u))
  (C * um u) (C * um v) (C * v) (C * u) => a b c f g h i.
lra.
Qed.

Lemma condition_kappa_F0 (C kappa : R) : 1 < C -> 1 < kappa ->
  condition_kappa_F C kappa 0 < 0.
Proof.
move=> C1 k1.
have C0 : 0 < C := lt_trans ltr01 C1.
have r1 := kappa_r_lt1 kappa k1.
have m0 : 0 < um 0 by apply: universality_m_gt0; exact: kappa_sq2_gt0.
have hL := condition_kappa_LE C kappa 0 C0.
have Cm : um 0 < C * um 0 by rewrite ltr_pMl.
rewrite /condition_kappa_F.
move: r1 hL; set r := (kappa - 3%:R) / (kappa - 1) => r1 hL.
set L0 := condition_kappa_L C kappa 0 in hL *.
have [L0n|L0p] := leP L0 0.
  (* L(0) <= 0: m(-L(0)) <= m(0) < C m(0) *)
  have L0n' : 0 <= (- L0)%R by rewrite oppr_ge0.
  have /andP[h _] := kappa_m_lip _ _ L0n'.
  by move: h Cm; move: (um 0) (um (- L0)%R) (C * um 0) => a b c; lra.
(* L(0) > 0: m(-L(0)) = m(L(0)) + L(0) <= m(0) + L(0), and
   L(0) < (C - 1) m(0) *)
have hs := kappa_m_sym L0.
have /andP[h _] := kappa_m_lip _ _ (ltW L0p).
have k0 : 0 < (C - 1) ^+ 2 by rewrite exprn_gt0 // subr_gt0.
have h1 : C * L0 < (C - 1) ^+ 2 * um 0.
  rewrite hL add0r -mulrA -[X in _ < X]mul1r ltr_pM2r //.
  by rewrite mulr_gt0.
have h2 : (C - 1) ^+ 2 * um 0 < C * ((C - 1) * um 0).
  rewrite expr2 -mulrA ltr_pM2r ?mulr_gt0 ?subr_gt0 //.
  by rewrite ltrBlDr ltrDl.
have h3 : L0 < (C - 1) * um 0.
  by rewrite -(ltr_pM2l C0); exact: lt_trans h1 h2.
move: hs h h3 Cm; rewrite mulrBl mul1r.
by move: (um 0) (um L0) (um (- L0)%R) (C * um 0) => a b c f; lra.
Qed.

Lemma condition_kappa_Fsq2 (C kappa : R) : 1 < C ->
  0 < condition_kappa_F C kappa sq2.
Proof.
move=> C1; have C0 : 0 < C := lt_trans ltr01 C1.
rewrite /condition_kappa_F (universality_m_out sq2 (lexx _)) mulr0 subr0.
apply: universality_m_gt0.
rewrite /condition_kappa_L (universality_m_out sq2 (lexx _)) mulr0 addr0.
apply: lt_trans kappa_sq2_gt0.
by rewrite oppr_lt0 divr_gt0 // kappa_sq2_gt0.
Qed.

(* 3. The root. *)

Lemma condition_kappa_u_spec (C kappa : R) : 1 < C -> 1 < kappa ->
  [/\ 0 < condition_kappa_u C kappa, condition_kappa_u C kappa < sq2,
      condition_kappa_F C kappa (condition_kappa_u C kappa) = 0 &
      forall u : R, 0 <= u <= sq2 -> condition_kappa_F C kappa u = 0 ->
        u = condition_kappa_u C kappa].
Proof.
move=> C1 k1.
have C0 : 0 < C := lt_trans ltr01 C1.
have hlip u v := condition_kappa_F_lip C kappa u v C1.
have F0 := condition_kappa_F0 C kappa C1 k1.
have Fs := condition_kappa_Fsq2 C kappa C1.
have hlt u v : u < v -> u < sq2 ->
    condition_kappa_F C kappa u < condition_kappa_F C kappa v.
  by move=> uv us; exact: condition_kappa_F_lt.
rewrite /condition_kappa_u.
move: hlip F0 Fs hlt; set F := condition_kappa_F C kappa.
set K := (1 + `|(kappa - 3%:R) / (kappa - 1)| * (C - 1) ^+ 2) / C + C.
move=> hlip F0 Fs hlt.
have K0 : 0 < K.
  rewrite /K; apply: addr_gt0; last exact: (lt_trans ltr01 C1).
  apply: divr_gt0; last exact: (lt_trans ltr01 C1).
  apply: lt_le_trans (ltr01) _.
  by rewrite lerDl mulr_ge0 // sqr_ge0.
have hmono u v : u <= v -> v <= sq2 -> F u <= F v.
  move=> uv vs; have [->|uv'] := eqVneq u v; first exact: lexx.
  have uv'' : u < v by rewrite lt_neqAle uv' uv.
  exact/ltW/hlt/(lt_le_trans uv'').
have s0 := kappa_sq2_gt0.
pose T := [set u : R | 0 <= u <= sq2 /\ F u <= 0].
have -> : [set u : R | 0 <= u <= sq2 /\ F u <= 0] = T by [].
have T0 : T 0 by split; [rewrite lexx ltW | exact: ltW].
have Tub : ubound T sq2 by move=> u [/andP[_ ->]].
have hasT : has_sup T by split; [exists 0 | exists sq2].
have lo u : 0 <= u -> u < sup T -> F u <= 0.
  move=> u0 us.
  have st : 0 < sup T - u by rewrite subr_gt0.
  have [e [/andP[e0 es] he] te] := sup_adherent st hasT.
  have ue : u <= e by move: te; rewrite opprB addrC subrK => /ltW.
  exact: le_trans (hmono _ _ ue es) he.
(* sup T > 0, since F is negative near 0 *)
pose t1 := Num.min (- F 0 / (2%:R * K)) sq2.
have t10 : 0 < t1.
  by rewrite lt_min s0 andbT divr_gt0 ?oppr_gt0 ?mulr_gt0.
have Tt1 : T t1.
  split; first by rewrite (ltW t10) ge_min lexx orbT.
  have b : K * t1 <= - F 0 / 2%:R.
    have : t1 <= - F 0 / (2%:R * K) by rewrite ge_min lexx.
    rewrite -(ler_pM2l K0) => hb; apply: le_trans hb _.
    have e : K * (- F 0 / (2%:R * K)) = - F 0 / 2%:R.
      by have hK := lt0r_neq0 K0; field.
    by rewrite e.
  have := hlip 0 t1 (ltW t10); rewrite subr0.
  by move: b F0; move: (F t1) (F 0) (K * t1) => a b c; lra.
have uT0 : 0 < sup T := lt_le_trans t10 (sup_upper_bound hasT Tt1).
(* sup T < sqrt 2, since F is positive near sqrt 2 *)
pose dl := F sq2 / K.
have dl0 : 0 < dl by rewrite divr_gt0.
have Kdl : K * dl = F sq2 by rewrite /dl mulrC divfK // gt_eqF.
have ub : ubound T (sq2 - dl).
  move=> t [/andP[t0 ts] ht]; rewrite leNgt; apply/negP => tl.
  have hl := hlip t sq2 ts.
  have : K * (sq2 - t) < K * dl by rewrite ltr_pM2l //; lra.
  rewrite Kdl; move: hl ht; move: (F sq2) (F t) (K * (sq2 - t)) => a b c.
  lra.
have uTs : sup T < sq2 by have := ge_sup (ex_intro _ 0 T0) ub; lra.
(* F (sup T) = 0 *)
have Fle : F (sup T) <= 0.
  rewrite leNgt; apply/negP => Fp.
  pose h := Num.min (F (sup T) / (2%:R * K)) (sup T / 2%:R).
  have h0 : 0 < h by rewrite lt_min !divr_gt0 ?mulr_gt0.
  have hT : h <= sup T / 2%:R by rewrite ge_min lexx orbT.
  have t0 : 0 <= sup T - h by rewrite subr_ge0; apply: le_trans hT _; lra.
  have tl : sup T - h < sup T by rewrite ltrBlDr ltrDl.
  have := lo _ t0 tl.
  have hl := hlip (sup T - h) (sup T) (ltW tl).
  have b : K * h <= F (sup T) / 2%:R.
    have : h <= F (sup T) / (2%:R * K) by rewrite ge_min lexx.
    rewrite -(ler_pM2l K0) => hb; apply: le_trans hb _.
    have e : K * (F (sup T) / (2%:R * K)) = F (sup T) / 2%:R.
      by have hK := lt0r_neq0 K0; field.
    by rewrite e.
  have e : sup T - (sup T - h) = h by ring.
  rewrite e in hl.
  by move: hl b Fp; move: (F (sup T)) (F (sup T - h)) (K * h) => a b c; lra.
have Fge : 0 <= F (sup T).
  rewrite leNgt; apply/negP => Fn.
  pose t2 := Num.min (sup T + - F (sup T) / (2%:R * K)) sq2.
  have tt2 : sup T < t2.
    by rewrite lt_min uTs andbT ltrDl divr_gt0 ?oppr_gt0 ?mulr_gt0.
  have Tt2 : T t2.
    split.
      apply/andP; split; last by rewrite ge_min lexx orbT.
      exact: le_trans (ltW uT0) (ltW tt2).
    have b : K * (t2 - sup T) <= - F (sup T) / 2%:R.
      have : t2 - sup T <= - F (sup T) / (2%:R * K).
        by rewrite lerBlDl ge_min lexx.
      rewrite -(ler_pM2l K0) => hb; apply: le_trans hb _.
      have hK := lt0r_neq0 K0.
      have e : K * (- F (sup T) / (2%:R * K)) = - F (sup T) / 2%:R by field.
      by rewrite e.
    have hl := hlip (sup T) t2 (ltW tt2).
    move: hl b Fn; move: (F t2) (F (sup T)) (K * (t2 - sup T)) => a b c.
    lra.
  by have := sup_upper_bound hasT Tt2; move: tt2; lra.
have FuT : F (sup T) = 0 by apply/eqP; rewrite eq_le Fle Fge.
split => //.
move=> u /andP[u0 us] Fu.
have [uv|vu|//] := ltgtP u (sup T).
  by have := hlt _ _ uv (lt_trans uv uTs); rewrite Fu FuT ltxx.
by have := hlt _ _ vu uTs; rewrite Fu FuT ltxx.
Qed.

(* The cutoff: -sqrt 2 < ell < u. *)
Lemma condition_kappa_ell_spec (C kappa : R) : 1 < C -> 1 < kappa ->
  - sq2 < condition_kappa_ell C kappa < condition_kappa_u C kappa.
Proof.
move=> C1 k1.
have [u0 us Fu _] := condition_kappa_u_spec C kappa C1 k1.
have C0 : 0 < C := lt_trans ltr01 C1.
have r1 := kappa_r_lt1 kappa k1.
have mu0 := universality_m_gt0 _ us.
have hL := condition_kappa_LE C kappa (condition_kappa_u C kappa) C0.
move: Fu; rewrite /condition_kappa_F -/(condition_kappa_ell C kappa).
move: r1 hL mu0 u0 us.
set r := (kappa - 3%:R) / (kappa - 1).
set u := condition_kappa_u C kappa; set l := condition_kappa_ell C kappa.
move=> r1 hL mu0 u0 us Fu.
have Cmu : 0 < C * um u by rewrite mulr_gt0.
apply/andP; split.
  (* m(-ell) = C m(u) > 0, so -ell < sqrt 2 *)
  rewrite ltrNl ltNge; apply/negP => sl.
  have := universality_m_out _ sl.
  by move: Fu Cmu; move: (um (- l)%R) (C * um u) => a b; lra.
(* if ell >= u: C m(u) = m(ell) + ell <= m(u) + ell, so
   C ell - u >= (C - 1) ell >= (C - 1)^2 m(u) > r (C - 1)^2 m(u) *)
rewrite ltNge; apply/negP => ul.
have hs := kappa_m_sym l.
have /andP[h _] := kappa_m_lip _ _ ul.
have h1 : (C - 1) * um u <= l.
  move: Fu hs h; rewrite mulrBl mul1r.
  by move: (um (- l)%R) (um l) (um u) (C * um u) => a b c f; lra.
have C10 : 0 < C - 1 by rewrite subr_gt0.
have h2 : (C - 1) ^+ 2 * um u <= (C - 1) * l.
  by rewrite expr2 -mulrA ler_wpM2l // ltW.
have h3 : (C - 1) * l <= C * l - u.
  by rewrite mulrBl mul1r lerB.
have h4 : r * (C - 1) ^+ 2 * um u < (C - 1) ^+ 2 * um u.
  rewrite -mulrA -[X in _ < X]mul1r ltr_pM2r //.
  by rewrite mulr_gt0 // exprn_gt0.
have e : C * l - u = r * (C - 1) ^+ 2 * um u by rewrite hL; ring.
move: h2 h3 h4 e.
move: ((C - 1) ^+ 2 * um u) ((C - 1) * l) (C * l - u) (r * (C - 1) ^+ 2 * um u).
by move=> a b c f; lra.
Qed.

(* Conjunct (a) of the curve statement. *)
Theorem condition_kappa_root_holds (kappa : R) : 1 < kappa ->
  condition_kappa_root kappa.
Proof.
move=> k1 C C1.
have [u0 us Fu uniq] := condition_kappa_u_spec C kappa C1 k1.
have ell := condition_kappa_ell_spec C kappa C1 k1.
by split => //; rewrite u0 us.
Qed.
