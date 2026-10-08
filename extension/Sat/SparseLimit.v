(* The sparse estimates of Proposition 3.1 (first display) and the sparse
   lower bound of Proposition 3.3 with probability tending to one, for
   supports of size at most C0 d ln d, when n / d^2 tends to alpha > 0
   (Koehler and Sohn, arXiv 2608.27372, lines 2133-2418 of arxiv_v1.tex),
   at Stdlib's R. Items S3 and S4 of stage 3 of phase 5 (lane C), after
   Sat/AprioriSparse (the bounds for each d) and Sat/SparseLower (the
   deterministic Proposition 3.3).

   Proved here.
   - ln_pow_le_sqrt: c (ln d)^p <= sqrt d for every large d; ev_nat and
     its combinators (ev_and, ev_gt, ev_ln_ge1) for "every large d", and
     density_ev: q d^2 <= n <= (alpha + 1) d^2 for every large d,
     q = min (alpha / 2, 1).
   - gram_dev_alg, gram_dev_rate: with beta = 1/d and th = ln d / sqrt d,
     the defect gram_dev of the Gram matrices Q_I (Sat/AprioriSparse)
     satisfies 0 <= gram_dev <= Cg (ln d)^4 / sqrt d and
     gram_dev sqrt m <= Cg sqrt C0 (ln d)^2, when m <= C0 d ln d,
     1 + ln (n / m) <= 4 ln d and (ln d)^2 <= sqrt d; Cg = rate_Cg K C0 =
     256 C_T^2 + 96 C_T + 48 with C_T = 2100 * 252 * 5 K^2 sqrt C0.
   - points_rate: the constant L of the bound on |X_I| (sparse_points_bound
     with s = d) satisfies L^2 <= rate_CL K C0 d (ln d)^2,
     rate_CL K C0 = 1024 K^2 (10 C0 + 7).
   - sparse_lower_rate: on the events of the two sparse bounds, Proposition
     3.3 (sparse_lower of Sat/SparseLower) gives
     |h|_1 sqrt d <= rate_CS K C0 (ln d)^4 nuclear (L_X^* h) for every h
     with at most m nonzero coordinates, rate_CS K C0 =
     rate_CL K C0 (1 + 2 Cg sqrt C0) + 2 C0.
   - sparse_lower_limit_features (Proposition 3.3 with probability
     tending to one, through the first display of Proposition 3.1 at the
     rates delta <= Cg (ln d)^4 / sqrt d and
     L^2 <= rate_CL K C0 d (ln d)^2): if n / d^2 tends to alpha > 0, then
     for every eps > 0 there is D such that for every d >= D and every flat
     family of component laws with the hypotheses on the features of
     sparse_gram_bound_flat, outside a measurable event of probability at
     most eps, every h with at most C0 d ln d nonzero coordinates
     satisfies |h|_1 sqrt d <= rate_CS K C0 (ln d)^4 nuclear (L_X^* h).
     The event is that of sparse_gram_bound_flat and
     sparse_points_bound_flat with m = floor (C0 d ln d); its probability
     is at most 12 / sqrt m + 2 (alpha + 1) / d^2 + 2 exp (- d). D does not
     depend on the laws. sparse_lower_limit is the case of
     universality_sample_law with coordinate laws. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets cardinality reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From mathcomp Require Import normedtype sequences exp.
From GaussianAnalysis.matrix Require Import euclidean opnorm nuclear.
From GaussianAnalysis.probability Require Import lindeberg subgaussian.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Features Require Import Definitions.
From EllipsoidUniversality.Mixture Require Import Flat.
From EllipsoidUniversality.Sat Require Import Apriori AprioriSparse.
From EllipsoidUniversality.Sat Require Import SparseLower.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).
Local Notation lnR x := (ln (x : R)).

(* 1. Rates. *)

(* c (ln d)^p <= sqrt d for every large d. *)
Lemma ln_pow_le_sqrt (c : R) (p : nat) : 0 < c ->
  exists D : nat, forall d : nat, (D <= d)%N ->
  c * lnR d%:R ^+ p <= Num.sqrt d%:R.
Proof.
move=> c0.
set U := c * 2 ^+ p.+1 * p.+1`!%:R.
have U0 : 0 < U by rewrite /U !mulr_gt0 // ?exprn_gt0 // ltr0n fact_gt0.
exists (archimedean.Num.truncn (expR U)).+1 => d hd.
have dU : expR U < d%:R.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
have d0 : 0 < d%:R :> R by apply: lt_trans dU; exact: expR_gt0.
set u := ln d%:R.
have uU : U < u.
  by rewrite -(expRK U) /u ltr_ln // posrE expR_gt0.
have u0 : 0 <= u by apply: le_trans (ltW uU); exact: ltW.
(* sqrt d = exp (u / 2) >= (u / 2)^(p + 1) / (p + 1)! >= c u^p *)
have ed : d%:R = expR u by rewrite /u lnK // posrE.
have sd : Num.sqrt d%:R = expR (u / 2).
  by rewrite ed {1}(splitr u) expRD -expr2 sqrtr_sqr ger0_norm.
rewrite sd.
have u2 : 0 <= u / 2 by rewrite divr_ge0.
apply: le_trans (_ : (u / 2) ^+ p.+1 / p.+1`!%:R <= _); last first.
  by apply: le_trans (expR_ge1Dxn p u2); rewrite lerDr ler01.
have P0 : 0 < 2 ^+ p.+1 * p.+1`!%:R :> R.
  by rewrite mulr_gt0 ?exprn_gt0 // ltr0n fact_gt0.
have e1 : (u / 2) ^+ p.+1 / p.+1`!%:R =
    u ^+ p * (u / (2 ^+ p.+1 * p.+1`!%:R)).
  have Pn := gt_eqF P0.
  have fn : p.+1`!%:R != 0 :> R by rewrite pnatr_eq0 -lt0n fact_gt0.
  rewrite expr_div_n exprS.
  by field.
have e2 : c = U / (2 ^+ p.+1 * p.+1`!%:R).
  by have Pn := gt_eqF P0; rewrite /U -mulrA; field.
rewrite e1 mulrC; apply: ler_wpM2l; first by rewrite exprn_ge0.
by rewrite e2 ler_pM2r ?invr_gt0 //; exact: ltW.
Qed.

Arguments ln_pow_le_sqrt c%_ring_scope p%_nat_scope _.


(* The constants of the rates. *)
Definition rate_CT (K C0 : R) : R :=
  (2100 * 252 * 5 * K ^+ 2 * Num.sqrt C0)%R.
Definition rate_Cg (K C0 : R) : R :=
  (256 * rate_CT K C0 ^+ 2 + 96 * rate_CT K C0 + 48)%R.
Definition rate_CL (K C0 : R) : R := (1024 * K ^+ 2 * (10 * C0 + 7))%R.
Definition rate_CS (K C0 : R) : R :=
  (rate_CL K C0 * (1 + 2 * (rate_Cg K C0 * Num.sqrt C0)) + 2 * C0)%R.

Lemma rate_CT_ge0 K C0 : 0 <= rate_CT K C0.
Proof.
exact: (mulr_ge0 (mulr_ge0 (mulr_ge0 (mulr_ge0 (ler0n _ 2100)
  (ler0n _ 252)) (ler0n _ 5)) (sqr_ge0 K)) (sqrtr_ge0 C0)).
Qed.

Lemma rate_Cg_ge0 K C0 : 0 <= rate_Cg K C0.
Proof.
have h := rate_CT_ge0 K C0.
rewrite /rate_Cg; apply: addr_ge0; last exact: ler0n.
apply: addr_ge0; first exact: (mulr_ge0 (ler0n _ 256) (sqr_ge0 _)).
exact: (mulr_ge0 (ler0n _ 96) h).
Qed.

Lemma rate_CL_ge0 K C0 : 0 <= C0 -> 0 <= rate_CL K C0.
Proof.
move=> C00; rewrite /rate_CL; apply: mulr_ge0.
  exact: (mulr_ge0 (ler0n _ 1024) (sqr_ge0 K)).
by apply: addr_ge0; [exact: (mulr_ge0 (ler0n _ 10) C00) | exact: ler0n].
Qed.

Lemma rate_CS_gt0 K C0 : 0 < C0 -> 0 < rate_CS K C0.
Proof.
move=> C00; rewrite /rate_CS.
apply: (@lt_le_trans _ _ (0 + 2 * C0)); first by rewrite add0r mulr_gt0.
apply: lerD => //; apply: mulr_ge0; first exact: rate_CL_ge0 (ltW C00).
apply: addr_ge0 => //; apply: mulr_ge0 => //.
exact: (mulr_ge0 (rate_Cg_ge0 K C0) (sqrtr_ge0 C0)).
Qed.

(* The arithmetic of the defect: with D = sd^2, th sd = l = s^2,
   l^2 <= sd, 0 <= T <= C_T l s, 0 <= B <= 5 D and 0 <= rm <=
   sqrt C0 sd s, the defect is at most Cg l^4 / sd, and times rm at most
   Cg sqrt C0 l^2. *)
Lemma gram_dev_alg (C0 C_T l s sd D th T B rm : R) :
  0 < C0 -> 0 <= C_T -> 1 <= s -> s ^+ 2 = l -> l ^+ 2 <= sd ->
  sd ^+ 2 = D -> th * sd = l -> 0 <= T -> T <= C_T * l * s ->
  0 <= B -> B <= 5 * D -> 0 <= rm -> rm <= Num.sqrt C0 * sd * s ->
  let Cg := 256 * C_T ^+ 2 + 96 * C_T + 48 in
  let dev := (256 * T ^+ 2 + 32 * T * Num.sqrt B + 8 / D * B) / D +
    th * (2 + th) + (3 + 2 * th) / D in
  [/\ 0 <= dev, dev <= Cg * (l ^+ 4 / sd) &
    dev * rm <= Cg * Num.sqrt C0 * l ^+ 2].
Proof.
move=> C00 CT0 s1 ss l2 sdD thl T0 TC B0 B5 rm0 rmC Cg dev.
have s0 : 0 <= s by apply: le_trans s1.
have l1 : 1 <= l by rewrite -ss expr2 -[1]mul1r ler_pM.
have l0 : 0 <= l by apply: le_trans l1.
have sl : s <= l by rewrite -ss expr2 ler_peMl.
have ll2 : l <= l ^+ 2 by rewrite expr2 ler_peMl.
have sd1 : 1 <= sd by apply: le_trans l2; apply: le_trans ll2.
have sd0 : 0 < sd by apply: lt_le_trans sd1.
have D0 : 0 < D by rewrite -sdD exprn_gt0.
have th0 : 0 <= th.
  have := thl; move/(congr1 (fun x => x / sd)); rewrite mulfK ?gt_eqF //.
  by move=> ->; rewrite divr_ge0 // ltW.
have sdn : sd != 0 by rewrite gt_eqF.
have thE : th = l / sd by rewrite -thl mulfK.
have lsd : l <= sd by apply: le_trans l2.
have th1 : th <= 1 by rewrite thE ler_pdivrMr // mul1r.
have Dsd : sd <= D by rewrite -sdD expr2 ler_peMl // ltW.
have l4 : 1 <= l ^+ 4 by rewrite exprn_ege1.
have g0 : 0 <= l ^+ 4 / sd by rewrite divr_ge0 ?exprn_ge0 // ltW.
have dD x : 0 <= x -> x / D <= x / sd.
  by move=> x0; rewrite ler_wpM2l // lef_pV2 // posrE.
have sqB : Num.sqrt B <= 3 * sd.
  have h3 : 0 <= 3 * sd by rewrite mulr_ge0 // ltW.
  rewrite -(ler_sqr (sqrtr_ge0 B) h3) sqr_sqrtr // exprMn sdD.
  apply: le_trans B5 _; apply: ler_wpM2r; first exact: ltW.
  by rewrite -natrX ler_nat.
have TT : T ^+ 2 <= C_T ^+ 2 * l ^+ 3.
  have e : C_T ^+ 2 * l ^+ 3 = (C_T * l * s) ^+ 2.
    by rewrite !exprMn ss; ring.
  rewrite e; have h0 : 0 <= C_T * l * s by rewrite !mulr_ge0.
  by rewrite (ler_sqr T0 h0).
(* the five terms of the defect *)
have Di0 : 0 <= D^-1 by rewrite invr_ge0 ltW.
have e1 : T ^+ 2 / D <= C_T ^+ 2 * (l ^+ 3 / D).
  by rewrite mulrA; apply: ler_wpM2r.
have e2 : T * Num.sqrt B / D <= 3 * C_T * (l * s / sd).
  have h : T * Num.sqrt B <= C_T * l * s * (3 * sd).
    by apply: ler_pM => //; exact: sqrtr_ge0.
  apply: le_trans (ler_wpM2r Di0 h) _.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by rewrite -sdD; field.
have e3 : 8 / D * B / D <= 40 / D.
  apply: ler_wpM2r => //.
  rewrite -mulrA [D^-1 * B]mulrC.
  have -> : (40 = 8 * 5 :> R)%R by rewrite -natrM.
  apply: ler_wpM2l => //.
  by rewrite ler_pdivrMr.
have e4 : th * (2 + th) <= 3 * th.
  have h : th * th <= th * 1 := ler_wpM2l th0 th1.
  rewrite mulr1 in h; rewrite mulrDr.
  move: h; move: (th * th) => q h; lra.
have e5 : (3 + 2 * th) / D <= 5 / D.
  apply: ler_wpM2r => //.
  have -> : (5 = 3 + 2 :> R)%R by rewrite -natrD.
  by rewrite lerD2l -[X in _ <= X]mulr1 ler_wpM2l.
have hdev : dev <= 256 * (C_T ^+ 2 * (l ^+ 3 / D)) +
    96 * (C_T * (l * s / sd)) + 45 / D + 3 * th.
  by rewrite /dev; lra.
(* each term against l^4 / sd *)
have l34 : l ^+ 3 <= l ^+ 4.
  by rewrite [X in _ <= X]exprSr ler_peMr // exprn_ge0.
have lsl2 : l * s <= l ^+ 2 by rewrite expr2 ler_wpM2l.
have l24 : l ^+ 2 <= l ^+ 4.
  by rewrite (_ : 4 = 2 + 2)%N // exprD ler_peMr ?exprn_ge0 // exprn_ege1.
have isd0 : 0 <= sd^-1 by rewrite invr_ge0 ltW.
have f1 : l ^+ 3 / D <= l ^+ 4 / sd.
  apply: le_trans (dD _ (exprn_ge0 3 l0)) _.
  exact: ler_wpM2r.
have f2 : l * s / sd <= l ^+ 4 / sd.
  by apply: ler_wpM2r => //; exact: le_trans l24.
have f3 : D^-1 <= l ^+ 4 / sd.
  apply: le_trans (_ : D^-1 <= sd^-1) _.
    by rewrite lef_pV2 // posrE.
  by rewrite ler_peMl.
have f4 : th <= l ^+ 4 / sd.
  by rewrite thE; apply: ler_wpM2r => //; apply: le_trans l24.
(* each term times rm against sqrt C0 l^2 *)
have sC0 : 0 <= Num.sqrt C0 := sqrtr_ge0 C0.
have lssd : l * s / sd <= 1 by rewrite ler_pdivrMr // mul1r (le_trans lsl2).
have r1 : l ^+ 3 / D * rm <= Num.sqrt C0 * l ^+ 2.
  have h0 : 0 <= l ^+ 3 / D by rewrite divr_ge0 ?exprn_ge0 // ltW.
  apply: le_trans (ler_wpM2l h0 rmC) _.
  have -> : l ^+ 3 / D * (Num.sqrt C0 * sd * s) =
      Num.sqrt C0 * l ^+ 2 * (l * s / sd).
    by rewrite -sdD; field.
  by rewrite -[X in _ <= X]mulr1 ler_wpM2l // mulr_ge0 // exprn_ge0.
have r2 : l * s / sd * rm <= Num.sqrt C0 * l ^+ 2.
  have h0 : 0 <= l * s / sd by rewrite !mulr_ge0.
  apply: le_trans (ler_wpM2l h0 rmC) _.
  have -> : l * s / sd * (Num.sqrt C0 * sd * s) =
      Num.sqrt C0 * (l * s ^+ 2).
    by field.
  by rewrite ss expr2.
have r3 : D^-1 * rm <= Num.sqrt C0 * l ^+ 2.
  apply: le_trans (ler_wpM2l Di0 rmC) _.
  have -> : D^-1 * (Num.sqrt C0 * sd * s) = Num.sqrt C0 * (s / sd).
    by rewrite -sdD; field.
  apply: ler_wpM2l => //.
  apply: le_trans (_ : s <= l ^+ 2); last exact: le_trans ll2.
  by rewrite ler_pdivrMr // ler_peMr.
have r4 : th * rm <= Num.sqrt C0 * l ^+ 2.
  apply: le_trans (ler_wpM2l th0 rmC) _.
  have -> : th * (Num.sqrt C0 * sd * s) = Num.sqrt C0 * (l * s).
    by rewrite -thl; ring.
  by apply: ler_wpM2l.
have CT2 : 0 <= C_T ^+ 2 := sqr_ge0 C_T.
have g1 : C_T ^+ 2 * (l ^+ 3 / D) <= C_T ^+ 2 * (l ^+ 4 / sd).
  by apply: ler_wpM2l.
have g2 : C_T * (l * s / sd) <= C_T * (l ^+ 4 / sd).
  by apply: ler_wpM2l.
have h1 : C_T ^+ 2 * (l ^+ 3 / D * rm) <=
    C_T ^+ 2 * (Num.sqrt C0 * l ^+ 2).
  by apply: ler_wpM2l.
have h2 : C_T * (l * s / sd * rm) <= C_T * (Num.sqrt C0 * l ^+ 2).
  by apply: ler_wpM2l.
split.
- rewrite /dev; apply: addr_ge0; first apply: addr_ge0.
  + apply: divr_ge0; last exact: ltW.
    apply: addr_ge0; first apply: addr_ge0.
    * exact: (mulr_ge0 (ler0n _ 256) (sqr_ge0 T)).
    * exact: (mulr_ge0 (mulr_ge0 (ler0n _ 32) T0) (sqrtr_ge0 B)).
    * exact: (mulr_ge0 (divr_ge0 (ler0n _ 8) (ltW D0)) B0).
  + exact: (mulr_ge0 th0 (addr_ge0 (ler0n _ 2) th0)).
  + exact: (divr_ge0 (addr_ge0 (ler0n _ 3) (mulr_ge0 (ler0n _ 2) th0))
      (ltW D0)).
- by apply: le_trans hdev _; rewrite /Cg; lra.
- by apply: le_trans (ler_wpM2r rm0 hdev) _; rewrite /Cg; lra.
Qed.

(* The defect of the Gram matrices with beta = 1/d and th = ln d / sqrt d:
   gram_dev <= Cg (ln d)^4 / sqrt d and gram_dev sqrt m <= Cg sqrt C0
   (ln d)^2. *)
Lemma gram_dev_rate (K C0 th : R) (n d m : nat) :
  0 < K -> 0 < C0 -> (5 <= d)%N -> (0 < m)%N -> (m <= n)%N ->
  1 <= lnR d%:R -> lnR d%:R ^+ 2 <= Num.sqrt d%:R ->
  m%:R <= C0 * d%:R * lnR d%:R -> 1 + lnR (n%:R / m%:R) <= 4 * lnR d%:R ->
  th * Num.sqrt d%:R = lnR d%:R ->
  let delta := gram_dev K n d m d%:R^-1 th in
  [/\ 0 <= delta, delta <= rate_Cg K C0 * (lnR d%:R ^+ 4 / Num.sqrt d%:R) &
    delta * Num.sqrt m%:R <= rate_Cg K C0 * Num.sqrt C0 * lnR d%:R ^+ 2].
Proof.
move=> K0 C00 d5 m0 mn l1 l2 mC lnm thl delta.
set C_T := rate_CT K C0.
set Cg := rate_Cg K C0.
have d0 : 0 < d%:R :> R by rewrite ltr0n (leq_trans _ d5).
have l0 : 0 <= lnR d%:R by apply: le_trans l1.
have s1 : 1 <= Num.sqrt (lnR d%:R) by rewrite -{1}sqrtr1 ler_sqrt.
have ss : Num.sqrt (lnR d%:R) ^+ 2 = lnR d%:R by rewrite sqr_sqrtr.
have sdD : Num.sqrt (d%:R : R) ^+ 2 = d%:R by rewrite sqr_sqrtr // ltW.
have rmC : Num.sqrt (m%:R : R) <=
    Num.sqrt C0 * Num.sqrt (d%:R : R) * Num.sqrt (lnR d%:R).
  have h0 : 0 <= C0 * d%:R * lnR d%:R by rewrite !mulr_ge0 // ltW.
  have h := mC; rewrite -(ler_sqrt _ h0) in h.
  have c0 : 0 <= C0 by exact: ltW.
  have cd0 : 0 <= C0 * d%:R by rewrite mulr_ge0 // ltW.
  by rewrite (sqrtrM _ cd0) (sqrtrM _ c0) in h.
(* the scale T of the restricted isometry theorem: T <= C_T l sqrt l *)
have hT : gram_scale K n d m d%:R^-1 <=
    C_T * lnR d%:R * Num.sqrt (lnR d%:R).
  rewrite /gram_scale /rip_T.
  rewrite lnV ?posrE // opprK.
  have nm1 : 1 <= (n%:R / m%:R : R).
    by rewrite ler_pdivlMr ?ltr0n // mul1r ler_nat.
  have X0 : 0 <= 1 + lnR (n%:R / m%:R) + lnR d%:R.
    by rewrite !addr_ge0 // ln_ge0.
  have X5 : 1 + lnR (n%:R / m%:R) + lnR d%:R <= 5 * lnR d%:R.
    move: lnm l0; move: (lnR (n%:R / m%:R)) (lnR d%:R) => a b h1 h2; lra.
  have sd0 : 0 < Num.sqrt (d%:R : R) by rewrite sqrtr_gt0.
  have P0 : 0 <= 2100 * 1 * (252 * K ^+ 2 / Num.sqrt (d%:R : R)).
    apply: mulr_ge0; first exact: (mulr_ge0 (ler0n _ 2100) ler01).
    apply: divr_ge0; last exact: ltW.
    exact: (mulr_ge0 (ler0n _ 252) (sqr_ge0 K)).
  apply: le_trans (_ : 2100 * 1 * (252 * K ^+ 2 / Num.sqrt (d%:R : R)) *
      (Num.sqrt C0 * Num.sqrt (d%:R : R) * Num.sqrt (lnR d%:R)) *
      (5 * lnR d%:R) <= _).
    exact: (ler_pM (mulr_ge0 P0 (sqrtr_ge0 _)) X0 (ler_wpM2l P0 rmC) X5).
  have sdn : Num.sqrt (d%:R : R) != 0 by rewrite gt_eqF.
  rewrite /C_T /rate_CT le_eqVlt; apply/orP; left; apply/eqP; field.
have dp : (d%:R : R) \in Num.pos by rewrite posrE.
have nm1 : 1 <= (n%:R / m%:R : R).
  by rewrite ler_pdivlMr ?ltr0n // mul1r ler_nat.
have X0 : 0 <= 1 + lnR (n%:R / m%:R) + lnR d%:R.
  by rewrite !addr_ge0 // ln_ge0.
have sd0 : 0 < Num.sqrt (d%:R : R) by rewrite sqrtr_gt0.
have P0 : 0 <= 2100 * 1 * (252 * K ^+ 2 / Num.sqrt (d%:R : R)).
  apply: mulr_ge0; first exact: (mulr_ge0 (ler0n _ 2100) ler01).
  apply: divr_ge0; last exact: ltW.
  exact: (mulr_ge0 (ler0n _ 252) (sqr_ge0 K)).
have hT0 : 0 <= gram_scale K n d m d%:R^-1.
  rewrite /gram_scale /rip_T (lnV dp) opprK.
  exact: (mulr_ge0 (mulr_ge0 P0 (sqrtr_ge0 _)) X0).
(* th = ln d / sqrt d is in [0, 1], and B <= 5 d *)
have th0 : 0 <= th.
  have := thl; move/(congr1 (fun x => x / Num.sqrt (d%:R : R))).
  by rewrite mulfK ?gt_eqF // => ->; rewrite divr_ge0 // ltW.
have th1 : th <= 1.
  have e : th = lnR d%:R / Num.sqrt (d%:R : R) by rewrite -thl mulfK ?gt_eqF.
  rewrite e ler_pdivrMr // mul1r; apply: le_trans l2.
  by rewrite expr2 ler_peMl.
have B0 : 0 <= gram_feature_bound d th.
  rewrite /gram_feature_bound; apply: addr_ge0.
    apply: mulr_ge0; first exact: ler0n.
    by rewrite addr_ge0 // mulr_ge0 // addr_ge0.
  by rewrite addr_ge0 // mulr_ge0.
have B5 : gram_feature_bound d th <= 5 * d%:R.
  rewrite /gram_feature_bound.
  have h1 : 1 + th * (2 + th) <= 4.
    have h : th * th <= th * 1 := ler_wpM2l th0 th1.
    rewrite mulr1 in h; rewrite mulrDr.
    move: h th1; move: (th * th) => q h t1; lra.
  have h3 : d%:R * (1 + th * (2 + th)) <= d%:R * 4.
    by apply: ler_wpM2l => //; exact: ler0n.
  have d5' : (5%:R <= d%:R :> R) by rewrite ler_nat.
  move: h3 d5' th1.
  move: (d%:R * (1 + th * (2 + th))) (d%:R : R) => p D h3 h4 t1.
  lra.
have CT0 : 0 <= C_T := rate_CT_ge0 K C0.
have rm0 : 0 <= Num.sqrt (m%:R : R) := sqrtr_ge0 _.
exact: (gram_dev_alg C0 C_T (lnR d%:R) (Num.sqrt (lnR d%:R))
  (Num.sqrt (d%:R : R)) d%:R th (gram_scale K n d m d%:R^-1)
  (gram_feature_bound d th) (Num.sqrt (m%:R : R)) C00 CT0 s1 ss l2 sdD thl
  hT0 hT B0 B5 rm0 rmC).
Qed.

(* 2. Eventually in d. *)

Definition ev_nat (P : nat -> Prop) : Prop :=
  exists D : nat, forall d : nat, (D <= d)%N -> P d.

Lemma ev_and (P Q : nat -> Prop) : ev_nat P -> ev_nat Q ->
  ev_nat (fun d => P d /\ Q d).
Proof.
move=> [D1 h1] [D2 h2]; exists (maxn D1 D2) => d.
by rewrite geq_max => /andP[d1 d2]; split; [exact: h1 | exact: h2].
Qed.

Arguments ev_and {P Q}.

Lemma ev_mono (P Q : nat -> Prop) : (forall d, P d -> Q d) ->
  ev_nat P -> ev_nat Q.
Proof. by move=> h [D hD]; exists D => d dD; apply: h; exact: hD. Qed.

Arguments ev_mono {P Q}.

Lemma ev_gt (x : R) : ev_nat (fun d => x < d%:R).
Proof.
exists (archimedean.Num.truncn x).+1 => d hd.
apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
by rewrite ler_nat.
Qed.

Arguments ev_gt x%_ring_scope.

Lemma ev_ge (k : nat) : ev_nat (fun d => (k <= d)%N).
Proof. by exists k. Qed.

Lemma ev_ln_ge1 : ev_nat (fun d => 1 <= lnR d%:R).
Proof.
apply: ev_mono (ev_gt (expR 1)) => d hd.
have d0 : 0 < d%:R :> R by apply: lt_trans hd; exact: expR_gt0.
rewrite -[X in X <= _](expRK 1) ler_ln ?posrE ?expR_gt0 //.
exact: ltW.
Qed.

(* q d^2 <= n d <= (alpha + 1) d^2 for every large d, q = min (alpha/2, 1). *)
Lemma density_ev (alpha : R) (n : nat -> nat) : 0 < alpha ->
  universality_density_tends_to n alpha ->
  ev_nat (fun d => Num.min (alpha / 2) 1 * d%:R ^+ 2 <= (n d)%:R /\
                   (n d)%:R <= (alpha + 1) * d%:R ^+ 2).
Proof.
move=> a0 hn.
set q := Num.min (alpha / 2) 1.
have q0 : 0 < q by rewrite lt_min divr_gt0 // ltr01.
have [D1 h1] := hn _ q0.
exists (maxn D1 1) => d; rewrite geq_max => /andP[d1 dpos].
have dR : 0 < d%:R :> R by rewrite ltr0n.
have hd := h1 d d1; rewrite /paper_main_density RdivE in hd.
have d2R : 0 < d%:R ^+ 2 :> R by rewrite exprn_gt0.
have qa : q <= alpha / 2 by rewrite /q ge_min lexx.
move: hd; rewrite ltr_norml => /andP[hlo hhi].
have rlo : q <= (n d)%:R / d%:R ^+ 2 by lra.
have rhi : (n d)%:R / d%:R ^+ 2 <= alpha + 1.
  have q1 : q <= 1 by rewrite /q ge_min lexx orbT.
  by lra.
by split; [rewrite -ler_pdivlMr | rewrite -ler_pdivrMr].
Qed.

Arguments density_ev alpha%_ring_scope n _ _.

(* 3. Proposition 3.3 at the rates. *)

(* The constant of the bound on |X_I| with s = d. *)
Lemma points_rate (K C0 : R) (n d m : nat) :
  0 < C0 -> (0 < m)%N -> (m <= n)%N -> 1 <= lnR d%:R ->
  m%:R <= C0 * d%:R * lnR d%:R -> 1 + lnR (n%:R / m%:R) <= 4 * lnR d%:R ->
  (32 * K * Num.sqrt (m%:R * (1 + lnR (n%:R / m%:R)) + 6 * (m + d)%:R +
    d%:R)) ^+ 2 <= rate_CL K C0 * d%:R * lnR d%:R ^+ 2.
Proof.
move=> C00 m0 mn l1 mC lnm.
have l0 : 0 <= lnR d%:R by apply: le_trans l1.
have nm1 : 1 <= (n%:R / m%:R : R).
  by rewrite ler_pdivlMr ?ltr0n // mul1r ler_nat.
have b0 : 0 <= lnR (n%:R / m%:R) := ln_ge0 nm1.
have X0 : 0 <= m%:R * (1 + lnR (n%:R / m%:R)) + 6 * (m + d)%:R + d%:R.
  by rewrite !addr_ge0 // mulr_ge0 // addr_ge0.
rewrite exprMn sqr_sqrtr //.
have e32 : (32 * K) ^+ 2 = 1024 * K ^+ 2 by rewrite exprMn -natrX.
rewrite e32 /rate_CL -[X in _ <= X]mulrA -[X in _ <= X]mulrA.
apply: ler_wpM2l; first exact: (mulr_ge0 (ler0n _ 1024) (sqr_ge0 K)).
have P1 : m%:R * (1 + lnR (n%:R / m%:R)) <= m%:R * (4 * lnR d%:R).
  by apply: ler_wpM2l => //; exact: ler0n.
have P2 : m%:R * (4 * lnR d%:R) <= C0 * d%:R * lnR d%:R * (4 * lnR d%:R).
  by apply: ler_wpM2r => //; rewrite mulr_ge0.
have ll : lnR d%:R <= lnR d%:R ^+ 2 by rewrite expr2 ler_peMl.
have F1 : C0 * d%:R * lnR d%:R <= C0 * d%:R * lnR d%:R ^+ 2.
  by apply: ler_wpM2l => //; rewrite mulr_ge0 ?ler0n // ltW.
have F2 : d%:R <= d%:R * lnR d%:R ^+ 2 :> R.
  by rewrite ler_peMr ?ler0n // exprn_ege1.
rewrite natrD.
move: P1 P2 F1 F2 mC.
move: (m%:R * (1 + lnR (n%:R / m%:R))) (m%:R : R) (d%:R : R) (lnR d%:R).
move=> P M D l h1 h2 h3 h4 h5; nra.
Qed.

(* Proposition 3.3 on the events of the sparse bounds, at the rates. *)
Lemma sparse_lower_rate (K C0 th L : R) (n d m : nat)
    (x : paper_main_sample n d) :
  0 < K -> 0 < C0 -> (5 <= d)%N -> (0 < m)%N -> (m <= n)%N ->
  1 <= lnR d%:R -> lnR d%:R ^+ 2 <= Num.sqrt d%:R ->
  2 * rate_Cg K C0 * lnR d%:R ^+ 4 <= Num.sqrt d%:R ->
  m%:R <= C0 * d%:R * lnR d%:R -> 1 + lnR (n%:R / m%:R) <= 4 * lnR d%:R ->
  th * Num.sqrt d%:R = lnR d%:R ->
  L ^+ 2 <= rate_CL K C0 * d%:R * lnR d%:R ^+ 2 ->
  (forall u : 'rV[R]_n, (#|supp u| <= m)%N ->
     `|frobenius (sample_adj x u) ^+ 2 / d%:R - mxdot u u| <=
     gram_dev K n d m d%:R^-1 th * mxdot u u) ->
  (forall u : 'rV[R]_n, (#|supp u| <= m)%N ->
     frobenius (sample_comb x u) <= L * frobenius u) ->
  forall h : 'rV[R]_n, (#|supp h| <= m)%N ->
  (\sum_i `|h 0 i|) * Num.sqrt d%:R <=
  rate_CS K C0 * lnR d%:R ^+ 4 * nuclear (sample_adj x h).
Proof.
move=> K0 C00 d5 m0 mn l1 l2 hg mC lnm thl hL hQ hX h hm.
have [dl0 dl1 dl2] :=
  gram_dev_rate K C0 th n d m K0 C00 d5 m0 mn l1 l2 mC lnm thl.
have d0 : (0 < d)%N by apply: leq_trans d5.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have sd0 : 0 < Num.sqrt (d%:R : R) by rewrite sqrtr_gt0.
have l0 : 0 <= lnR d%:R by apply: le_trans l1.
have dh : gram_dev K n d m d%:R^-1 th <= 1 / 2.
  apply: le_trans dl1 _.
  rewrite mulrA ler_pdivrMr //.
  rewrite -mulrA in hg.
  move: hg; move: (rate_Cg K C0 * lnR d%:R ^+ 4) (Num.sqrt (d%:R : R)).
  by move=> a b hab; lra.
(* Proposition 3.3 on the event *)
have S4 := sparse_lower n d x d0 m (gram_dev K n d m d%:R^-1 th) L dl0 dh
  hQ hX h hm.
(* its constant is at most rate_CS d (ln d)^4 *)
have l24 : lnR d%:R ^+ 2 <= lnR d%:R ^+ 4.
  by rewrite (_ : 4 = 2 + 2)%N // exprD ler_peMr ?exprn_ge0 // exprn_ege1.
have l14 : lnR d%:R <= lnR d%:R ^+ 4.
  by apply: le_trans l24; rewrite expr2 ler_peMl.
have CL0 : 0 <= rate_CL K C0 := rate_CL_ge0 K C0 (ltW C00).
have Cg0 : 0 <= rate_Cg K C0 := rate_Cg_ge0 K C0.
have sC0 : 0 <= Num.sqrt C0 := sqrtr_ge0 C0.
have dd0 : 0 <= d%:R :> R := ltW dR.
have one : 1 + 2 * gram_dev K n d m d%:R^-1 th * Num.sqrt (m%:R : R) <=
    1 + 2 * (rate_Cg K C0 * Num.sqrt C0 * lnR d%:R ^+ 2).
  by rewrite -mulrA lerD2l ler_pM2l.
have p1 : L ^+ 2 * (1 + 2 * gram_dev K n d m d%:R^-1 th *
    Num.sqrt (m%:R : R)) <=
    rate_CL K C0 * d%:R * lnR d%:R ^+ 2 *
    (1 + 2 * (rate_Cg K C0 * Num.sqrt C0 * lnR d%:R ^+ 2)).
  apply: (ler_pM (sqr_ge0 _) _ hL one).
  by rewrite addr_ge0 // !mulr_ge0 // sqrtr_ge0.
have F1 : rate_CL K C0 * d%:R * lnR d%:R ^+ 2 <=
    rate_CL K C0 * d%:R * lnR d%:R ^+ 4.
  by apply: ler_wpM2l => //; rewrite mulr_ge0.
have F2 : C0 * d%:R * lnR d%:R <= C0 * d%:R * lnR d%:R ^+ 4.
  by apply: ler_wpM2l => //; rewrite mulr_ge0 // ltW.
have CB : L ^+ 2 * (1 + 2 * gram_dev K n d m d%:R^-1 th *
    Num.sqrt (m%:R : R)) + 2 * m%:R <=
    rate_CS K C0 * d%:R * lnR d%:R ^+ 4.
  rewrite /rate_CS.
  move: p1 F1 F2 mC.
  move: (L ^+ 2 * (1 + 2 * gram_dev K n d m d%:R^-1 th *
    Num.sqrt (m%:R : R))) (rate_CL K C0) (rate_Cg K C0 * Num.sqrt C0).
  move=> P a b h1 h2 h3 h4; nra.
(* divide by d *)
have N0 : 0 <= nuclear (sample_adj x h) := nuclear_ge0 _.
have h2 := le_trans S4 (ler_wpM2r N0 CB).
rewrite -(ler_pM2l dR).
move: h2; move: (\sum_i `|h 0 i|) (nuclear (sample_adj x h)).
move=> A N' h2.
apply: le_trans (_ : A * (d%:R * Num.sqrt (d%:R : R)) <= _).
  by rewrite mulrCA.
apply: le_trans h2 _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

(* 4. Proposition 3.3 with probability tending to one. *)

(* For flat families of component laws whose features satisfy the
   hypotheses of sparse_gram_bound_flat; D does not depend on the laws. *)
Theorem sparse_lower_limit_features (K alpha C0 : R) (n : nat -> nat) :
  0 < K -> 0 < alpha -> universality_density_tends_to n alpha -> 0 < C0 ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  forall lam : nat -> probability (measurableTypeR R) R,
    (forall k, (k < n d * d)%N -> mixture_component_law K (lam k)) ->
    (forall i (y : 'rV[R]_(d * d)), (i < n d)%N -> mxdot y y = 1 ->
       subexponential (data_feature_law (flat_row lam d i) d)
         (fun z => mxdot z y) (252 * K ^+ 2 / Num.sqrt d%:R)) ->
    (forall i (y : 'rV[R]_(d * d)), (i < n d)%N -> mxdot y y = 1 ->
       \int[data_feature_law (flat_row lam d i) d]_v mxdot v y = 0) ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (tuple_prod lam (n d * d) E <= eps%:E)%E &
    forall x, ~ E x -> forall h : 'rV[R]_(n d),
      #|supp h|%:R <= C0 * d%:R * lnR d%:R ->
      (\sum_i `|h 0 i|) * Num.sqrt d%:R <=
      rate_CS K C0 * lnR d%:R ^+ 4 * nuclear (sample_adj x h)].
Proof.
move=> K0 a0 hn C00 eps e0.
set q := Num.min (alpha / 2) 1.
have q0 : 0 < q by rewrite lt_min divr_gt0 // ltr01.
have Cg0 : 0 <= rate_Cg K C0 := rate_Cg_ge0 K C0.
have K2 : 0 < K ^+ 2 by rewrite exprn_gt0.
have c1 := density_ev _ _ a0 hn.
have c3 := ln_pow_le_sqrt 1 2 ltr01.
have p4 : 0 < 2 * rate_Cg K C0 + 1.
  by apply: ltr_wpDl; [exact: (mulr_ge0 (ler0n _ 2) Cg0) | exact: ltr01].
have c4 := ln_pow_le_sqrt (2 * rate_Cg K C0 + 1) 4 p4.
have c5 := ln_pow_le_sqrt (C0 / q) 1 (divr_gt0 C00 q0).
have p6 : 0 < (48 * K ^+ 2)^-1 by rewrite invr_gt0 mulr_gt0.
have c6 := ln_pow_le_sqrt (48 * K ^+ 2)^-1 1 p6.
have [D hD] := ev_and c1 (ev_and ev_ln_ge1 (ev_and c3 (ev_and c4
  (ev_and c5 (ev_and c6 (ev_and (ev_gt (expR (2304 * K ^+ 4)))
  (ev_and (ev_gt (((36 / eps) ^+ 2 + 1) / C0))
  (ev_and (ev_gt (6 * (alpha + 1) / eps)) (ev_and (ev_gt (6 / eps))
  (ev_and (ev_gt (alpha + 1)) (ev_ge 5))))))))))).
exists D => d dD lam hlam hw cen.
have [[h1a h1b] [h2 [h3 [h4 [h5 [h6 [h7 [h9 [h10 [h11 [h12 d5]]]]]]]]]]] :=
  hD d dD.
have d0 : (0 < d)%N by apply: leq_trans d5.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have l1 : 1 <= lnR d%:R := h2.
have l0 : 0 <= lnR d%:R by apply: le_trans l1.
have l2 : lnR d%:R ^+ 2 <= Num.sqrt (d%:R : R) by rewrite mul1r in h3.
have hg : 2 * rate_Cg K C0 * lnR d%:R ^+ 4 <= Num.sqrt (d%:R : R).
  apply: le_trans h4; apply: ler_wpM2r; first exact: exprn_ge0.
  by rewrite lerDl.
have sd0 : 0 < Num.sqrt (d%:R : R) by rewrite sqrtr_gt0.
have sd1 : 1 <= Num.sqrt (d%:R : R).
  by rewrite -{1}sqrtr1 ler_sqrt ?ler0n // ler1n.
have sdd : Num.sqrt (d%:R : R) <= d%:R.
  rewrite -{2}[d%:R](sqr_sqrtr (ltW dR)) expr2.
  by rewrite ler_peMl // ltW.
have x0 : 0 <= C0 * d%:R * lnR d%:R by rewrite !mulr_ge0 // ltW.
pose m := archimedean.Num.truncn (C0 * d%:R * lnR d%:R).
have mC : m%:R <= C0 * d%:R * lnR d%:R.
  by rewrite /m archimedean.Num.Theory.truncn_le.
have C0d : 1 <= C0 * d%:R.
  have e9 : 1 <= (36 / eps) ^+ 2 + 1 by rewrite lerDr sqr_ge0.
  move: h9; rewrite ltr_pdivrMr // => /ltW h.
  by rewrite mulrC; exact: le_trans e9 h.
have m0 : (0 < m)%N.
  rewrite /m archimedean.Num.Theory.truncn_ge_nat //.
  by rewrite -[1%:R]mulr1 ler_pM.
have hCl : C0 * lnR d%:R <= q * d%:R.
  have qn : q != 0 by rewrite gt_eqF.
  have e : C0 * lnR d%:R = q * (C0 / q * lnR d%:R ^+ 1).
    by rewrite expr1; field.
  rewrite e; apply: ler_wpM2l; first exact: ltW.
  exact: le_trans h5 sdd.
have mn : (m <= n d)%N.
  rewrite -(ler_nat R); apply: le_trans mC _; apply: le_trans _ h1a.
  have h := ler_wpM2l (ltW dR) hCl.
  rewrite -/q; move: h; move: (C0 * lnR d%:R) => c h; nra.
have npos : (0 < n d)%N by apply: leq_trans m0 mn.
have nR : 0 < (n d)%:R :> R by rewrite ltr0n.
have mR : 1 <= m%:R :> R by rewrite ler1n.
have nd3 : (n d)%:R <= d%:R ^+ 3 :> R.
  apply: le_trans h1b _.
  have -> : d%:R ^+ 3 = d%:R ^+ 2 * d%:R :> R by rewrite exprSr.
  rewrite mulrC.
  by apply: ler_wpM2l; [exact: exprn_ge0 (ltW dR) | exact: ltW h12].
have lnm : 1 + lnR ((n d)%:R / m%:R) <= 4 * lnR d%:R.
  have h : lnR ((n d)%:R / m%:R) <= 3 * lnR d%:R.
    apply: le_trans (_ : _ <= lnR (d%:R ^+ 3)) _.
      rewrite ler_ln ?posrE ?exprn_gt0 ?divr_gt0 ?ltr0n //.
      apply: le_trans nd3.
      by rewrite ler_pdivrMr ?ltr0n // ler_peMr // ltW.
    by rewrite lnXn // mulr_natl.
  by move: h l1; move: (lnR ((n d)%:R / m%:R)) (lnR d%:R) => a b hab hb; lra.
pose th := lnR d%:R / Num.sqrt (d%:R : R).
have thl : th * Num.sqrt (d%:R : R) = lnR d%:R.
  by rewrite /th divfK // gt_eqF.
have th0 : 0 <= th by rewrite /th divr_ge0 // ltW.
pose L := 32 * K * Num.sqrt (m%:R * (1 + lnR ((n d)%:R / m%:R)) +
  6 * (m + d)%:R + d%:R).
have hL : L ^+ 2 <= rate_CL K C0 * d%:R * lnR d%:R ^+ 2.
  exact: (points_rate K C0 (n d) d m C00 m0 mn l1 mC lnm).
have beta0 : 0 < (d%:R : R)^-1 by rewrite invr_gt0.
have beta1 : (d%:R : R)^-1 <= 1 / 2.
  rewrite mul1r lef_pV2 ?posrE // ler_nat.
  by apply: leq_trans d5.
have [G1 [mG1 PG1 hG1]] := sparse_gram_bound_flat K (n d) d m lam hlam hw cen
  d0 m0 mn (d%:R)^-1 th beta0 beta1 th0.
have [G2 [mG2 PG2 hG2]] := sparse_points_bound_flat K (n d) d lam m
  d%:R hlam d0 m0 mn (ler0n _ d).
have e3 : 0 < eps / 3 by rewrite divr_gt0.
have T3 : 2 * expR (- (d%:R : R)) <= eps / 3.
  have e : expR (- (d%:R : R)) <= d%:R^-1.
    rewrite expRN lef_pV2 ?posrE ?expR_gt0 //.
    by apply: le_trans (expR_ge1Dx _); rewrite lerDr.
  apply: le_trans (ler_wpM2l (ler0n _ 2) e) _.
  have h : 6 < d%:R * eps by rewrite -ltr_pdivrMr.
  rewrite ler_pdivrMr //.
  by move: h; move: (d%:R : R) => dd hdd; lra.
have T1 : 2 * (trunc_log 4 m).+2%:R *
    expR (- (Num.sqrt (m%:R : R) * (1 + lnR ((n d)%:R / m%:R)))) <= eps / 3.
  have b0 : 0 <= lnR ((n d)%:R / m%:R).
    by apply: ln_ge0; rewrite ler_pdivlMr ?ltr0n // mul1r ler_nat.
  have ex : expR (- (Num.sqrt (m%:R : R) * (1 + lnR ((n d)%:R / m%:R)))) <=
      expR (- Num.sqrt (m%:R : R)).
    by rewrite ler_expR lerN2 ler_peMr ?sqrtr_ge0 // lerDl.
  apply: le_trans (ler_wpM2l _ ex) _.
    by rewrite mulr_ge0 // ler0n.
  apply: le_trans (trunc_log_expR_le m m0) _.
  have hm1 := archimedean.Num.Theory.truncnS_gt (C0 * d%:R * lnR d%:R).
  rewrite -/m in hm1.
  have h9' : (36 / eps) ^+ 2 + 1 < C0 * d%:R.
    by move: h9; rewrite ltr_pdivrMr // [d%:R * C0]mulrC.
  have Cl : C0 * d%:R <= C0 * d%:R * lnR d%:R.
    by rewrite ler_peMr // mulr_ge0 // ltW.
  have mq : (36 / eps) ^+ 2 < m%:R.
    have := lt_le_trans h9' Cl; move/lt_trans => /(_ _ hm1).
    by rewrite -[m.+1%:R]natr1 ltrD2r.
  have sm : 36 / eps < Num.sqrt (m%:R : R).
    have e0' : 0 <= 36 / eps by rewrite divr_ge0 // ltW.
    by rewrite -(ger0_norm e0') -sqrtr_sqr ltr_sqrt // ltr0n.
  have h : 36 < Num.sqrt (m%:R : R) * eps by rewrite -ltr_pdivrMr.
  have sm0 : 0 < Num.sqrt (m%:R : R) by rewrite sqrtr_gt0 ltr0n.
  rewrite ler_pdivrMr //.
  by move: h; move: (Num.sqrt (m%:R : R)) => s hs; lra.
have th2d : th ^+ 2 * d%:R = lnR d%:R ^+ 2.
  rewrite /th expr_div_n sqr_sqrtr ?ler0n //.
  by rewrite divfK // gt_eqF.
have thd : th * d%:R = lnR d%:R * Num.sqrt (d%:R : R).
  rewrite /th -[X in _ * X](sqr_sqrtr (ler0n _ d)) expr2.
  by rewrite mulrA divfK // gt_eqF.
have K4 : 0 < K ^+ 4 by rewrite exprn_gt0.
have l48 : lnR d%:R <= 48 * K ^+ 2 * Num.sqrt (d%:R : R).
  have h := h6; rewrite expr1 in h.
  by rewrite -ler_pdivrMl ?mulr_gt0.
have amb : th ^+ 2 * d%:R / (576 * K ^+ 4) <= th * d%:R / (12 * K ^+ 2).
  rewrite th2d thd.
  have e : lnR d%:R ^+ 2 / (576 * K ^+ 4) =
      lnR d%:R * lnR d%:R / (48 * K ^+ 2) / (12 * K ^+ 2).
    have Kn : K != 0 by rewrite gt_eqF.
    by rewrite expr2; field.
  rewrite e; apply: ler_wpM2r; first by rewrite invr_ge0 mulr_ge0 // ltW.
  rewrite ler_pdivrMr ?mulr_gt0 //.
  by rewrite -mulrA [Num.sqrt _ * _]mulrC; apply: ler_wpM2l.
have l7 : 2304 * K ^+ 4 < lnR d%:R.
  by rewrite -[X in X < _](expRK (2304 * K ^+ 4)) ltr_ln ?posrE ?expR_gt0.
have ea : expR (- Num.min (th ^+ 2 * d%:R / (576 * K ^+ 4))
    (th * d%:R / (12 * K ^+ 2))) <= (d%:R ^+ 4)^-1.
  rewrite (min_l amb) th2d.
  have -> : (d%:R ^+ 4)^-1 = expR (- (4%:R * lnR d%:R)).
    by rewrite expRN expRM_natl lnK // posrE.
  rewrite ler_expR lerN2 ler_pdivlMr ?mulr_gt0 //.
  have h := ler_wpM2r l0 (ltW l7).
  have e : 4%:R * lnR d%:R * (576 * K ^+ 4) = 2304 * K ^+ 4 * lnR d%:R.
    by ring.
  by rewrite e expr2.
have T2 : (n d)%:R * (2 * expR (- Num.min (th ^+ 2 * d%:R / (576 * K ^+ 4))
    (th * d%:R / (12 * K ^+ 2)))) <= eps / 3.
  apply: le_trans (ler_wpM2l (ler0n _ _) (ler_wpM2l (ler0n _ 2) ea)) _.
  have w0 : 0 <= 2 * (d%:R ^+ 4)^-1 :> R.
    by rewrite mulr_ge0 // invr_ge0 exprn_ge0 // ler0n.
  apply: le_trans (ler_wpM2r w0 h1b) _.
  have e : (alpha + 1) * d%:R ^+ 2 * (2 * (d%:R ^+ 4)^-1) =
      2 * (alpha + 1) / d%:R / d%:R.
    have dn : d%:R != 0 :> R by rewrite gt_eqF.
    move: dn; move: (d%:R : R) => D' dn.
    by field.
  rewrite e.
  have h : 6 * (alpha + 1) < d%:R * eps by rewrite -ltr_pdivrMr.
  rewrite ler_pdivrMr // ler_pdivrMr //.
  have d1 : 1 <= d%:R :> R by rewrite ler1n.
  have hd : d%:R * eps <= d%:R * eps * d%:R.
    by rewrite ler_peMr // mulr_ge0 // ltW.
  by lra.
exists (~` G1 `|` ~` G2); split.
- exact: measurableU (measurableC mG1) (measurableC mG2).
- apply: le_trans (measureU2 _ (measurableC mG1) (measurableC mG2)) _.
  apply: le_trans (leeD PG1 PG2) _.
  rewrite -EFinD lee_fin.
  by move: T1 T2 T3; lra.
move=> x nE h hs.
have xG1 : G1 x by apply: contrapT => nG; apply: nE; left.
have xG2 : G2 x by apply: contrapT => nG; apply: nE; right.
have hm : (#|supp h| <= m)%N.
  by rewrite /m archimedean.Num.Theory.truncn_ge_nat.
exact: (sparse_lower_rate K C0 th L (n d) d m x K0 C00 d5 m0 mn l1 l2 hg mC
  lnm thl hL (hG1 x xG1) (hG2 x xG2) h hm).
Qed.

(* The same for the sample law of coordinate laws. *)
Theorem sparse_lower_limit (kappa K alpha C0 : R)
    (nu : nat -> nat -> probability (measurableTypeR R) R) (n : nat -> nat) :
  (forall d j, (j < d)%N -> universality_coordinate_law kappa K (nu d j)) ->
  0 < alpha -> universality_density_tends_to n alpha -> 0 < C0 ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (universality_sample_law (nu d) (n d) d E <= eps%:E)%E &
    forall x, ~ E x -> forall h : 'rV[R]_(n d),
      #|supp h|%:R <= C0 * d%:R * lnR d%:R ->
      (\sum_i `|h 0 i|) * Num.sqrt d%:R <=
      rate_CS K C0 * lnR d%:R ^+ 4 * nuclear (sample_adj x h)].
Proof.
move=> hnu a0 hn C00 eps e0.
have K0 : 0 < K by have [] := hnu 1%N 0%N isT.
have [D hD] := sparse_lower_limit_features K alpha C0 n K0 a0 hn C00 eps e0.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d0].
exact: (hD d dD _ (sample_law_component kappa K (n d) d (nu d) (hnu d))
  (sample_law_feature_hw kappa K (n d) d (nu d) (hnu d) d0)
  (sample_law_feature_mean kappa K (n d) d (nu d) (hnu d))).
Qed.
