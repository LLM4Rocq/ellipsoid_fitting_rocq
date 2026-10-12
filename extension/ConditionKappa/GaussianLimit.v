(* The Gaussian limit at fourth moment kappa, at Stdlib's R: items M3, M4
   and M5 of phase 11 (notes/phase11-plan.md, sections 3.3, 5 and 6; the
   math plan notes/general-fourth-moment-condition-plan.md, sections 4.3
   and 4.4; reviews/phase11-plan-review.md, sections 2.3 and 2.4; lane A).

   Setting as in Geometry: kappa > 1, c = (kappa - 3) / 2, a0 = min(1, 1 + c),
   C > 1, K_C = cond_cone C, T = cone_map kappa. a has law gauss (d * d),
   G = goe_part (vec_mx a) (diagonal variance 1, off-diagonal variance 1/2),
   H = G / sqrt d, and W = goe_mx a = sqrt 2 H, of spectral edge 2. X(H) is
   the maximizer of the surrogate objective Phi-bar_H on K_C (item M1).

   Results to prove here.
   - M3, proved. H = goe_half a = goe_mx a / sqrt 2, and
     G = sqrt d H (goe_part_half). kappa_diag_var_cvg: diag_var X(H) -> 0
     in probability (kappa_argmax_diag_var_tail of Geometry, which is
     goe_diag_var_tail of library/random_matrix/goe_rotation.v for
     F(W) = X(W / sqrt 2), with |X|_F^2 <= |H|_F^2 / a0^2 and
     |H|_F^2 / d -> 1/2, goe_half_sqnorm_cvg); goe_half_diag_cvg:
     |diag H|_F / sqrt d -> 0, so goe_half_trace_cvg: tr H / d -> 0
     (trace_le_diag: |tr H| / d <= |diag H|_F / sqrt d);
     kappa_sup_gap_cvg: (sup_K Phi_H - sup_K Phi-bar_H) / d -> 0, by the
     bounds of M2 (kappa_sup_gap_bounds), |D|_F^2 = d diag_var X
     (diag_dev_sqr), |E|_F^2 <= 2 e^2 |diag H|_F^2 + 2 c^2 |D|_F^2 and
     |<diag H, diag X>| <= |diag H|_F |H|_F / a0.
   - M4. (1/d) max_K Phi-bar_H -> alpha(C, kappa) in probability. The route
     is section 3.3 of the plan: the duality in mu,
       max_K Phi-bar_H = opt_mu (|Pi_K(H - c mu I)|_F^2 + c d mu^2),
     a maximum for c < 0 and a minimum for c > 0, attained at
     mu = tr(X) / d (mu = 0 at c = 0); the windows 0 <= mu <= M = 3 / a0
     and 0 <= t <= B = 3 + |c| M on the event |W|_op <= 3, for the random
     and for the limiting optimizers; the three limits, uniform in mu in
     [0, M]: the trace term 2 c mu tr(H) / d, |H|_F^2 / d -> 1/2
     (goe_sqnorm_half of Condition/GaussianCone.v), and the shifted
     clipping energy (1/d) inf_t sum_i dist(lambda_i(H) - c mu, [t, C t])^2
     (wigner_uniform_inf on [0, B] at the points of a net in mu, and a
     Lipschitz bound in mu); and the identification of the limit by
     interface I2.
   - M5. |Pi_{T K_C} G|_F^2 = d max_K Phi_H, and interface I1 below.

   Interface I2 (from item S2, Curve, lane C; used by M4). With
   c = (kappa - 3) / 2, condition_kappa_dual C kappa mu of Curve is
     1/2 + c (1 + c) mu^2 - inf_(t >= 0) (v(-t - c mu) + v(C t + c mu)),
   the limit of (1/d) (|Pi_K(H - c mu I)|_F^2 + c d mu^2). Item S2 proves,
   for C > 1 and kappa > 1: some mu* with 0 <= mu* <= 1 / (sqrt 2 a0) <= M
   and condition_kappa_dual C kappa mu* = condition_kappa_alpha C kappa;
   if kappa <= 3, condition_kappa_dual C kappa mu <= condition_kappa_alpha
   C kappa for every mu; if 3 <= kappa, condition_kappa_alpha C kappa <=
   condition_kappa_dual C kappa mu for every mu. Until S2 lands, M4 may take
   these three facts as hypotheses.

   Interface I1 (the output of M5; used by item G1, GaussianWitness and
   GaussianGap, lane B). sigma_{C,kappa} is the support function of Cone
   (item B1, lane B),
     sigma_{C,kappa}(A) = sup { <A, T S> : S in K_C, |T S|_F <= 1 },
   with the unit ball after T. M5 proves, for C > 1 and kappa > 1,
     cvg_prob (fun d => gauss (d * d))
       (fun d a => sigma_{C,kappa}(vec_mx a) / d)
       (sqrt (condition_kappa_alpha C kappa)),
   the hypothesis hQ2 of Condition/GaussianWitness.v with sigma_{C,kappa}
   in place of cond_support C and alpha(C, kappa) in place of
   condition_alpha C. Since sigma_{C,kappa}(A) = |Pi_{T K_C}(A)|_F for the
   closed convex cone T K_C, this is M3, M4 and the identity of M5. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets interval reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability realfun.
From GaussianAnalysis Require Import euclidean real_spectral opnorm.
From GaussianAnalysis Require Import psd_part measurable_matrix von_neumann.
From GaussianAnalysis Require Import variational gauss goe wigner goe_rotation.
From GaussianAnalysis Require Import semicircle_law gauss_smoothing.
From GaussianAnalysis Require Import condition_cone trace_projection.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.
From EllipsoidUniversality.Gaussian Require Import InProbability Limit.
From EllipsoidUniversality.Condition Require Import GaussianCone.
From EllipsoidUniversality.ConditionKappa Require Import Geometry Cone Curve.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

(* 1. H = W / sqrt 2 = G / sqrt d. *)

Definition goe_half {d : nat} (a : 'rV[RR]_(d * d)) : 'M[R]_d :=
  (Num.sqrt 2)^-1 *: goe_mx a.

Section goe_half.
Variable d : nat.
Implicit Types a : 'rV[RR]_(d * d).

Lemma goe_half_symmetric a : goe_half a \is symmetricmx.
Proof.
apply/symmetricmxP; rewrite /goe_half linearZ /=.
by move/symmetricmxP: (goe_mx_symmetric a) => ->.
Qed.

Lemma goe_part_half a : (0 < d)%N ->
  goe_part (vec_mx a) = Num.sqrt d%:R *: goe_half a.
Proof.
move=> d0; rewrite goe_partE // /goe_half [RHS]scalerA; congr (_ *: _).
by rewrite sqrtrM ?ler0n // sqrtrV ?ler0n.
Qed.

Lemma goe_half_sqnorm a : (0 < d)%N ->
  mxdot (goe_half a) (goe_half a) / d%:R =
  mxdot (goe_part (vec_mx a)) (goe_part (vec_mx a)) / d%:R ^+ 2.
Proof.
move=> d0; rewrite goe_part_half //; move: (goe_half a) => H.
rewrite mxdotZl mxdotZr mulrA -expr2 sqr_sqrtr ?ler0n //.
have dn : d%:R != 0 :> RR by rewrite pnatr_eq0 -lt0n.
by field.
Qed.

Lemma diag_partZ (k : R) (A : 'M[R]_d) : diag_part (k *: A) = k *: diag_part A.
Proof.
by apply/matrixP => i j; rewrite !mxE; case: (i == j); rewrite ?mulr0.
Qed.

Lemma goe_half_diag a : (0 < d)%N ->
  frobenius (diag_part (goe_half a)) / Num.sqrt d%:R =
  frobenius (diag_part (goe_part (vec_mx a))) / d%:R.
Proof.
move=> d0; have sd : 0 < Num.sqrt (d%:R : RR) by rewrite sqrtr_gt0 ltr0n.
rewrite goe_part_half //; move: (goe_half a) => H.
rewrite diag_partZ frobeniusZ ger0_norm ?sqrtr_ge0 //.
have e : d%:R = Num.sqrt d%:R * Num.sqrt d%:R :> RR.
  by rewrite -expr2 sqr_sqrtr ?ler0n.
rewrite [X in _ = _ / X]e.
have s0 : Num.sqrt d%:R != 0 :> RR by rewrite gt_eqF.
by field.
Qed.

(* |tr A| / n <= |diag A|_F / sqrt n. *)
Lemma trace_le_diag (A : 'M[R]_d) : (0 < d)%N ->
  `|\tr A| / d%:R <= frobenius (diag_part A) / Num.sqrt d%:R.
Proof.
move=> d0; have sd : 0 < Num.sqrt (d%:R : RR) by rewrite sqrtr_gt0 ltr0n.
have h := mxtrace_sqr_le (diag_part A).
rewrite mxtrace_diag_part -frobenius_sqr in h.
have e : d%:R = Num.sqrt d%:R ^+ 2 :> RR by rewrite sqr_sqrtr ?ler0n.
rewrite [X in _ / X <= _]e; rewrite [X in _ / X <= _]e in h.
move: (frobenius (diag_part A)) (frobenius_ge0 (diag_part A)) (Num.sqrt d%:R)
  sd h => f f0 s s0 h.
rewrite ler_pdivrMr ?exprn_gt0 // expr2 mulrA divfK ?gt_eqF //.
rewrite ler_pdivrMr ?exprn_gt0 // in h.
have hn := real_normK (num_real (\tr A)); have n0 := normr_ge0 (\tr A).
have fs : 0 <= f * s by rewrite mulr_ge0 // ltW.
by nra.
Qed.

End goe_half.

(* The events of a measurable statistic. *)
Lemma measurable_le_fun n (f : 'rV[RR]_n -> RR) (r : RR) :
  measurable_fun [set: 'rV[RR]_n] f -> measurable [set a | r <= f a].
Proof.
move=> mf; have mI : measurable [set y : RR | r <= y].
  have -> : [set y : RR | r <= y] = [set` Interval (BLeft r) (BInfty _ false)].
    by apply/seteqP; split => y /=; rewrite in_itv /= andbT.
  exact: measurable_itv.
by have := mf measurableT _ mI; rewrite setTI.
Qed.

Lemma measurable_lt_fun n (f : 'rV[RR]_n -> RR) (r : RR) :
  measurable_fun [set: 'rV[RR]_n] f -> measurable [set a | r < f a].
Proof.
move=> mf; have mI : measurable [set y : RR | r < y].
  have -> : [set y : RR | r < y] = [set` Interval (BRight r) (BInfty _ false)].
    by apply/seteqP; split => y /=; rewrite in_itv /= andbT.
  exact: measurable_itv.
by have := mf measurableT _ mI; rewrite setTI.
Qed.

(* 2. M3: the comparison in probability. *)

(* |diag H|_F / sqrt d = |diag G|_F / d -> 0 (goe_diag_cvg of Limit). *)
Lemma goe_half_diag_cvg :
  cvg_prob (fun d => gauss (d * d))
    (fun d a => frobenius (diag_part (goe_half a)) / Num.sqrt d%:R) 0.
Proof.
have := goe_diag_cvg; apply: cvg_prob_eq; exists 1%N => d d1 a.
by rewrite goe_half_diag.
Qed.

(* |tr H| / d <= |diag H|_F / sqrt d -> 0. *)
Lemma goe_half_trace_cvg :
  cvg_prob (fun d => gauss (d * d)) (fun d a => \tr (goe_half a) / d%:R) 0.
Proof.
have hU := goe_half_diag_cvg.
have hL := cvg_probN hU; rewrite oppr0 in hL.
apply: (cvg_prob_squeeze _ hL hU); exists 1%N => d d1 a.
have := trace_le_diag (goe_half a) d1.
by rewrite -ler_norml normrM [`|_^-1|]ger0_norm ?invr_ge0 ?ler0n.
Qed.

(* |H|_F^2 / d = |G|_F^2 / d^2 -> 1/2, and |H|_F / sqrt d -> 1 / sqrt 2. *)
Lemma goe_half_sqnorm_cvg :
  cvg_prob (fun d => gauss (d * d))
    (fun d a => mxdot (goe_half a) (goe_half a) / d%:R) (2%:R^-1).
Proof.
have := goe_sqnorm_half; apply: cvg_prob_eq; exists 1%N => d d1 a.
by rewrite goe_half_sqnorm.
Qed.

Lemma goe_half_norm_cvg :
  cvg_prob (fun d => gauss (d * d))
    (fun d a => frobenius (goe_half a) / Num.sqrt d%:R)
    (Num.sqrt 2%:R^-1).
Proof.
have := cvg_prob_sqrt goe_half_sqnorm_cvg; apply: cvg_prob_eq.
exists 1%N => d d1 a.
by rewrite sqrtrM ?mxdot_ge0 // sqrtrV ?ler0n.
Qed.

(* A statistic bounded in absolute value by one that tends to 0. *)
Lemma cvg_prob_abs_le (Y Z : forall d, 'rV[RR]_(d * d) -> RR) :
  (exists D0 : nat, forall d, (D0 <= d)%N -> forall a, `|Y d a| <= Z d a) ->
  cvg_prob (fun d => gauss (d * d)) Z 0 ->
  cvg_prob (fun d => gauss (d * d)) Y 0.
Proof.
move=> [D0 h] hZ eta e0; apply: negligibleW (hZ eta e0) _.
exists D0 => d dD a /=; rewrite !subr0 => hy.
by apply: le_trans hy (le_trans (h d dD a) (ler_norm _)).
Qed.

Lemma frobenius_diag_le d (A : 'M[R]_d) :
  frobenius (diag_part A) <= frobenius A.
Proof. by rewrite /frobenius ler_sqrt ?mxdot_ge0 // mxdot_diag_part_le. Qed.

Lemma diag_part1 d : diag_part (1%:M : 'M[R]_d) = 1%:M.
Proof. by apply/matrixP => i j; rewrite !mxE; case: (i == j). Qed.

(* |D|_F^2 = d diag_var X. *)
Lemma diag_dev_sqr d (X : 'M[R]_d) : (0 < d)%N ->
  mxdot (diag_dev X) (diag_dev X) = d%:R * diag_var X.
Proof.
move=> d0.
have -> : diag_dev X = diag_part (X - (\tr X / d%:R) *: 1%:M).
  by rewrite diag_partB diag_partZ diag_part1.
rewrite mxdot_diag_part2 /diag_var mulrA mulfV ?mul1r ?pnatr_eq0 -?lt0n //.
by apply: eq_bigr => i _; rewrite !mxE eqxx mulr1.
Qed.

Section kappa_comparison.
Variables (kappa C : R).
Hypotheses (k1 : 1 < kappa) (C0 : 0 <= C).

Local Notation c := (cone_shift kappa).
Local Notation e := (Num.sqrt (1 + cone_shift kappa) - 1).
Local Notation a0 := (Num.min 1 (1 + cone_shift kappa)).

(* diag_var X(H) -> 0: goe_diag_var_tail with |X|_F^2 <= |H|_F^2 / a0^2
   and |H|_F^2 / d -> 1/2. *)
Lemma kappa_diag_var_cvg :
  cvg_prob (fun d => gauss (d * d))
    (fun d a => diag_var (kappa_argmax kappa C (goe_half a))) 0.
Proof.
move=> eta e0 eps p0.
have a0p := a0_gt0 k1.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have hh : 0 < 2%:R^-1 :> RR by rewrite invr_gt0 ltr0n.
have [D1 h1] := goe_half_sqnorm_cvg hh e2.
have B0 : 0 < (a0 ^+ 2)^-1 by rewrite invr_gt0 exprn_gt0.
exists (maxn D1 (archimedean.Num.truncn (4 * (a0 ^+ 2)^-1 / (eta * eps))).+1).
move=> d; rewrite geq_max => /andP[d1 d2].
have d0 : (0 < d)%N by apply: leq_trans d2.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have [A [mA PA hA]] := h1 d d1.
have tail : (gauss (d * d)
    [set a | (eta <= diag_var (kappa_argmax kappa C (goe_half a)))%R] <=
  (2 * (a0 ^+ 2)^-1 / ((d%:R + 2) * eta))%:E +
  gauss (d * d) [set a | ((a0 ^+ 2)^-1 * d%:R <
    mxdot (kappa_argmax kappa C (goe_half a))
          (kappa_argmax kappa C (goe_half a)))%R])%E.
  exact: (kappa_argmax_diag_var_tail d k1 C0 (ltW B0) e0).
have Fm := @kappa_argmax_goe_measurable kappa C d k1 C0.
have mX (i j : 'I_d) : measurable_fun [set: 'rV[RR]_(d * d)]
    (fun a => kappa_argmax kappa C (goe_half a) i j : RR).
  exact: (measurable_fun_mxP _).1 Fm i j.
have mdv : measurable_fun [set: 'rV[RR]_(d * d)]
    (fun a => diag_var (kappa_argmax kappa C (goe_half a)) : RR).
  rewrite /diag_var; apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_sum => j; apply: measurableT_comp (exprn_measurable 2) _.
  apply: measurable_funB => //; apply: measurable_funM => //.
  by rewrite /mxtrace; apply: measurable_sum => i.
have mN2 : measurable_fun [set: 'rV[RR]_(d * d)]
    (fun a => mxdot (kappa_argmax kappa C (goe_half a))
                    (kappa_argmax kappa C (goe_half a)) : RR).
  rewrite /mxdot; apply: measurable_sum => i; apply: measurable_sum => j.
  exact: measurable_funM.
have sub : [set a : 'rV[RR]_(d * d) | (a0 ^+ 2)^-1 * d%:R <
    mxdot (kappa_argmax kappa C (goe_half a))
          (kappa_argmax kappa C (goe_half a))] `<=` A.
  move=> a /= hX; apply: hA => /=.
  have hn := kappa_argmax_norm k1 C0 (goe_half a).
  have f0 := frobenius_ge0 (kappa_argmax kappa C (goe_half a)).
  have hn2 : mxdot (kappa_argmax kappa C (goe_half a))
      (kappa_argmax kappa C (goe_half a)) <=
      mxdot (goe_half a) (goe_half a) * (a0 ^+ 2)^-1.
    rewrite -!frobenius_sqr -expr_div_n.
    by rewrite ler_pXn2r ?nnegrE ?divr_ge0 ?frobenius_ge0 ?(ltW a0p).
  have hH : 1 < mxdot (goe_half a) (goe_half a) / d%:R.
    rewrite ltr_pdivlMr // mul1r.
    by rewrite -(ltr_pM2r B0); apply: lt_le_trans _ hn2; rewrite mulrC.
  by rewrite ler_normr; apply/orP; left; lra.
exists [set a | eta <= diag_var (kappa_argmax kappa C (goe_half a))]; split.
- exact: (measurable_le_fun _ mdv).
- apply: le_trans tail _.
  rewrite [eps]splitr EFinD; apply: leeD.
    rewrite lee_fin.
    have hd : 4 * (a0 ^+ 2)^-1 / (eta * eps) < d%:R.
      apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
      by rewrite ler_nat.
    have pe : 0 < eta * eps by rewrite mulr_gt0.
    rewrite ler_pdivrMr ?mulr_gt0 ?addr_gt0 //.
    rewrite ltr_pdivrMr // in hd.
    by move: hd B0; nra.
  apply: le_trans (le_measure _ _ _ sub) PA.
  + by rewrite inE; exact: (measurable_lt_fun _ mN2).
  + by rewrite inE.
- move=> a /= h; apply: le_trans h _.
  by rewrite subr0 ger0_norm // diag_var_ge0.
Qed.

(* The bounds of the comparison, for d >= 1, with H = goe_half a and
   X = X(H): the gap (sup_K Phi_H - sup_K Phi-bar_H) / d lies between
   (2 e <diag H, diag X> - c |D|_F^2) / d and that plus |E|_F^2 / (a0 d). *)
Lemma kappa_sup_gap_bounds d (a : 'rV[RR]_(d * d)) : (0 < d)%N ->
  2 * e * (mxdot (diag_part (goe_half a))
                 (diag_part (kappa_argmax kappa C (goe_half a))) / d%:R) -
    c * diag_var (kappa_argmax kappa C (goe_half a)) <=
  (sup [set kappa_obj kappa (goe_half a) S | S in cond_cone C] -
   sup [set trace_quad c (goe_half a) S | S in cond_cone C]) / d%:R <=
  2 * e * (mxdot (diag_part (goe_half a))
                 (diag_part (kappa_argmax kappa C (goe_half a))) / d%:R) -
    c * diag_var (kappa_argmax kappa C (goe_half a)) +
  mxdot (kappa_err kappa (goe_half a) (kappa_argmax kappa C (goe_half a)))
        (kappa_err kappa (goe_half a) (kappa_argmax kappa C (goe_half a))) /
    d%:R / a0.
Proof.
move=> d0; have dR : 0 < d%:R :> RR by rewrite ltr0n.
have [hlo hhi] := kappa_argmax_sup k1 C0 (goe_half a).
rewrite (kappa_argmax_quad_sup k1 C0 (goe_half a)).
have hv := kappa_argmax_value kappa C (goe_half a).
rewrite diag_dev_sqr // in hv.
move: hlo hhi hv.
move: (sup [set kappa_obj kappa (goe_half a) S | S in cond_cone C]).
move: (kappa_obj kappa (goe_half a) (kappa_argmax kappa C (goe_half a))).
move: (trace_quad c (goe_half a) (kappa_argmax kappa C (goe_half a))).
move: (mxdot (kappa_err kappa (goe_half a) (kappa_argmax kappa C (goe_half a)))
  (kappa_err kappa (goe_half a) (kappa_argmax kappa C (goe_half a)))).
move: (mxdot (diag_part (goe_half a))
  (diag_part (kappa_argmax kappa C (goe_half a)))).
move: (diag_var (kappa_argmax kappa C (goe_half a))).
move=> v m E2 q p s hlo hhi hv.
have id : 0 < d%:R^-1 :> RR by rewrite invr_gt0.
have dn : d%:R != 0 :> RR by rewrite gt_eqF.
have an : a0 != 0 by rewrite gt_eqF // a0_gt0.
apply/andP; split.
  rewrite ler_pdivlMr //.
  have -> : (2 * e * (m / d%:R) - c * v) * d%:R = 2 * e * m - c * (d%:R * v).
    by field.
  by rewrite -hv; lra.
rewrite ler_pdivrMr //.
have -> : (2 * e * (m / d%:R) - c * v + E2 / d%:R / a0) * d%:R =
    2 * e * m - c * (d%:R * v) + E2 / a0 by field.
by rewrite -hv; lra.
Qed.

Lemma kappa_sup_gap_cvg :
  cvg_prob (fun d => gauss (d * d))
    (fun d a => (sup [set kappa_obj kappa (goe_half a) S | S in cond_cone C] -
       sup [set trace_quad c (goe_half a) S | S in cond_cone C]) / d%:R) 0.
Proof.
have a0p := a0_gt0 k1.
(* <diag H, diag X> / d -> 0 *)
have hY1 : cvg_prob (fun d => gauss (d * d))
    (fun d a => mxdot (diag_part (goe_half a))
      (diag_part (kappa_argmax kappa C (goe_half a))) / d%:R) 0.
  apply: (@cvg_prob_abs_le _ (fun d a =>
    frobenius (diag_part (goe_half a)) / Num.sqrt d%:R *
    (frobenius (goe_half a) / Num.sqrt d%:R) * a0^-1)).
    exists 1%N => d d1 a.
    have dR : 0 < d%:R :> RR by rewrite ltr0n.
    have sd : 0 < Num.sqrt (d%:R : RR) by rewrite sqrtr_gt0.
    have h1 := mxdot_le (diag_part (goe_half a))
      (diag_part (kappa_argmax kappa C (goe_half a))).
    have h2 := frobenius_diag_le (kappa_argmax kappa C (goe_half a)).
    have h3 := kappa_argmax_norm k1 C0 (goe_half a).
    rewrite ler_pdivlMr // in h3.
    have g0 := frobenius_ge0 (diag_part (goe_half a)).
    have i1 := ler_wpM2r (ltW a0p) h1.
    have i2 := ler_wpM2r (ltW a0p) (ler_wpM2l g0 h2).
    have i3 := ler_wpM2l g0 h3.
    have e : d%:R = Num.sqrt d%:R * Num.sqrt d%:R :> RR.
      by rewrite -expr2 sqr_sqrtr ?ler0n.
    rewrite normrM [`|_^-1|]ger0_norm ?invr_ge0 ?ler0n // [X in _ / X <= _]e.
    have s0 : Num.sqrt d%:R != 0 :> RR by rewrite gt_eqF.
    have a00 : a0 != 0 by rewrite gt_eqF.
    have -> : frobenius (diag_part (goe_half a)) / Num.sqrt d%:R *
        (frobenius (goe_half a) / Num.sqrt d%:R) * a0^-1 =
        frobenius (diag_part (goe_half a)) * frobenius (goe_half a) / a0 /
        (Num.sqrt d%:R * Num.sqrt d%:R) by field.
    rewrite ler_pM2r ?invr_gt0 ?mulr_gt0 // ler_pdivlMr //.
    by lra.
  have := cvg_probM (cvg_probM goe_half_diag_cvg goe_half_norm_cvg)
    (cvg_prob_cst _ a0^-1).
  by rewrite !mul0r.
(* |D|_F^2 / d = diag_var X -> 0, and |E|_F^2 / d -> 0 *)
have hY2 := kappa_diag_var_cvg.
have hY3 : cvg_prob (fun d => gauss (d * d))
    (fun d a => mxdot
      (kappa_err kappa (goe_half a) (kappa_argmax kappa C (goe_half a)))
      (kappa_err kappa (goe_half a) (kappa_argmax kappa C (goe_half a))) /
      d%:R) 0.
  apply: (@cvg_prob_abs_le _ (fun d a =>
    2 * e ^+ 2 * ((frobenius (diag_part (goe_half a)) / Num.sqrt d%:R) *
                  (frobenius (diag_part (goe_half a)) / Num.sqrt d%:R)) +
    2 * c ^+ 2 * diag_var (kappa_argmax kappa C (goe_half a)))).
    exists 1%N => d d1 a.
    have dR : 0 < d%:R :> RR by rewrite ltr0n.
    have sd : 0 < Num.sqrt (d%:R : RR) by rewrite sqrtr_gt0.
    rewrite ger0_norm ?divr_ge0 ?mxdot_ge0 ?ler0n //.
    have hv := diag_dev_sqr (kappa_argmax kappa C (goe_half a)) d1.
    rewrite /kappa_err; move: hv.
    move: (diag_var (kappa_argmax kappa C (goe_half a))).
    move: (diag_part (goe_half a))
      (diag_dev (kappa_argmax kappa C (goe_half a))) => P Q v hv.
    have fe : frobenius P / Num.sqrt d%:R * (frobenius P / Num.sqrt d%:R) =
        mxdot P P / d%:R.
      by rewrite -expr2 expr_div_n frobenius_sqr sqr_sqrtr ?ler0n.
    have dn : d%:R != 0 :> RR by rewrite gt_eqF.
    rewrite fe ler_pdivrMr //.
    have -> : (2 * e ^+ 2 * (mxdot P P / d%:R) + 2 * c ^+ 2 * v) * d%:R =
        2 * e ^+ 2 * mxdot P P + 2 * c ^+ 2 * (d%:R * v) by field.
    rewrite -hv.
    have sq := mxdot_ge0 (e *: P + c *: Q).
    rewrite !(mxdotDl, mxdotDr, mxdotNl, mxdotNr, mxdotZl, mxdotZr) in sq *.
    rewrite (mxdotC Q P) in sq *.
    by lra.
  have := cvg_probD
    (cvg_probM (cvg_prob_cst _ (2 * e ^+ 2))
      (cvg_probM goe_half_diag_cvg goe_half_diag_cvg))
    (cvg_probM (cvg_prob_cst _ (2 * c ^+ 2)) hY2).
  by rewrite !mulr0 addr0.
have hL := cvg_probB (cvg_probM (cvg_prob_cst _ (2 * e)) hY1)
  (cvg_probM (cvg_prob_cst _ c) hY2).
rewrite !mulr0 subrr in hL.
have hU := cvg_probD hL (cvg_probM hY3 (cvg_prob_cst _ a0^-1)).
rewrite mul0r addr0 in hU.
apply: (cvg_prob_squeeze _ hL hU); exists 1%N => d d1 a.
exact: kappa_sup_gap_bounds.
Qed.

End kappa_comparison.

(* 3. M4: the duality in mu, deterministic. A_mu = H - c mu I, and
   P(A) = |A|_F^2 - cond_dist C A is the maximum of 2 <A, S> - |S|_F^2
   over S in K_C (cond_value_ge, cond_value_le). *)

Section duality.
Variables (C : R) (d : nat).
Hypotheses (C1 : 1 <= C) (d0 : (0 < d)%N).
Implicit Types (A H S Y : 'M[R]_d).

Lemma cond_value_ge A S : A \is symmetricmx -> cond_cone C S ->
  2 * mxdot A S - mxdot S S <= mxdot A A - cond_dist C A.
Proof.
move=> As KS; have [t t0 ht] := cond_energy_le As KS.
have := @cond_dist_le _ d C t A t0.
have -> : 2 * mxdot A S - mxdot S S = mxdot A A - mxdot (A - S) (A - S).
  by rewrite mxdotBl !mxdotBr (mxdotC S A); ring.
by lra.
Qed.

Lemma cond_value_le A Y : A \is symmetricmx -> cond_cone C Y ->
  (forall S, cond_cone C S -> mxdot (A - Y) (S - Y) <= 0) ->
  mxdot A A - cond_dist C A <= 2 * mxdot A Y - mxdot Y Y.
Proof.
move=> As KY hY.
suff : mxdot A A - (2 * mxdot A Y - mxdot Y Y) <= cond_dist C A by lra.
apply: cond_dist_ge => t t0.
have Kt := @cond_clip_cone _ d C t A C1 t0.
have hS := hY _ Kt.
rewrite -(@cond_clip_energy _ d C t A C1 t0 As).
move: (cond_clip C t A) hS => S hS.
have := mxdot_ge0 (S - Y).
rewrite !mxdotBl !mxdotBr in hS *.
rewrite ?(mxdotC S A) ?(mxdotC Y A) ?(mxdotC Y S) in hS *.
by lra.
Qed.

Lemma scalar_mx_dot (k : R) A : mxdot (k%:M : 'M[R]_d) A = k * \tr A.
Proof. by rewrite -scalemx1 mxdotZl mxdot1l. Qed.

(* Phi-bar_H(S) = 2 <H - c mu I, S> - |S|_F^2 + c d mu^2
   - c d (tr S / d - mu)^2. *)
Lemma trace_quad_split (c mu : R) H S :
  trace_quad c H S =
  2 * mxdot (H - (c * mu)%:M) S - mxdot S S + c * d%:R * mu ^+ 2 -
  c * d%:R * (\tr S / d%:R - mu) ^+ 2.
Proof.
have dn : d%:R != 0 :> RR by rewrite pnatr_eq0 -lt0n.
rewrite /trace_quad mxdotBl scalar_mx_dot.
by field.
Qed.

Lemma shift_sym H (m : R) : H \is symmetricmx -> H - m%:M \is symmetricmx.
Proof.
move=> Hs; apply/symmetricmxP; rewrite linearB /= tr_scalar_mx.
by move/symmetricmxP: Hs => ->.
Qed.

Section kappa_duality.
Variable kappa : R.
Hypothesis k1 : 1 < kappa.
Hypothesis C0 : 0 <= C.

Local Notation c := (cone_shift kappa).
Local Notation argmax H := (kappa_argmax kappa C H).
Local Notation Pv A := (mxdot A A - cond_dist C A).

(* For c <= 0, P(A_mu) + c d mu^2 <= max_K Phi-bar_H for every mu. *)
Lemma kappa_dual_le (mu : R) H : H \is symmetricmx -> c <= 0 ->
  Pv (H - (c * mu)%:M) + c * d%:R * mu ^+ 2 <= trace_quad c H (argmax H).
Proof.
move=> Hs c0.
have As := shift_sym (c * mu)%R Hs.
suff : Pv (H - (c * mu)%:M) <= trace_quad c H (argmax H) - c * d%:R * mu ^+ 2.
  by lra.
suff : mxdot (H - (c * mu)%:M) (H - (c * mu)%:M) -
    (trace_quad c H (argmax H) - c * d%:R * mu ^+ 2) <=
    cond_dist C (H - (c * mu)%:M) by lra.
apply: cond_dist_ge => t t0.
have Kt := @cond_clip_cone _ d C t (H - (c * mu)%:M) C1 t0.
rewrite -(@cond_clip_energy _ d C t (H - (c * mu)%:M) C1 t0 As).
have hge := kappa_argmax_ge k1 C0 H Kt.
have pen := mulr_ge0 (ltW (a0_gt0 k1))
  (mxdot_ge0 (cond_clip C t (H - (c * mu)%:M) - argmax H)).
rewrite (trace_quad_split c mu H) in hge.
have hsq := mulr_le0_ge0 (mulr_le0_ge0 c0 (ler0n _ d))
  (sqr_ge0 (\tr (cond_clip C t (H - (c * mu)%:M)) / d%:R - mu)).
move: (cond_clip C t (H - (c * mu)%:M)) hge pen hsq => S hge pen hsq.
move: (H - (c * mu)%:M) hge => A hge.
rewrite mxdotBl !mxdotBr (mxdotC S A).
by lra.
Qed.

(* For c >= 0, max_K Phi-bar_H <= P(A_mu) + c d mu^2 for every mu. *)
Lemma kappa_dual_ge (mu : R) H : H \is symmetricmx -> 0 <= c ->
  trace_quad c H (argmax H) <= Pv (H - (c * mu)%:M) + c * d%:R * mu ^+ 2.
Proof.
move=> Hs c0.
have As := shift_sym (c * mu)%R Hs.
have [KX _] := kappa_argmaxP k1 C0 H.
have hv := cond_value_ge As KX.
have hsq := mulr_ge0 (mulr_ge0 c0 (ler0n _ d))
  (sqr_ge0 (\tr (argmax H) / d%:R - mu)).
rewrite (trace_quad_split c mu H).
by lra.
Qed.

(* At mu = tr X / d, max_K Phi-bar_H = P(H - c mu I) + c d mu^2. *)
Lemma kappa_dual_eq H : H \is symmetricmx ->
  trace_quad c H (argmax H) =
  Pv (H - (c * (\tr (argmax H) / d%:R))%:M) +
  c * d%:R * (\tr (argmax H) / d%:R) ^+ 2.
Proof.
move=> Hs.
have As := shift_sym (c * (\tr (argmax H) / d%:R))%R Hs.
have [KX hX] := kappa_argmaxP k1 C0 H.
have h1 := cond_value_ge As KX.
have h2 : Pv (H - (c * (\tr (argmax H) / d%:R))%:M) <=
    2 * mxdot (H - (c * (\tr (argmax H) / d%:R))%:M) (argmax H) -
    mxdot (argmax H) (argmax H).
  apply: cond_value_le => // S KS.
  have -> : H - (c * (\tr (argmax H) / d%:R))%:M - argmax H =
      H - argmax H - (c * (\tr (argmax H) / d%:R)) *: 1%:M.
    by rewrite -scalemx1 addrAC.
  exact: hX.
rewrite (trace_quad_split c (\tr (argmax H) / d%:R)%R H).
rewrite subrr expr0n /= mulr0 subr0.
by apply/eqP; rewrite eq_le; apply/andP; split; lra.
Qed.

End kappa_duality.
End duality.

(* 4. M4: the shifted clipping energy. *)

(* shift_fun C m t x = dist(x / sqrt 2 - m, [t, C t])^2 when C >= 1 and
   t >= 0 (shift_funE): at an eigenvalue x of W, the summand of
   cond_energy C t (H - m I). *)
Definition shift_fun (C m t x : R) : R :=
  (Num.max (Num.max (t - (x / Num.sqrt 2 - m)) ((x / Num.sqrt 2 - m) - C * t))
     0 ^+ 2)%R.

Lemma shift_funE (C m t x : R) : 1 <= C -> 0 <= t ->
  shift_fun C m t x = itv_dist t (C * t) (x / Num.sqrt 2 - m) ^+ 2.
Proof.
by move=> C1 t0; rewrite /shift_fun (itv_dist_maxE C t _ C1 t0).
Qed.

Lemma shift_fun_continuous (C m t : R) : continuous (shift_fun C m t).
Proof.
move=> x; rewrite /shift_fun.
apply: (@continuous_comp _ _ _ (fun y : R => Num.max (Num.max
  (t - (y / Num.sqrt 2 - m)) ((y / Num.sqrt 2 - m) - C * t)) 0)
  (fun y => y ^+ 2)); last exact: exprn_continuous.
apply: continuous_max; last exact: cvg_cst.
apply: continuous_max.
  by apply: cvgB; [exact: cvg_cst|apply: cvgB;
    [apply: cvgM; [exact: cvg_id|exact: cvg_cst]|exact: cvg_cst]].
by apply: cvgB; [apply: cvgB;
  [apply: cvgM; [exact: cvg_id|exact: cvg_cst]|exact: cvg_cst]|exact: cvg_cst].
Qed.

(* The Lipschitz bound in t, x and m together. *)
Lemma shift_fun_lipschitz (C Bt Bm m m' t s x y : R) : 1 <= C ->
  0 <= t <= Bt -> 0 <= s <= Bt -> -3 <= x <= 3 -> -3 <= y <= 3 ->
  `|m| <= Bm -> `|m'| <= Bm ->
  `|shift_fun C m t x - shift_fun C m' s y| <=
  2 * ((1 + C) * Bt + 2 * (3 + Bm)) * (1 + C) *
  (`|t - s| + `|x - y| + `|m - m'|).
Proof.
move=> C1 /andP[t0 tB] /andP[s0 sB] /andP[x1 x2] /andP[y1 y2] hm hm'.
rewrite !shift_funE //.
have s1 : 1 <= Num.sqrt 2 :> RR := sqrt2_ge1.
have i0 : 0 < (Num.sqrt 2 : RR)^-1 by rewrite invr_gt0 (lt_le_trans ltr01).
have i1 : (Num.sqrt 2 : RR)^-1 <= 1 by rewrite invf_le1 ?(lt_le_trans ltr01).
have hsc (z : R) : -3 <= z <= 3 -> `|z / Num.sqrt 2| <= 3.
  move=> /andP[z1 z2]; rewrite normrM [`|_^-1|]ger0_norm ?(ltW i0) //.
  have : `|z| <= 3 by rewrite ler_norml z1 z2.
  by move=> h; apply: le_trans (ler_pM (normr_ge0 _) (ltW i0) h i1) _;
    rewrite mulr1.
have hp : `|x / Num.sqrt 2 - m| <= 3 + Bm.
  apply: le_trans (ler_normB _ _) _.
  by apply: lerD => //; apply: hsc; rewrite x1 x2.
have hq : `|y / Num.sqrt 2 - m'| <= 3 + Bm.
  apply: le_trans (ler_normB _ _) _.
  by apply: lerD => //; apply: hsc; rewrite y1 y2.
have hpq : `|(x / Num.sqrt 2 - m) - (y / Num.sqrt 2 - m')| <=
    `|x - y| + `|m - m'|.
  have -> : (x / Num.sqrt 2 - m) - (y / Num.sqrt 2 - m') =
      (x - y) / Num.sqrt 2 - (m - m') by ring.
  apply: le_trans (ler_normB _ _) _; apply: lerD => //.
  rewrite normrM [`|_^-1|]ger0_norm ?(ltW i0) //.
  by apply: le_trans (ler_pM (normr_ge0 _) (ltW i0) (lexx _) i1) _;
    rewrite mulr1.
move: (x / Num.sqrt 2 - m) (y / Num.sqrt 2 - m') hp hq hpq => p q hp hq hpq.
have tC : t <= C * t by rewrite ler_peMl.
have sC : s <= C * s by rewrite ler_peMl.
have hu : `|itv_dist t (C * t) p - itv_dist s (C * s) q| <=
    (1 + C) * `|t - s| + `|x - y| + `|m - m'|.
  apply: le_trans (ler_distD (itv_dist s (C * s) p) _ _) _.
  have h1 := itv_dist_shift t (C * t) s (C * s) p.
  have h2 := itv_dist_lipschitz p q sC.
  rewrite -mulrBr normrM [`|C|]ger0_norm ?(le_trans ler01) // in h1.
  by lra.
have ub (a b z : R) : itv_dist a b z <= `|a| + `|b| + 2 * `|z|.
  exact: itv_dist_le.
have u0 := itv_dist_ge0 t (C * t) p; have v0 := itv_dist_ge0 s (C * s) q.
have u1 := ub t (C * t) p; have v1 := ub s (C * s) q.
rewrite (ger0_norm t0) (ger0_norm (mulr_ge0 (le_trans ler01 C1) t0)) in u1.
rewrite (ger0_norm s0) (ger0_norm (mulr_ge0 (le_trans ler01 C1) s0)) in v1.
move: (itv_dist t (C * t) p) (itv_dist s (C * s) q) u0 v0 u1 v1 hu.
move=> u v u0 v0 u1 v1 hu.
rewrite subr_sqr normrM.
have hU : `|u + v| <= 2 * ((1 + C) * Bt + 2 * (3 + Bm)).
  rewrite ger0_norm ?addr_ge0 //.
  have h1 : C * t <= C * Bt by rewrite ler_wpM2l // (le_trans ler01).
  have h2 : C * s <= C * Bt by rewrite ler_wpM2l // (le_trans ler01).
  by lra.
have hd0 := normr_ge0 (u - v).
have L0 : 0 <= 2 * ((1 + C) * Bt + 2 * (3 + Bm)).
  by apply: le_trans hU; exact: normr_ge0.
have hfac : `|u - v| <= (1 + C) * (`|t - s| + `|x - y| + `|m - m'|).
  have := normr_ge0 (x - y); have := normr_ge0 (m - m'); move: hu; nra.
apply: le_trans (ler_pM (normr_ge0 _) (normr_ge0 _) hfac hU) _.
by rewrite [X in X <= _]mulrC mulrA.
Qed.

(* int ((a - y)_+^2 + (y - b)_+^2) dnu(y) = s(-a) + s(b), for the
   symmetric law nu of radius sqrt 2 (as clip_energyE of
   library/probability/variational.v, for any two endpoints). *)
Lemma threshold_clip_integral (a b : R) :
  \int[threshold_law]_y (Num.max (a - y) 0 ^+ 2 + Num.max (y - b) 0 ^+ 2) =
  universality_s (- a)%R + universality_s b.
Proof.
have i0 := integrable_upper_pow threshold_law2 (- a) (isT : (2 <= 2)%N).
have i1 : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun y => Num.max (a - (y : R)) 0 ^+ 2)).
  have := integrable_sym threshold_law_sym i0.
  by apply: eq_integrable => // y _ /=; rewrite opprK addrC.
have i2 := integrable_upper_pow threshold_law2 b (isT : (2 <= 2)%N).
rewrite RintegralD // !universality_sE; congr (_ + _).
have -> : \int[threshold_law]_y Num.max (a - (y : R)) 0 ^+ 2 =
    \int[threshold_law]_y (Num.max ((- (y : R)) - (- a)) 0 ^+ 2).
  by apply: eq_Rintegral => y _; rewrite opprK addrC.
exact: (Rintegral_sym threshold_law_sym i0).
Qed.

(* The integral of shift_fun against the semicircle law of radius 2. *)
Lemma shift_fun_integral (C m t : R) : 1 <= C -> 0 <= t ->
  \int[semicircle_prob 2]_x shift_fun C m t x =
  universality_s (- t - m)%R + universality_s (C * t + m)%R.
Proof.
move=> C1 t0.
rewrite -opprD -threshold_clip_integral /Rintegral.
have s2 : 0 < (Num.sqrt (2%:R : R))^-1 by rewrite invr_gt0 sqrtr_gt0 ltr0n.
pose g (y : R) := Num.max (t + m - y) 0 ^+ 2 + Num.max (y - (C * t + m)) 0 ^+ 2.
have g0 y : 0 <= g y by rewrite addr_ge0 // exprn_even_ge0.
have := @ge0_integral_semicircle_scale RR 2 (Num.sqrt 2%:R)^-1
  (fun y => (g y)%:E) (ltr0n RR 2) s2.
have q2 : (Num.sqrt (2%:R : R))^-1 * 2 = Num.sqrt 2%:R.
  have e : Num.sqrt (2%:R : R) ^+ 2 = 2 by rewrite sqr_sqrtr ?ler0n.
  by rewrite -{2}e expr2 mulrA mulVf ?mul1r // gt_eqF ?sqrtr_gt0 ?ltr0n.
rewrite q2 => h; rewrite -h.
- by move=> y; rewrite lee_fin.
- apply/measurable_EFinP; apply: measurable_funD; apply: measurable_funX.
    apply: measurable_maxr; last exact: measurable_cst.
    by apply: measurable_funB; [exact: measurable_cst|exact: measurable_id].
  apply: measurable_maxr; last exact: measurable_cst.
  by apply: measurable_funB; [exact: measurable_id|exact: measurable_cst].
- congr fine; apply: eq_integral => x _; congr EFin.
  rewrite (shift_funE m x C1 t0) (itv_dist_sqrE C t _ C1 t0) /g.
  by congr (_ + _); congr (Num.max _ 0 ^+ 2); ring.
Qed.

(* The spectrum of H - m I with H = W / sqrt 2. *)
Lemma spec_shift n (A : 'M[R]_n) (w : R) : A \is symmetricmx ->
  spec (A - w%:M) = spec A - const_mx w.
Proof.
move=> As; have [P Po E] := spec_shift_decomposition w As.
rewrite E spec_conj_diag // => i j ij.
rewrite !mxE lerD2r.
by have := spec_decr A ij; rewrite !mxE.
Qed.

Lemma cond_energy_shift_goe d (a : 'rV[RR]_(d * d)) (C m t : R) :
  (0 < d)%N -> 1 <= C -> 0 <= t ->
  cond_energy C t (goe_half a - m%:M) = d%:R * goe_stat (shift_fun C m t) a.
Proof.
move=> d0 C1 t0.
have i0 : 0 <= (Num.sqrt (2%:R : RR))^-1 by rewrite invr_ge0 sqrtr_ge0.
rewrite /cond_energy spec_shift ?goe_half_symmetric //.
rewrite /goe_half (spec_scale (goe_mx_symmetric a) i0) /goe_stat.
have dn : d%:R != 0 :> RR by rewrite gt_eqF ?ltr0n.
rewrite [RHS]mulrC divfK //; apply: eq_bigr => i _.
rewrite (shift_funE m _ C1 t0).
by congr (itv_dist _ _ _ ^+ 2); rewrite !mxE mulrC.
Qed.

(* On opnorm W <= 3 and for 3 + |m| <= B, cond_dist C (H - m I) / d is
   the infimum over t in [0, B] of the mean of shift_fun C m t over the
   eigenvalues of W. *)
Lemma cond_dist_shift_goe d (a : 'rV[RR]_(d * d)) (C m B : R) :
  (0 < d)%N -> 1 <= C -> opnorm (goe_mx a) <= 3 -> 3 + `|m| <= B ->
  cond_dist C (goe_half a - m%:M) / d%:R =
  inf [set goe_stat (shift_fun C m t) a | t in [set t : R | 0 <= t <= B]].
Proof.
move=> d0 C1 ho hB.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have B0 : 0 <= B by apply: le_trans hB; rewrite addr_ge0 ?ler0n ?normr_ge0.
have i0 : 0 <= (Num.sqrt (2%:R : RR))^-1 by rewrite invr_ge0 sqrtr_ge0.
have hV i : spec (goe_half a - m%:M) 0 i <= B.
  rewrite spec_shift ?goe_half_symmetric // /goe_half.
  rewrite (spec_scale (goe_mx_symmetric a) i0) !mxE.
  have s1 := sqrt2_ge1.
  have i1 : (Num.sqrt (2%:R : RR))^-1 <= 1.
    by rewrite invf_le1 ?(lt_le_trans ltr01).
  have h := spec_le_opnorm i (goe_mx_symmetric a).
  have h2 : `|(Num.sqrt 2%:R)^-1 * spec (goe_mx a) 0 i| <= 3.
    rewrite normrM ger0_norm //.
    apply: le_trans (ler_pM i0 (normr_ge0 _) i1 (le_trans h ho)) _.
    by rewrite mul1r.
  rewrite !mxE in h2.
  move: h2; rewrite ler_norml => /andP[_ h2].
  by have := ler_norm (- m); rewrite normrN; lra.
rewrite (cond_dist_itv C1 B0 hV).
have -> : [set cond_energy C t (goe_half a - m%:M) |
    t in [set t : R | 0 <= t <= B]] =
    [set d%:R * goe_stat (shift_fun C m t) a | t in [set t : R | 0 <= t <= B]].
  by apply: eq_imagel => t /andP[t0 _]; rewrite cond_energy_shift_goe.
rewrite inf_mulr //.
- by exists 0; rewrite /= lexx B0.
- move=> t /andP[t0 _]; rewrite /goe_stat divr_ge0 ?ler0n //.
  by apply: sumr_ge0 => i _; rewrite /shift_fun exprn_even_ge0.
- by rewrite mulrC mulKf // gt_eqF.
Qed.

(* The window of the limit: for sqrt 2 + |m| <= B, the infimum over
   t >= 0 of s(-t - m) + s(C t + m) is attained in [0, B]. *)
Lemma clip_shift_window (C m B : R) : 1 <= C -> Num.sqrt 2 + `|m| <= B ->
  inf [set universality_s (- t - m)%R + universality_s (C * t + m)%R |
       t in [set t : R | 0 <= t <= B]] =
  inf [set universality_s (- t - m)%R + universality_s (C * t + m)%R |
       t in [set t : R | 0 <= t]].
Proof.
move=> C1 hB.
have s0 : 0 <= Num.sqrt 2 :> RR by exact: sqrtr_ge0.
have B0 : 0 <= B by apply: le_trans hB; rewrite addr_ge0 ?normr_ge0.
have g0 t : 0 <= universality_s (- t - m)%R + universality_s (C * t + m)%R.
  by rewrite addr_ge0 // universality_sE upper_moment_ge0.
have lb1 : has_lbound [set universality_s (- t - m)%R +
    universality_s (C * t + m)%R | t in [set t : R | 0 <= t <= B]].
  by exists 0 => _ [t _ <-].
have lb2 : has_lbound [set universality_s (- t - m)%R +
    universality_s (C * t + m)%R | t in [set t : R | 0 <= t]].
  by exists 0 => _ [t _ <-].
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: lb_le_inf; first by exists (universality_s (- 0 - m)%R +
    universality_s (C * 0 + m)%R), 0 => //=; rewrite lexx.
  move=> _ [t t0 <-].
  have [tB|Bt] := leP t B.
    by apply: ge_inf => //; exists t => //=; rewrite t0 tB.
  apply: le_trans (_ : universality_s (- B - m)%R +
    universality_s (C * B + m)%R <= _).
    by apply: ge_inf => //; exists B => //=; rewrite B0 lexx.
  have hCB : Num.sqrt 2%:R <= C * B + m.
    have := ler_norm (- m); rewrite normrN.
    have : B <= C * B by rewrite ler_peMl.
    by lra.
  rewrite (universality_s_out (C * B + m)%R hCB) addr0.
  have hab : - t - m <= - B - m by lra.
  have := upper_moment2_lipschitz threshold_law2 hab.
  rewrite -!universality_sE => /andP[h1 _].
  have := universality_sE (C * t + m)%R.
  have := upper_moment_ge0 threshold_law 2 (C * t + m)%R.
  by lra.
apply: lb_le_inf; first by exists (universality_s (- 0 - m)%R +
  universality_s (C * 0 + m)%R), 0 => //=; rewrite lexx B0.
move=> _ [t /andP[t0 _] <-].
by apply: ge_inf => //; exists t.
Qed.
