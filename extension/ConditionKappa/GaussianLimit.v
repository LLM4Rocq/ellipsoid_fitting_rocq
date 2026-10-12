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
