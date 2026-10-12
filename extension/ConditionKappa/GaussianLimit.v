(* The Gaussian limit at fourth moment kappa, at Stdlib's R: items M3, M4
   and M5 of phase 11 (notes/phase11-plan.md, sections 3.3, 5 and 6; the
   math plan notes/general-fourth-moment-condition-plan.md, sections 4.3
   and 4.4; reviews/phase11-plan-review.md, sections 2.3 and 2.4; lane A).

   Setting as in Geometry: kappa > 1, c = (kappa - 3) / 2, a0 = min(1, 1 + c),
   C > 1, K_C = cond_cone C, T = cone_map kappa. a has law gauss (d * d),
   G = goe_part (vec_mx a) (diagonal variance 1, off-diagonal variance 1/2),
   H = G / sqrt d, and W = goe_mx a = sqrt 2 H, of spectral edge 2. X(H) is
   the maximizer of the surrogate objective Phi-bar_H on K_C (item M1).

   Results proved here.
   - M3. H = goe_half a = goe_mx a / sqrt 2, and
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
   - M4: kappa_quad_sup_cvg, (1/d) sup_K Phi-bar_H ->
     alpha(C, kappa) in probability, for C > 1 and kappa > 1. The route is
     section 3.3 of the plan, with P(A) = |A|_F^2 - cond_dist C A, the
     maximum of 2 <A, S> - |S|_F^2 over S in K_C (cond_value_ge,
     cond_value_le).
     - The duality in mu (section 3): P(H - c mu I) + c d mu^2 is at most
       max_K Phi-bar_H for c <= 0 (kappa_dual_le) and at least it for
       c >= 0 (kappa_dual_ge), for every mu, with equality at
       mu = tr X / d (kappa_dual_eq), for every c.
     - The windows: 0 <= tr X / d <= M = 1 / a0 when |H|_F^2 / d <= 1
       (kappa_argmax_trace_window), and t in [0, B], B = 3 + |c| M, on
       opnorm W <= 3 (cond_dist_shift_goe, which writes
       cond_dist C (H - c mu I) / d as the infimum over t in [0, B] of the
       mean of shift_fun C (c mu) t over the eigenvalues of W).
     - The three limits, uniform in mu in [0, M]: the trace term
       2 c mu tr H / d (goe_half_trace_cvg), |H|_F^2 / d -> 1/2
       (goe_half_sqnorm_cvg), and the shifted clipping energy
       (shift_inf_unif: wigner_uniform_inf at the points of a net in mu,
       and Lipschitz bounds in mu).
     - The identification: quad_shift_norm and kappa_dual_window, from
       shift_fun_integral and clip_shift_window, give
       (P(H - c mu I) + c d mu^2) / d within three errors of
       condition_kappa_dual C kappa mu (interface I2), and the squeeze
       kappa_quad_close uses the three facts of item S2 below.
   - M5: kcond_support_cvg, interface I1 below. For a closed
     convex cone K of row vectors, the maximum over K of 2 <z, y> - |y|^2
     is |Pi_K(z)|^2, attained at Pi_K(z) (cone_proj_value). On T K_C,
     2 <A, T S> - |T S|_F^2 = Phi_G(S) with G the symmetric part of A
     (kappa_obj_vec), and Phi_(sqrt d H)(sqrt d S) = d Phi_H(S)
     (kappa_objZ), so sigma_{C,kappa}(vec_mx a)^2 = |Pi_{T K_C} G|_F^2
     = d sup_K Phi_H (kcond_support_sqr, from kcond_support_proj of Cone).
     M3 and M4 then give sup_K Phi_H / d -> alpha(C, kappa).

   Interface I2 (from item S2, Curve, lane C; used by M4). With
   c = (kappa - 3) / 2, condition_kappa_dual C kappa mu of Curve is
     1/2 + c (1 + c) mu^2 - inf_(t >= 0) (v(-t - c mu) + v(C t + c mu)).
   Item S2 proves, for C > 1 and kappa > 1, the three facts that M4 uses:
   some mu0 with 0 <= mu0 <= 1 / (sqrt 2 a0) and
   condition_kappa_dual C kappa mu0 = condition_kappa_alpha C kappa
   (condition_kappa_dual_opt); if kappa <= 3, condition_kappa_dual C kappa
   mu <= condition_kappa_alpha C kappa for every mu
   (condition_kappa_dual_le); if 3 <= kappa, the reverse inequality
   (condition_kappa_dual_ge).

   Interface I1 (the output of M5; used by item G1, GaussianWitness and
   GaussianGap, lane B). sigma_{C,kappa} is the support function of Cone
   (item B1, lane B),
     sigma_{C,kappa}(A) = sup { <A, T S> : S in K_C, |T S|_F <= 1 },
   with the unit ball after T. M5 (kcond_support_cvg) proves, for C > 1
   and kappa > 1,
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
From GaussianAnalysis Require Import moreau condition_cone trace_projection.
From EllipsoidFitting Require Import PaperMainDefinitions.
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

(* 5. M4: the shifted clipping energy converges uniformly in mu. *)

(* A finite union of negligible families is negligible. *)
Lemma negligible_bigcup (n : nat) (E : nat -> forall d, set 'rV[RR]_(d * d)) :
  (forall k, (k <= n)%N -> negligible (fun d => gauss (d * d)) (E k)) ->
  negligible (fun d => gauss (d * d))
    (fun d => \bigcup_(k in [set k | (k <= n)%N]) E k d).
Proof.
elim: n => [|n IH] h.
  apply: negligibleW (h 0%N (leqnn 0)) _; exists 0%N => d _ a [k /= k0 Ea].
  by move: k0; rewrite leqn0 => /eqP k0; rewrite k0 in Ea.
have h1 := IH (fun k kn => h k (leqW kn)).
apply: negligibleW (negligibleU h1 (h n.+1 (leqnn _))) _.
exists 0%N => d _ a [k /= kn Ea].
have [kn'|kn'] := leqP k n; first by left; exists k.
right; have -> : n.+1 = k by apply/eqP; rewrite eqn_leq kn kn'.
exact: Ea.
Qed.

(* The infima of two pointwise close families are close. *)
Lemma inf_close (I : set R) (F G : R -> R) (delta : R) : I !=set0 ->
  (forall t, I t -> 0 <= F t) -> (forall t, I t -> 0 <= G t) ->
  (forall t, I t -> `|F t - G t| <= delta) ->
  `|inf [set F t | t in I] - inf [set G t | t in I]| <= delta.
Proof.
move=> [t0 It0] F0 G0 FG.
have lbF : has_lbound [set F t | t in I] by exists 0 => _ [t It <-]; exact: F0.
have lbG : has_lbound [set G t | t in I] by exists 0 => _ [t It <-]; exact: G0.
have h1 : inf [set F t | t in I] - delta <= inf [set G t | t in I].
  apply: lb_le_inf; first by exists (G t0), t0.
  move=> _ [t It <-]; have := FG t It; rewrite ler_distl => /andP[_ h].
  have : inf [set F t | t in I] <= F t by apply: ge_inf => //; exists t.
  by lra.
have h2 : inf [set G t | t in I] - delta <= inf [set F t | t in I].
  apply: lb_le_inf; first by exists (F t0), t0.
  move=> _ [t It <-]; have := FG t It; rewrite ler_distl => /andP[h _].
  have : inf [set G t | t in I] <= G t by apply: ge_inf => //; exists t.
  by lra.
by rewrite ler_distl; apply/andP; split; lra.
Qed.

(* The mean over the eigenvalues of W and the integral against the
   semicircle law are Lipschitz in the shift m. *)
Lemma goe_stat_shift_lipschitz d (a : 'rV[RR]_(d * d)) (C B Bm m m' t : R) :
  (0 < d)%N -> 1 <= C -> opnorm (goe_mx a) <= 3 -> 0 <= t <= B ->
  `|m| <= Bm -> `|m'| <= Bm ->
  `|goe_stat (shift_fun C m t) a - goe_stat (shift_fun C m' t) a| <=
  2 * ((1 + C) * B + 2 * (3 + Bm)) * (1 + C) * `|m - m'|.
Proof.
move=> d0 C1 ho ht hm hm'.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
rewrite /goe_stat -mulrBl -sumrB normrM [`|_^-1|]ger0_norm ?invr_ge0 ?ler0n //.
rewrite ler_pdivrMr //.
apply: le_trans (ler_norm_sum _ _ _) _.
have -> : 2 * ((1 + C) * B + 2 * (3 + Bm)) * (1 + C) * `|m - m'| * d%:R =
    \sum_(i < d) 2 * ((1 + C) * B + 2 * (3 + Bm)) * (1 + C) * `|m - m'|.
  by rewrite sumr_const card_ord mulr_natr.
apply: ler_sum => i _.
have hx : -3 <= spec (goe_mx a) 0 i <= 3.
  rewrite -ler_norml.
  exact: le_trans (spec_le_opnorm i (goe_mx_symmetric a)) ho.
have := shift_fun_lipschitz C1 ht ht hx hx hm hm'.
by rewrite !subrr normr0 !add0r.
Qed.

Lemma shift_integral_lipschitz (C B Bm m m' t : R) : 1 <= C -> 0 <= t <= B ->
  `|m| <= Bm -> `|m'| <= Bm ->
  `|\int[semicircle_prob 2]_x shift_fun C m t x -
    \int[semicircle_prob 2]_x shift_fun C m' t x| <=
  2 * ((1 + C) * B + 2 * (3 + Bm)) * (1 + C) * `|m - m'|.
Proof.
move=> C1 ht hm hm'.
apply: semicircle_near;
  [exact: shift_fun_continuous|exact: shift_fun_continuous|].
move=> x hx; have := shift_fun_lipschitz C1 ht ht hx hx hm hm'.
by rewrite !subrr normr0 !add0r.
Qed.

Section uniform_shift.
Variables (C c M : R).
Hypotheses (C1 : 1 <= C) (M0 : 0 < M).

Local Notation B := (3 + `|c| * M).
Local Notation L := (2 * ((1 + C) * (3 + `|c| * M) + 2 * (3 + `|c| * M)) *
  (1 + C)).

(* Outside a negligible event, on opnorm W <= 3, the infimum over t in
   [0, B] of the mean of shift_fun C (c mu) t over the eigenvalues of W is
   within eta of its limit, uniformly in mu in [0, M]: wigner_uniform_inf
   at the points of a finite net, and the Lipschitz bounds in mu. *)
Lemma shift_inf_unif (eta : R) : 0 < eta ->
  negligible (fun d => gauss (d * d))
    (fun d => [set a : 'rV[RR]_(d * d) | opnorm (goe_mx a) <= 3 /\
      exists2 mu : R, 0 <= mu <= M &
        eta <= `|inf [set goe_stat (shift_fun C (c * mu)%R t) a |
                      t in [set t : R | 0 <= t <= B]] -
                 inf [set \int[semicircle_prob 2]_x
                        shift_fun C (c * mu)%R t x |
                      t in [set t : R | 0 <= t <= B]]|]).
Proof.
move=> e0.
have cM0 : 0 <= `|c| * M by rewrite mulr_ge0 ?normr_ge0 // ltW.
have B0 : 0 <= B by rewrite addr_ge0 ?ler0n.
have C0 : 0 <= 1 + C by apply: addr_ge0 => //; apply: le_trans C1.
have L0 : 0 <= L.
  apply: mulr_ge0 => //; apply: mulr_ge0; first exact: ler0n.
  by apply: addr_ge0; [exact: mulr_ge0|apply: mulr_ge0; [exact: ler0n|
    exact: addr_ge0]].
have e3 : 0 < eta / 3 by rewrite divr_gt0.
have hx0 := archimedean.Num.Theory.truncnS_gt (L * `|c| * M / (eta / 3)).
move: (archimedean.Num.truncn (L * `|c| * M / (eta / 3))).+1 hx0 => N hx0.
have NR : 0 < N%:R :> RR.
  apply: le_lt_trans hx0; rewrite divr_ge0 ?(ltW e3) //.
  apply: mulr_ge0; last exact: ltW.
  by apply: mulr_ge0 => //; exact: normr_ge0.
have hN : L * `|c| * M / N%:R <= eta / 3.
  rewrite ltr_pdivrMr // in hx0.
  by rewrite ler_pdivrMr //; apply: ltW; rewrite [_ * N%:R]mulrC.
pose mu k := k%:R * M / N%:R.
have mu0 k : (k <= N)%N -> 0 <= mu k <= M.
  move=> kN; rewrite /mu divr_ge0 ?mulr_ge0 ?ler0n ?(ltW M0) //=.
  rewrite ler_pdivrMr // mulrC ler_wpM2l ?(ltW M0) //.
  by rewrite ler_nat.
have cmu (x : R) : 0 <= x <= M -> `|c * x| <= `|c| * M.
  move=> /andP[x0 xM]; rewrite normrM [`|x|]ger0_norm //.
  by rewrite ler_wpM2l ?normr_ge0.
pose F k d := [set a : 'rV[RR]_(d * d) | eta / 3 <=
  `|inf [set goe_stat (shift_fun C (c * mu k)%R t) a |
        t in [set t : R | 0 <= t <= B]] -
    inf [set \int[semicircle_prob 2]_x shift_fun C (c * mu k)%R t x |
        t in [set t : R | 0 <= t <= B]]|].
have hF k : (k <= N)%N -> negligible (fun d => gauss (d * d)) (F k).
  move=> kN eps p0.
  have m0 : 0 < Num.min (eta / 3) eps by rewrite lt_min e3 p0.
  have hm := cmu _ (mu0 k kN).
  have hx (t x y : R) : 0 <= t <= B -> -3 <= x <= 3 -> -3 <= y <= 3 ->
      `|shift_fun C (c * mu k)%R t x - shift_fun C (c * mu k)%R t y| <=
      L * `|x - y|.
    move=> ht hx hy.
    have := shift_fun_lipschitz C1 ht ht hx hy hm hm.
    by rewrite !subrr normr0 add0r addr0.
  have ht (t s x : R) : 0 <= t <= B -> 0 <= s <= B -> -3 <= x <= 3 ->
      `|shift_fun C (c * mu k)%R t x - shift_fun C (c * mu k)%R s x| <=
      L * `|t - s|.
    move=> h1 h2 h3.
    have := shift_fun_lipschitz C1 h1 h2 h3 h3 hm hm.
    by rewrite !subrr normr0 !addr0.
  have [D hD] := @wigner_uniform_inf RR (shift_fun C (c * mu k)%R) L 0 B B0
    (fun t => @shift_fun_continuous C (c * mu k)%R t) hx ht _ m0.
  exists D => d dD; have [A [mA PA hA]] := hD d dD.
  exists A; split => //.
    by apply: le_trans PA _; rewrite lee_fin ge_min lexx orbT.
  move=> a /= h; apply: hA => /=; apply: le_trans h.
  by rewrite ge_min lexx.
apply: negligibleW (negligible_bigcup hF) _.
exists 1%N => d d1 a /= [ho [m hm hge]].
have mN0 : 0 <= m * N%:R / M.
  by case/andP: hm => m0 _; rewrite divr_ge0 ?mulr_ge0 ?ler0n // ltW.
have /andP[k1 k2] := archimedean.Num.Theory.truncn_itv mN0.
move: (archimedean.Num.truncn (m * N%:R / M)) k1 k2 => k k1 k2.
have kN : (k <= N)%N.
  rewrite -(ler_nat RR); apply: le_trans k1 _.
  case/andP: hm => _ mM.
  by rewrite ler_pdivrMr // mulrC ler_wpM2l ?ler0n.
have hk : `|m - mu k| <= M / N%:R.
  have -> : m - mu k = (m * N%:R / M - k%:R) * (M / N%:R).
    rewrite /mu; have Mn : M != 0 by rewrite gt_eqF.
    have Nn : N%:R != 0 :> RR by rewrite gt_eqF.
    by field.
  rewrite normrM [`|M / _|]ger0_norm ?divr_ge0 ?ler0n ?(ltW M0) //.
  rewrite -[X in _ <= X]mul1r ler_wpM2r ?divr_ge0 ?ler0n ?(ltW M0) //.
  rewrite ger0_norm ?subr_ge0 //.
  have : (k.+1%:R : RR) = k%:R + 1 by rewrite -addn1 natrD.
  by lra.
have [Fk|nFk] := pselect (F k d a); first by exists k.
exfalso; move: nFk; rewrite /F /= => /negP; rewrite -ltNge => hlt.
have hmk := mu0 k kN.
have hcm := cmu _ hm; have hck := cmu _ hmk.
have lip : L * `|c * m - c * mu k| <= eta / 3.
  rewrite -mulrBr normrM mulrA; apply: le_trans hN.
  rewrite -mulrA -[X in _ <= X]mulrA [X in _ <= X]mulrA.
  have := ler_wpM2l (mulr_ge0 L0 (normr_ge0 c)) hk.
  by rewrite !mulrA.
have h1 : `|inf [set goe_stat (shift_fun C (c * m)%R t) a |
      t in [set t : R | 0 <= t <= B]] -
    inf [set goe_stat (shift_fun C (c * mu k)%R t) a |
      t in [set t : R | 0 <= t <= B]]| <= eta / 3.
  apply: le_trans lip; apply: inf_close.
  - by exists 0; rewrite /= lexx B0.
  - move=> t _; rewrite /goe_stat divr_ge0 ?ler0n //.
    by apply: sumr_ge0 => i _; rewrite /shift_fun exprn_even_ge0.
  - move=> t _; rewrite /goe_stat divr_ge0 ?ler0n //.
    by apply: sumr_ge0 => i _; rewrite /shift_fun exprn_even_ge0.
  - by move=> t ht; exact: goe_stat_shift_lipschitz.
have h3 : `|inf [set \int[semicircle_prob 2]_x shift_fun C (c * mu k)%R t x |
      t in [set t : R | 0 <= t <= B]] -
    inf [set \int[semicircle_prob 2]_x shift_fun C (c * m)%R t x |
      t in [set t : R | 0 <= t <= B]]| <= eta / 3.
  apply: le_trans lip; rewrite distrC; apply: inf_close.
  - by exists 0; rewrite /= lexx B0.
  - move=> t _; apply: Rintegral_ge0 => x _.
    by rewrite /shift_fun exprn_even_ge0.
  - move=> t _; apply: Rintegral_ge0 => x _.
    by rewrite /shift_fun exprn_even_ge0.
  - by move=> t ht; exact: shift_integral_lipschitz.
move: hge h1 hlt h3.
set p := inf [set goe_stat (shift_fun C (c * m)%R t) a |
  t in [set t : R | 0 <= t <= B]].
set q := inf [set goe_stat (shift_fun C (c * mu k)%R t) a |
  t in [set t : R | 0 <= t <= B]].
set u := inf [set \int[semicircle_prob 2]_x shift_fun C (c * mu k)%R t x |
  t in [set t : R | 0 <= t <= B]].
set v := inf [set \int[semicircle_prob 2]_x shift_fun C (c * m)%R t x |
  t in [set t : R | 0 <= t <= B]].
clearbody p q u v => hge h1 hlt h3.
have t1 := ler_distD q p v; have t2 := ler_distD u q v.
by lra.
Qed.

End uniform_shift.

(* 6. M4: the limit of (1/d) sup_K Phi-bar_H. *)

(* The normalized dual expression: (P(H - c mu I) + c d mu^2) / d. *)
Lemma quad_shift_norm (C : R) d (H : 'M[R]_d) (c mu : R) : (0 < d)%N ->
  (mxdot (H - (c * mu)%:M) (H - (c * mu)%:M) - cond_dist C (H - (c * mu)%:M) +
     c * d%:R * mu ^+ 2) / d%:R =
  mxdot H H / d%:R - 2 * c * mu * (\tr H / d%:R) + c * (1 + c) * mu ^+ 2 -
  cond_dist C (H - (c * mu)%:M) / d%:R.
Proof.
move=> d0; have dn : d%:R != 0 :> RR by rewrite pnatr_eq0 -lt0n.
rewrite mxdotBl !mxdotBr (mxdotC H ((c * mu)%:M)) !scalar_mx_dot mxtrace_scalar.
by rewrite -mulr_natr; field.
Qed.

(* The two squeezes of the duality, for c <= 0 and for c >= 0. *)
Lemma squeeze_max (V Q0 qs al e : R) : Q0 <= V -> qs <= al ->
  `|Q0 - al| <= e -> `|V - qs| <= e -> `|V - al| <= e.
Proof.
move=> h1 h2; rewrite !ler_norml => /andP[h3 h4] /andP[h5 h6].
by apply/andP; split; lra.
Qed.

Lemma squeeze_min (V Q0 qs al e : R) : V <= Q0 -> al <= qs ->
  `|Q0 - al| <= e -> `|V - qs| <= e -> `|V - al| <= e.
Proof.
move=> h1 h2; rewrite !ler_norml => /andP[h3 h4] /andP[h5 h6].
by apply/andP; split; lra.
Qed.

Section kappa_spectral.
Variables (kappa C : R).
Hypotheses (k1 : 1 < kappa) (C1 : 1 < C).

Local Notation c := (cone_shift kappa).
Local Notation a0 := (Num.min 1 (1 + cone_shift kappa)).

Let C1' : 1 <= C := ltW C1.
Let C0 : 0 <= C := ltW (lt_trans ltr01 C1).

(* The window of mu = tr X / d: if |H|_F^2 / d <= 1, then
   0 <= tr X / d <= 1 / a0. *)
Lemma kappa_argmax_trace_window d (H : 'M[R]_d) : (0 < d)%N ->
  mxdot H H / d%:R <= 1 ->
  0 <= \tr (kappa_argmax kappa C H) / d%:R <= a0^-1.
Proof.
move=> d0 hH.
have a0p := a0_gt0 k1.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have sd : 0 < Num.sqrt (d%:R : RR) by rewrite sqrtr_gt0.
apply/andP; split.
  by rewrite divr_ge0 ?ler0n // kappa_argmax_tr_ge0.
have h1 := trace_le_diag (kappa_argmax kappa C H) d0.
have h2 := frobenius_diag_le (kappa_argmax kappa C H).
have h3 := kappa_argmax_norm k1 C0 H.
have h4 : frobenius H / Num.sqrt d%:R <= 1.
  rewrite -(ler_pXn2r (n := 2)) ?nnegrE ?divr_ge0 ?frobenius_ge0 ?sqrtr_ge0 //.
  by rewrite expr1n expr_div_n frobenius_sqr sqr_sqrtr ?ler0n.
apply: le_trans (ler_norm _) _.
rewrite normrM [`|_^-1|]ger0_norm ?invr_ge0 ?ler0n //.
apply: le_trans h1 _.
apply: (@le_trans _ _ (frobenius (kappa_argmax kappa C H) / Num.sqrt d%:R)).
  by apply: ler_wpM2r; [rewrite invr_ge0 sqrtr_ge0|exact: h2].
apply: (@le_trans _ _ (frobenius H / Num.sqrt d%:R / a0)).
  rewrite mulrAC; apply: ler_wpM2r; first by rewrite invr_ge0 sqrtr_ge0.
  exact: h3.
rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r => //.
by rewrite invr_ge0 ltW.
Qed.

(* Interface I2 at mu in [0, 1 / a0]: condition_kappa_dual C kappa mu is
   1/2 + c (1 + c) mu^2 minus the infimum over t in [0, B] of the integral
   of shift_fun C (c mu) t against the semicircle law of radius 2. *)
Lemma kappa_dual_window (mu : R) : 0 <= mu <= a0^-1 ->
  condition_kappa_dual C kappa mu =
  2^-1 + c * (1 + c) * mu ^+ 2 -
  inf [set \int[semicircle_prob 2]_x shift_fun C (c * mu)%R t x |
       t in [set t : R | 0 <= t <= 3 + `|c| * a0^-1]].
Proof.
move=> /andP[m0 mM].
have hB : Num.sqrt 2 + `|c * mu| <= 3 + `|c| * a0^-1.
  apply: lerD.
    have h : Num.sqrt 2 < 3 / 2 :> RR.
      rewrite -(@ltr_pXn2r _ 2) ?nnegrE ?sqrtr_ge0 ?divr_ge0 // sqr_sqrtr //.
      by rewrite expr_div_n; lra.
    by lra.
  by rewrite normrM [`|mu|]ger0_norm // ler_wpM2l ?normr_ge0.
rewrite /condition_kappa_dual -cone_shiftE; congr (_ - _).
rewrite -(clip_shift_window C1' hB); congr inf.
by apply: eq_imagel => t /andP[t0 _]; rewrite (shift_fun_integral _ C1' t0).
Qed.

(* The deterministic squeeze: on the good event, (1/d) sup_K Phi-bar_H is
   within 3 del of alpha(C, kappa). The duality of section 3 at
   mu = tr X / d, which lies in [0, 1 / a0] (kappa_argmax_trace_window),
   and at the optimizer mu0 of interface I2 (condition_kappa_dual_opt),
   with the inequalities condition_kappa_dual_le and _ge of item S2. *)
Lemma kappa_quad_close d (a : 'rV[RR]_(d * d)) (del : R) : (0 < d)%N ->
  opnorm (goe_mx a) <= 3 ->
  `|mxdot (goe_half a) (goe_half a) / d%:R - 2^-1| <= Num.min 2^-1 del ->
  `|\tr (goe_half a) / d%:R| <= del / (2 * `|c| * a0^-1 + 1) ->
  (forall mu, 0 <= mu <= a0^-1 ->
     `|inf [set goe_stat (shift_fun C (c * mu)%R t) a |
            t in [set t : R | 0 <= t <= 3 + `|c| * a0^-1]] -
       inf [set \int[semicircle_prob 2]_x shift_fun C (c * mu)%R t x |
            t in [set t : R | 0 <= t <= 3 + `|c| * a0^-1]]| <= del) ->
  `|sup [set trace_quad c (goe_half a) S | S in cond_cone C] / d%:R -
    condition_kappa_alpha C kappa| <= 3 * del.
Proof.
move=> d0 ho hH htr hD.
have a0p := a0_gt0 k1.
have M0 : 0 < a0^-1 by rewrite invr_gt0.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have Hs := goe_half_symmetric a.
have den : 0 < 2 * `|c| * a0^-1 + 1.
  by rewrite ltr_pwDr // mulr_ge0 ?mulr_ge0 ?ler0n ?normr_ge0 // ltW.
have hdel : `|mxdot (goe_half a) (goe_half a) / d%:R - 2^-1| <= del.
  by apply: le_trans hH _; rewrite ge_min lexx orbT.
have hQ mu : 0 <= mu <= a0^-1 ->
    `|(mxdot (goe_half a - (c * mu)%:M) (goe_half a - (c * mu)%:M) -
       cond_dist C (goe_half a - (c * mu)%:M) + c * d%:R * mu ^+ 2) / d%:R -
      condition_kappa_dual C kappa mu| <= 3 * del.
  move=> hmu; have /andP[m0 mM] := hmu.
  have hBm : 3 + `|c * mu| <= 3 + `|c| * a0^-1.
    by rewrite lerD2l normrM [`|mu|]ger0_norm // ler_wpM2l ?normr_ge0.
  rewrite quad_shift_norm // (kappa_dual_window hmu).
  rewrite (cond_dist_shift_goe d0 C1' ho hBm).
  have h1 := hD mu hmu.
  have h2 : `|2 * c * mu * (\tr (goe_half a) / d%:R)| <= del.
    have hc' (x : R) : `|2 * x * mu| <= 2 * `|x| * a0^-1.
      rewrite normrM normrM ger0_norm ?ler0n // [`|mu|]ger0_norm //.
      by rewrite -!mulrA ler_wpM2l ?ler0n // ler_wpM2l ?normr_ge0.
    have hc := hc' (cone_shift kappa).
    rewrite ler_pdivlMr // in htr.
    rewrite normrM.
    have := normr_ge0 (2 * c * mu); have := normr_ge0 (\tr (goe_half a) / d%:R).
    by nra.
  move: h1 h2 hdel; rewrite !ler_norml => /andP[h1 h1'] /andP[h2 h2']
    /andP[h3 h3'].
  by apply/andP; split; lra.
rewrite (kappa_argmax_quad_sup k1 C0 (goe_half a)).
have hH1 : mxdot (goe_half a) (goe_half a) / d%:R <= 1.
  move: hH; rewrite ler_norml => /andP[_ h].
  have : Num.min 2^-1 del <= 2^-1 by rewrite ge_min lexx.
  by lra.
have hw := kappa_argmax_trace_window d0 hH1.
have heq := kappa_dual_eq C1' d0 k1 C0 Hs.
have [mu0 [m00 m01 hq0]] := condition_kappa_dual_opt C kappa C1 k1.
have hmu0 : 0 <= mu0 <= a0^-1.
  rewrite m00 /=; apply: le_trans m01 _.
  rewrite -cone_shiftD1 mul1r invfM ler_piMl ?invr_ge0 ?(ltW a0p) //.
  rewrite invf_le1 ?sqrtr_gt0 ?ltr0n //.
  exact: sqrt2_ge1.
have hQ0 := hQ mu0 hmu0; have hQs := hQ _ hw.
rewrite hq0 in hQ0.
rewrite heq.
have dinv : 0 <= d%:R^-1 :> RR by rewrite invr_ge0 ltW.
have [k3|k3] := leP kappa 3.
  have c0 : c <= 0.
    by rewrite cone_shiftE pmulr_lle0 ?invr_gt0 ?ltr0n // subr_le0.
  have hle := ler_wpM2r dinv (kappa_dual_le C1' d0 k1 C0 mu0 Hs c0).
  rewrite heq in hle.
  have hal := condition_kappa_dual_le C kappa C1 k1 k3
    (\tr (kappa_argmax kappa C (goe_half a)) / d%:R)%R.
  exact: squeeze_max hle hal hQ0 hQs.
have c0 : 0 <= c.
  by rewrite cone_shiftE pmulr_lge0 ?invr_gt0 ?ltr0n // subr_ge0 ltW.
have hge := ler_wpM2r dinv (kappa_dual_ge d0 k1 C0 mu0 Hs c0).
rewrite heq in hge.
have hal := condition_kappa_dual_ge C kappa C1 k1 (ltW k3)
  (\tr (kappa_argmax kappa C (goe_half a)) / d%:R)%R.
exact: squeeze_min hge hal hQ0 hQs.
Qed.

(* Item M4: (1/d) sup_K Phi-bar_H -> alpha(C, kappa) in probability. *)
Theorem kappa_quad_sup_cvg :
  cvg_prob (fun d => gauss (d * d))
    (fun d a => sup [set trace_quad c (goe_half a) S | S in cond_cone C] /
       d%:R)
    (condition_kappa_alpha C kappa).
Proof.
move=> eta e0.
have a0p := a0_gt0 k1.
have M0 : 0 < a0^-1 by rewrite invr_gt0.
have del0 : 0 < eta / 6 by rewrite divr_gt0.
have m0 : 0 < Num.min 2^-1 (eta / 6).
  by rewrite lt_min del0 andbT invr_gt0 ltr0n.
have den : 0 < 2 * `|c| * a0^-1 + 1.
  by rewrite ltr_pwDr // mulr_ge0 ?mulr_ge0 ?ler0n ?normr_ge0 // ltW.
have q0 : 0 < eta / 6 / (2 * `|c| * a0^-1 + 1) by rewrite divr_gt0.
have s3 : 2 * Num.sqrt 2 < 3 :> R.
  have s2 : Num.sqrt 2 < 3 / 2 :> R.
    rewrite -(@ltr_pXn2r _ 2) ?nnegrE ?sqrtr_ge0 ?divr_ge0 // sqr_sqrtr //.
    by rewrite expr_div_n; lra.
  by lra.
have n1 : negligible (fun d => gauss (d * d))
    (fun d => [set a : 'rV[RR]_(d * d) | 3 <= opnorm (goe_mx a)]).
  apply: negligible_measurable => [d|eps p0].
    exact: measurable_goe_opnorm.
  have [D hD] := goe_opnorm_tail_small s3 p0.
  by exists D => d dD; exact: hD.
have n2 := goe_half_sqnorm_cvg m0.
have n3 := goe_half_trace_cvg q0.
have n4 := shift_inf_unif (cone_shift kappa) C1' M0 del0.
apply: negligibleW (negligibleU (negligibleU (negligibleU n1 n2) n3) n4) _.
exists 1%N => d d1 a /= hge.
have [h1|h1] := leP 3 (opnorm (goe_mx a)); first by left; left; left.
have [h2|h2] := leP (Num.min 2^-1 (eta / 6))
  `|mxdot (goe_half a) (goe_half a) / d%:R - 2^-1|.
  by left; left; right.
have [h3|h3] := leP (eta / 6 / (2 * `|c| * a0^-1 + 1))
  `|\tr (goe_half a) / d%:R - 0|.
  by left; right.
right; split; first exact: ltW.
apply: contrapT => hn.
have hD mu : 0 <= mu <= a0^-1 ->
    `|inf [set goe_stat (shift_fun C (c * mu)%R t) a |
           t in [set t : R | 0 <= t <= 3 + `|c| * a0^-1]] -
      inf [set \int[semicircle_prob 2]_x shift_fun C (c * mu)%R t x |
           t in [set t : R | 0 <= t <= 3 + `|c| * a0^-1]]| <= eta / 6.
  move=> hmu; rewrite leNgt; apply/negP => hlt; apply: hn.
  by exists mu => //; exact: ltW.
rewrite subr0 in h3.
have := kappa_quad_close d1 (ltW h1) (ltW h2) (ltW h3) hD.
by move: hge; lra.
Qed.

End kappa_spectral.

(* 7. M5: the support function of T K_C. *)

(* For a closed convex cone K of row vectors, the maximum over K of
   2 <z, y> - |y|^2 is |Pi_K(z)|^2, attained at Pi_K(z). *)
Lemma cone_proj_value N (K : set 'rV[RR]_N) (z : 'rV[RR]_N) :
  closed K -> K 0 ->
  (forall x y (t : RR), K x -> K y -> 0 <= t <= 1 -> K (x + t *: (y - x))) ->
  (forall y (k : RR), K y -> 0 <= k -> K (k *: y)) ->
  [/\ K (proj K z),
      forall y, K y -> 2 * mxdot z y - mxdot y y <=
        mxdot (proj K z) (proj K z) &
      2 * mxdot z (proj K z) - mxdot (proj K z) (proj K z) =
      mxdot (proj K z) (proj K z)].
Proof.
move=> Kc K0 Kcvx Kcone.
have Kn : K !=set0 by exists 0.
have [Kp hp] := projP Kc Kn Kcvx z.
move: (proj K z) Kp hp => p Kp hp.
have h0 := hp 0 K0.
have h2 := hp (2 *: p) (Kcone p 2 Kp (ler0n _ 2)).
rewrite sub0r mxdotNr oppr_le0 in h0.
have e2 : 2 *: p - p = p by rewrite scaler_nat mulr2n addrK.
rewrite e2 in h2.
have e : mxdot z p = mxdot p p.
  have : mxdot (z - p) p = 0 by apply/eqP; rewrite eq_le h2 h0.
  by rewrite mxdotBl => /eqP; rewrite subr_eq0 => /eqP.
split => //.
  move=> y Ky; have := hp y Ky; have := mxdot_ge0 (y - p).
  rewrite !mxdotBl !mxdotBr ?(mxdotC y p) ?(mxdotC p z) e.
  by lra.
by rewrite e; lra.
Qed.

Section kappa_support.
Variables (kappa C : R).
Hypotheses (k1 : 1 < kappa) (C1 : 1 < C).

Local Notation c := (cone_shift kappa).

Let C0 : 0 <= C := ltW (lt_trans ltr01 C1).

(* Phi_H is quadratic: Phi_{k H}(k S) = k^2 Phi_H(S). *)
Lemma kappa_objZ d (k : R) (H S : 'M[R]_d) :
  kappa_obj kappa (k *: H) (k *: S) = k ^+ 2 * kappa_obj kappa H S.
Proof.
rewrite /kappa_obj cone_mapZ diag_partZ !mxdotZl !mxdotZr.
by rewrite expr2; ring.
Qed.

(* 2 <A, T S> - |T S|_F^2 = Phi_G(S) with G the symmetric part of A, in
   the coordinates of mxvec. *)
Lemma kappa_obj_vec d (a : 'rV[RR]_(d * d)) (S : 'M[R]_d) :
  S \is symmetricmx ->
  2 * mxdot a (mxvec (cone_map kappa S)) -
    mxdot (mxvec (cone_map kappa S)) (mxvec (cone_map kappa S)) =
  kappa_obj kappa (goe_part (vec_mx a)) S.
Proof.
move=> Ss.
have TS : paper_main_symmetric (cone_map kappa S).
  by apply: cone_map_sym; apply/paper_symmetricP.
have e1 : mxdot a (mxvec (cone_map kappa S)) =
    mxdot (goe_part (vec_mx a)) (cone_map kappa S).
  rewrite -[in LHS](vec_mxK a) -mxdot_vec_mx !mxvecK.
  by rewrite -!pairing_mxdot pairing_goe_part.
have e2 : mxdot (mxvec (cone_map kappa S)) (mxvec (cone_map kappa S)) =
    mxdot S S + c * mxdot (diag_part S) (diag_part S).
  rewrite -mxdot_vec_mx !mxvecK -!pairing_mxdot pairing_cone_map ?(ltW k1) //.
  by rewrite !pairing_mxdot mxdot_diag_parts.
by rewrite e1 e2 /kappa_obj; ring.
Qed.

(* sigma_{C,kappa}(A)^2 = |Pi_{T K_C}(A)|_F^2 = d sup_K Phi_H, with
   A = vec_mx a and H = goe_half a. *)
Lemma kcond_support_sqr d (a : 'rV[RR]_(d * d)) : (0 < d)%N ->
  kcond_support kappa C (vec_mx a : 'M[RR]_d) ^+ 2 =
  d%:R * sup [set kappa_obj kappa (goe_half a) S | S in cond_cone C].
Proof.
move=> d0.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have sd : 0 < Num.sqrt (d%:R : RR) by rewrite sqrtr_gt0.
have sdn : Num.sqrt (d%:R : RR) != 0 by rewrite gt_eqF.
have sd2 : Num.sqrt (d%:R : RR) ^+ 2 = d%:R by rewrite sqr_sqrtr ?ler0n.
rewrite (kcond_support_proj kappa C d a k1 C0) frobenius_sqr.
have [Kp hmax heq] := cone_proj_value a (kcond_cone_vec_closed kappa C d k1 C0)
  (kcond_cone_vec0 kappa C d) (@kcond_cone_vec_convex kappa C d)
  (@kcond_cone_vecZ kappa C d).
move: (proj (kcond_cone_vec kappa C d) a) Kp hmax heq => p Kp hmax heq.
have hG S : cond_cone C S ->
    d%:R * kappa_obj kappa (goe_half a) S =
    2 * mxdot a (mxvec (cone_map kappa (Num.sqrt d%:R *: S))) -
    mxdot (mxvec (cone_map kappa (Num.sqrt d%:R *: S)))
          (mxvec (cone_map kappa (Num.sqrt d%:R *: S))).
  move=> [Ss _].
  have Ss' : Num.sqrt d%:R *: S \is symmetricmx.
    by apply/symmetricmxP; rewrite linearZ /=; move/symmetricmxP: Ss => ->.
  by rewrite (kappa_obj_vec a Ss') goe_part_half // kappa_objZ sd2.
have ub : ubound [set kappa_obj kappa (goe_half a) S | S in cond_cone C]
    (mxdot p p / d%:R).
  move=> _ [S KS <-]; rewrite ler_pdivlMr // mulrC (hG S KS).
  apply: hmax; exists (Num.sqrt d%:R *: S) => //.
  exact: cond_coneZ (ltW sd) KS.
have [S0 KS0 pS0] := Kp.
have K1 : cond_cone C ((Num.sqrt d%:R)^-1 *: S0).
  by apply: cond_coneZ => //; rewrite invr_ge0 ltW.
have att : kappa_obj kappa (goe_half a) ((Num.sqrt d%:R)^-1 *: S0) =
    mxdot p p / d%:R.
  apply: (mulfI (_ : d%:R != 0)); first by rewrite gt_eqF.
  rewrite (hG _ K1) scalerA mulfV // scale1r pS0 heq.
  by rewrite mulrC divfK // gt_eqF.
have -> : sup [set kappa_obj kappa (goe_half a) S | S in cond_cone C] =
    mxdot p p / d%:R.
  apply/eqP; rewrite eq_le; apply/andP; split.
    by apply: ge_sup ub; exists (mxdot p p / d%:R), ((Num.sqrt d%:R)^-1 *: S0).
  apply: sup_upper_bound; last by exists ((Num.sqrt d%:R)^-1 *: S0).
  split; first by exists (mxdot p p / d%:R), ((Num.sqrt d%:R)^-1 *: S0).
  by exists (mxdot p p / d%:R).
by rewrite mulrC divfK // gt_eqF.
Qed.

(* Item M5, interface I1: sigma_{C,kappa}(vec_mx a) / d ->
   sqrt alpha(C, kappa) in probability, for kappa > 1 and C > 1. *)
Theorem kcond_support_cvg :
  cvg_prob (fun d => @gauss RR (d * d))
    (fun d a => kcond_support kappa C (vec_mx a : 'M[RR]_d) / d%:R)
    (Num.sqrt (condition_kappa_alpha C kappa)).
Proof.
have h := cvg_probD (kappa_sup_gap_cvg k1 C0) (kappa_quad_sup_cvg k1 C1).
rewrite add0r in h.
have := cvg_prob_sqrt h.
apply: cvg_prob_eq; exists 1%N => d d1 a.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
rewrite -mulrDl subrK.
have k0 := kcond_support_ge0 kappa C d (vec_mx a : 'M[RR]_d).
rewrite -[RHS]ger0_norm ?divr_ge0 ?ler0n // -sqrtr_sqr expr_div_n.
rewrite (kcond_support_sqr a d1) expr2 -mulf_div divff ?mul1r //.
by rewrite gt_eqF.
Qed.

End kappa_support.
