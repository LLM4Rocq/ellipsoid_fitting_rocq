(* The support function of the cone of bounded condition number at a
   Gaussian symmetric matrix, at Stdlib's R: item Q2 of phase 8
   (notes/three-extensions-plan.md, sections 2 (G1, G2) and 5.2).

   Setting. For a of law gauss (d * d), A = vec_mx a and its symmetric part
   H = goe_part A = (A + A^T) / 2 = sqrt (d / 2) W, with W = goe_mx a the
   GOE matrix of random_matrix/goe.v (goe_partE). The empirical law of the
   eigenvalues of W tends to the semicircle law of radius 2 (wigner), so
   the eigenvalues of H / sqrt d = W / sqrt 2 have the limit threshold_law,
   the semicircle law of radius sqrt 2, as for the frozen definitions. For
   C >= 1, cond_support C A is the supremum of <A, Q> over the Q of
   cond_cone C with |Q|_F <= 1 (library/matrix/condition_cone.v); it only
   depends on the symmetric part H (cond_support_sym), and
   cond_support C H ^ 2 = |H|_F^2 - cond_dist C H (cond_support_sqr), with
   cond_dist C H the infimum over t >= 0 of
   cond_energy C t H = sum_i dist(lambda_i(H), [t, C t])^2.

   Main results.
   - cone_fun C t x = (max (t - x / sqrt 2, x / sqrt 2 - C t))_+^2, which
     is dist(x / sqrt 2, [t, C t])^2 for t >= 0 and C >= 1 (cone_funE,
     itv_dist_maxE): continuous in x, Lipschitz in x and in t on
     [-3, 3] x [0, 3] (cone_fun_lipx, cone_fun_lipt), and its integral
     against the semicircle law of radius 2 is clip_energy threshold_law C t
     (cone_fun_integral, from clip_energyE of
     library/probability/variational.v and the change of scale
     ge0_integral_semicircle_scale).
   - The spectrum: cond_dist C H / d^2 = cond_dist C (W / sqrt 2) / d
     (cond_dist_goe_scale, by cond_distZ), and when opnorm W <= 3 this is
     the infimum over t in [0, 3] of goe_stat (cone_fun C t) a, the mean of
     cone_fun C t over the eigenvalues of W (cond_dist_goe_inf, by
     cond_dist_itv, cond_energy_goe and inf_mulr).
   - cond_dist_goe_cvg: cond_dist C H / d^2 converges in probability
     (cvg_prob of Gaussian/InProbability) to the infimum of
     clip_energy threshold_law C t over t in [0, 3]: wigner_uniform_inf of
     random_matrix/wigner.v on that window, and P(opnorm W >= 3) -> 0
     (goe_opnorm_tail_small, since 3 > 2 sqrt 2).
   - goe_sqnorm_half: |H|_F^2 / d^2 -> 1/2 (goe_sqnorm_cvg of
     Gaussian/Limit at zeta = 0). Hence cond_support_goe_cvg_inf:
     cond_support C A / d converges in probability to
     sqrt (1/2 - inf_{t in [0, 3]} clip_energy threshold_law C t), for
     C >= 1.
   - clip_inf_window: the infimum over a window [0, T] that contains a
     point where clip_value is attained is clip_value. *)

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
From GaussianAnalysis Require Import variational gauss goe wigner.
From GaussianAnalysis Require Import semicircle_law gauss_smoothing.
From GaussianAnalysis Require Import condition_cone.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.
From EllipsoidUniversality.Gaussian Require Import InProbability Limit.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

(* 1. The function of the spectrum. *)

Definition cone_fun (C t x : R) : R :=
  Num.max (Num.max (t - x / Num.sqrt 2%:R) (x / Num.sqrt 2%:R - C * t)) 0 ^+ 2.

Lemma sqrt2_ge1 : 1 <= Num.sqrt 2%:R :> RR.
Proof. by rewrite -[X in X <= _]sqrtr1 ler_sqrt ?ler0n // ler1n. Qed.

Lemma itv_dist_le (a b x : R) : itv_dist a b x <= `|a| + `|b| + 2 * `|x|.
Proof.
rewrite /itv_dist.
have h1 : Num.max (a - x) 0 <= `|a| + `|x|.
  rewrite ge_max addr_ge0 ?normr_ge0 // andbT.
  have := ler_norm a; have := ler_norm (- x); rewrite normrN.
  by move=> h h'; lra.
have h2 : Num.max (x - b) 0 <= `|x| + `|b|.
  rewrite ge_max addr_ge0 ?normr_ge0 // andbT.
  have := ler_norm x; have := ler_norm (- b); rewrite normrN.
  by move=> h h'; lra.
by lra.
Qed.

(* For 0 <= t <= C t, the squared distance to [t, C t] is the sum of the
   squared parts below and above. *)
Lemma itv_dist_sqrE (C t x : R) : 1 <= C -> 0 <= t ->
  itv_dist t (C * t) x ^+ 2 =
  Num.max (t - x) 0 ^+ 2 + Num.max (x - C * t) 0 ^+ 2.
Proof.
move=> C1 t0; have tC : t <= C * t by rewrite ler_peMl.
rewrite /itv_dist.
have [xt|tx] := leP x t.
  have -> : Num.max (x - C * t) 0 = 0.
    by apply/max_idPr; rewrite subr_le0 (le_trans xt).
  by rewrite addr0 expr0n /= addr0.
have -> : Num.max (t - x) 0 = 0 by apply/max_idPr; rewrite subr_le0 ltW.
by rewrite add0r expr0n /= add0r.
Qed.

(* For 0 <= t <= C t, the distance to [t, C t] is the positive part of the
   larger of t - x and x - C t. *)
Lemma itv_dist_maxE (C t x : R) : 1 <= C -> 0 <= t ->
  itv_dist t (C * t) x = Num.max (Num.max (t - x) (x - C * t)) 0.
Proof.
move=> C1 t0; have tC : t <= C * t by rewrite ler_peMl.
rewrite /itv_dist.
have [xt|tx] := leP x t.
  have -> : Num.max (x - C * t) 0 = 0.
    by apply/max_idPr; rewrite subr_le0 (le_trans xt).
  rewrite addr0; congr (Num.max _ 0); apply/esym/max_idPl.
  by lra.
have -> : Num.max (t - x) 0 = 0 by apply/max_idPr; rewrite subr_le0 ltW.
rewrite add0r.
have [h|h] := leP (t - x) (x - C * t); first by [].
have h1 : x - C * t <= 0 by apply: le_trans (ltW h) _; rewrite subr_le0 ltW.
have h2 : t - x <= 0 by rewrite subr_le0 ltW.
by rewrite (max_idPr h1) (max_idPr h2).
Qed.

Lemma cone_funE (C t x : R) : 1 <= C -> 0 <= t ->
  cone_fun C t x = itv_dist t (C * t) (x / Num.sqrt 2%:R) ^+ 2.
Proof. by move=> C1 t0; rewrite /cone_fun itv_dist_maxE. Qed.

Lemma cone_fun_continuous (C t : R) : continuous (cone_fun C t).
Proof.
move=> x; rewrite /cone_fun.
apply: (@continuous_comp _ _ _ (fun y : R => Num.max (Num.max
  (t - y / Num.sqrt 2%:R) (y / Num.sqrt 2%:R - C * t)) 0) (fun y => y ^+ 2));
  last exact: exprn_continuous.
apply: continuous_max; last exact: cvg_cst.
apply: continuous_max.
  by apply: cvgB; [exact: cvg_cst | apply: cvgM; [exact: cvg_id|exact: cvg_cst]].
by apply: cvgB; [apply: cvgM; [exact: cvg_id|exact: cvg_cst] | exact: cvg_cst].
Qed.

Lemma cone_fun_bound (C t x : R) : 0 <= C -> 0 <= t <= 3 -> -3 <= x <= 3 ->
  0 <= itv_dist t (C * t) (x / Num.sqrt 2%:R) <= 3 * C + 9.
Proof.
move=> C0 /andP[t0 t3] /andP[x1 x2].
apply/andP; split; first exact: itv_dist_ge0.
apply: le_trans (itv_dist_le _ _ _) _.
have s1 := sqrt2_ge1.
have hx : `|x / Num.sqrt 2%:R| <= 3.
  have sp : 0 < Num.sqrt (2%:R : RR) by apply: lt_le_trans ltr01 s1.
  rewrite normrM normfV (ger0_norm (ltW sp)) ler_pdivrMr //.
  have hx3 : `|x| <= 3 by rewrite ler_norml; apply/andP; split.
  by nra.
rewrite (ger0_norm t0) ger0_norm ?mulr_ge0 //.
have : C * t <= C * 3 by rewrite ler_wpM2l.
by move=> h; lra.
Qed.

Lemma cone_fun_lipx (C t x y : R) : 1 <= C -> 0 <= t <= 3 ->
  -3 <= x <= 3 -> -3 <= y <= 3 ->
  `|cone_fun C t x - cone_fun C t y| <= (1 + C) * (6 * C + 18) * `|x - y|.
Proof.
move=> C1 ht hx hy.
have C0 : 0 <= C by apply: le_trans C1.
have t0 : 0 <= t by case/andP: ht.
have tC : t <= C * t by rewrite ler_peMl.
rewrite !(cone_funE C t _ C1 t0) subr_sqr normrM.
have /andP[u0 u1] := cone_fun_bound C t x C0 ht hx.
have /andP[v0 v1] := cone_fun_bound C t y C0 ht hy.
set u := itv_dist t (C * t) (x / _) in u0 u1 *.
set v := itv_dist t (C * t) (y / _) in v0 v1 *.
have huv : `|u - v| <= `|x - y|.
  apply: le_trans (itv_dist_lipschitz _ _ tC) _.
  have s1 := sqrt2_ge1.
  have sp : 0 < Num.sqrt (2%:R : RR) by apply: lt_le_trans ltr01 s1.
  rewrite -mulrBl normrM normfV (ger0_norm (ltW sp)) ler_pdivrMr //.
  by rewrite ler_peMr ?normr_ge0.
clearbody u v.
have hs : `|u + v| <= 6 * C + 18 by rewrite ger0_norm ?addr_ge0 //; lra.
apply: le_trans (ler_pM (normr_ge0 _) (normr_ge0 _) huv hs) _.
rewrite mulrC; apply: ler_wpM2r; first exact: normr_ge0.
by rewrite ler_peMl ?addr_ge0 ?mulr_ge0 //; lra.
Qed.

Lemma cone_fun_lipt (C t s x : R) : 1 <= C -> 0 <= t <= 3 -> 0 <= s <= 3 ->
  -3 <= x <= 3 ->
  `|cone_fun C t x - cone_fun C s x| <= (1 + C) * (6 * C + 18) * `|t - s|.
Proof.
move=> C1 ht hs hx.
have C0 : 0 <= C by apply: le_trans C1.
have t0 : 0 <= t by case/andP: ht.
have s0 : 0 <= s by case/andP: hs.
rewrite (cone_funE C t x C1 t0) (cone_funE C s x C1 s0) subr_sqr normrM.
have /andP[u0 u1] := cone_fun_bound C t x C0 ht hx.
have /andP[v0 v1] := cone_fun_bound C s x C0 hs hx.
set u := itv_dist t (C * t) _ in u0 u1 *.
set v := itv_dist s (C * s) _ in v0 v1 *.
have huv : `|u - v| <= (1 + C) * `|t - s|.
  apply: le_trans (itv_dist_shift _ _ _ _ _) _.
  by rewrite -mulrBr normrM (ger0_norm C0) mulrDl mul1r.
clearbody u v.
have hs' : `|u + v| <= 6 * C + 18 by rewrite ger0_norm ?addr_ge0 //; lra.
apply: le_trans (ler_pM (normr_ge0 _) (normr_ge0 _) huv hs') _.
by rewrite mulrAC.
Qed.

(* 2. The integral against the semicircle law of radius 2 is the energy of
   the clip for threshold_law, the semicircle law of radius sqrt 2. *)
Lemma cone_fun_integral (C t : R) : 1 <= C -> 0 <= t ->
  \int[semicircle_prob 2]_x cone_fun C t x = clip_energy threshold_law C t.
Proof.
move=> C1 t0.
rewrite -(clip_energyE threshold_law2 threshold_law_sym) /Rintegral.
have s2 : 0 < (Num.sqrt (2%:R : R))^-1 by rewrite invr_gt0 sqrtr_gt0 ltr0n.
pose g (y : R) := Num.max (t - y) 0 ^+ 2 + Num.max (y - C * t) 0 ^+ 2.
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
- congr fine; apply: eq_integral => x _.
  by rewrite (cone_funE C t x C1 t0) (itv_dist_sqrE C t _ C1 t0) mulrC.
Qed.

(* 3. The spectrum of the Gaussian matrix. *)

Lemma goe_part_sym d (A : 'M[R]_d) : goe_part A \is symmetricmx.
Proof.
by apply/symmetricmxP; rewrite /goe_part linearZ /= linearD /= trmxK addrC.
Qed.

Lemma goe_half_sym d (a : 'rV[RR]_(d * d)) :
  (Num.sqrt 2%:R)^-1 *: goe_mx a \is symmetricmx.
Proof.
apply/symmetricmxP; rewrite linearZ /=.
by move/symmetricmxP: (goe_mx_symmetric a) => ->.
Qed.

Lemma cond_dist_goe_scale d (a : 'rV[RR]_(d * d)) (C : R) : (0 < d)%N ->
  cond_dist C (goe_part (vec_mx a)) / d%:R ^+ 2 =
  cond_dist C ((Num.sqrt 2%:R)^-1 *: goe_mx a) / d%:R.
Proof.
move=> d0.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have sd : 0 < Num.sqrt (d%:R : RR) by rewrite sqrtr_gt0.
have -> : goe_part (vec_mx a) =
    Num.sqrt d%:R *: ((Num.sqrt 2%:R)^-1 *: goe_mx a).
  rewrite goe_partE // [RHS]scalerA; congr (_ *: _).
  by rewrite sqrtrM ?ler0n // sqrtrV ?ler0n.
rewrite (cond_distZ C sd (goe_half_sym d a)) sqr_sqrtr ?ler0n //.
have dn : d%:R != 0 :> RR by rewrite gt_eqF.
by field.
Qed.

Lemma cond_energy_goe d (a : 'rV[RR]_(d * d)) (C t : R) : (0 < d)%N ->
  1 <= C -> 0 <= t ->
  cond_energy C t ((Num.sqrt 2%:R)^-1 *: goe_mx a) =
  d%:R * goe_stat (cone_fun C t) a.
Proof.
move=> d0 C1 t0.
have i0 : 0 <= (Num.sqrt (2%:R : RR))^-1 by rewrite invr_ge0 sqrtr_ge0.
rewrite /cond_energy (spec_scale (goe_mx_symmetric a) i0) /goe_stat.
have dn : d%:R != 0 :> RR by rewrite gt_eqF ?ltr0n.
rewrite [RHS]mulrC divfK //; apply: eq_bigr => i _.
by rewrite (cone_funE C t _ C1 t0) mxE [_ * spec _ _ _]mulrC.
Qed.

(* The infimum of a positively scaled family. *)
Lemma inf_mulr (c : R) (I : set R) (f : R -> R) : 0 < c -> I !=set0 ->
  (forall t, I t -> 0 <= f t) ->
  inf [set c * f t | t in I] = c * inf [set f t | t in I].
Proof.
move=> c0 [t0 It0] f0.
have lbf : has_lbound [set f t | t in I].
  by exists 0 => _ [t It <-]; exact: f0.
have lbcf : has_lbound [set c * f t | t in I].
  by exists 0 => _ [t It <-]; rewrite mulr_ge0 ?(ltW c0) ?f0.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite -ler_pdivrMl //; apply: lb_le_inf; first by exists (f t0), t0.
  move=> _ [t It <-]; rewrite ler_pdivrMl //.
  by apply: ge_inf => //; exists t.
apply: lb_le_inf; first by exists (c * f t0), t0.
move=> _ [t It <-]; rewrite ler_pM2l //.
by apply: ge_inf => //; exists t.
Qed.

Lemma cond_dist_goe_inf d (a : 'rV[RR]_(d * d)) (C : R) : (0 < d)%N ->
  1 <= C -> opnorm (goe_mx a) <= 3 ->
  cond_dist C ((Num.sqrt 2%:R)^-1 *: goe_mx a) / d%:R =
  inf [set goe_stat (cone_fun C t) a | t in [set t : R | 0 <= t <= 3]].
Proof.
move=> d0 C1 ho.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have i0 : 0 <= (Num.sqrt (2%:R : RR))^-1 by rewrite invr_ge0 sqrtr_ge0.
have hV i : spec ((Num.sqrt 2%:R)^-1 *: goe_mx a) 0 i <= 3.
  rewrite (spec_scale (goe_mx_symmetric a) i0) mxE.
  have := spec_le_opnorm i (goe_mx_symmetric a).
  have s1 := sqrt2_ge1.
  have i1 : (Num.sqrt (2%:R : RR))^-1 <= 1 by rewrite invf_le1 ?(lt_le_trans ltr01).
  move=> h; apply: le_trans (ler_norm _) _; rewrite normrM ger0_norm //.
  by apply: le_trans (ler_pM i0 (normr_ge0 _) i1 (le_trans h ho)) _; rewrite mul1r.
rewrite (cond_dist_itv C1 (ler0n _ 3) hV).
have -> : [set cond_energy C t ((Num.sqrt 2%:R)^-1 *: goe_mx a) |
    t in [set t : R | 0 <= t <= 3]] =
    [set d%:R * goe_stat (cone_fun C t) a | t in [set t : R | 0 <= t <= 3]].
  by apply: eq_imagel => t /andP[t0 _]; rewrite cond_energy_goe.
rewrite inf_mulr //.
- by exists 0; rewrite /= lexx ler0n.
- move=> t _; rewrite /goe_stat divr_ge0 ?ler0n //.
  by apply: sumr_ge0 => i _; rewrite /cone_fun exprn_even_ge0.
- by rewrite mulrC mulKf // gt_eqF.
Qed.

(* 4. The limit in probability of cond_dist C H / d^2. *)

Lemma measurable_goe_opnorm d (c : R) :
  measurable [set a : 'rV[RR]_(d * d) | c <= opnorm (goe_mx a)].
Proof.
apply: measurable_ge_continuous.
exact: lipschitz_frobenius_continuous (@goe_opnorm_lipschitz RR d).
Qed.

Lemma cond_dist_goe_cvg (C : R) : 1 <= C ->
  cvg_prob (fun d => @gauss RR (d * d))
    (fun d a => cond_dist C (goe_part (vec_mx a)) / d%:R ^+ 2)
    (inf [set clip_energy threshold_law C t | t in [set t : R | 0 <= t <= 3]]).
Proof.
move=> C1 eta e0 eps p0.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have m0 : 0 < Num.min eta (eps / 2) by rewrite lt_min e0 e2.
have [D1 h1] := @wigner_uniform_inf RR (cone_fun C) ((1 + C) * (6 * C + 18)) 0 3
  (ler0n _ 3) (cone_fun_continuous C)
  (fun t x y ht hx hy => cone_fun_lipx C t x y C1 ht hx hy)
  (fun t s x ht hs hx => cone_fun_lipt C t s x C1 ht hs hx) _ m0.
have s3 : 2 * Num.sqrt 2 < 3 :> R.
  have s2 : Num.sqrt 2 < 3 / 2 :> R.
    rewrite -(@ltr_pXn2r _ 2) ?nnegrE ?sqrtr_ge0 ?divr_ge0 // sqr_sqrtr //.
    by rewrite expr_div_n; lra.
  by lra.
have [D2 h2] := goe_opnorm_tail_small s3 e2.
exists (maxn (maxn D1 D2) 1) => d; rewrite !geq_max => /andP[/andP[d1 d2] d0].
have [A [mA PA hA]] := h1 d d1.
pose B := [set a : 'rV[RR]_(d * d) | 3 <= opnorm (goe_mx a)].
have mB : measurable B := measurable_goe_opnorm d 3.
exists (A `|` B); split.
- exact: measurableU.
- apply: le_trans (measureU2 _ mA mB) _.
  apply: le_trans (leeD PA (h2 d d2)) _.
  rewrite -EFinD lee_fin.
  have : Num.min eta (eps / 2) <= eps / 2 by rewrite ge_min lexx orbT.
  by move=> h; lra.
move=> a /= h.
have [hb|hb] := leP 3 (opnorm (goe_mx a)); first by right.
left; apply: hA => /=.
have lim : [set \int[semicircle_prob 2]_x cone_fun C t x |
    t in [set t : R | 0 <= t <= 3]] =
    [set clip_energy threshold_law C t | t in [set t : R | 0 <= t <= 3]].
  by apply: eq_imagel => t /andP[t0 _]; rewrite cone_fun_integral.
rewrite lim -(cond_dist_goe_inf d a C d0 C1 (ltW hb)).
rewrite -(cond_dist_goe_scale d a C d0).
by apply: le_trans h; rewrite ge_min lexx.
Qed.

(* 5. The support function. *)

Lemma goe_sqnorm_half :
  cvg_prob (fun d => @gauss RR (d * d))
    (fun d a => mxdot (goe_part (vec_mx a)) (goe_part (vec_mx a)) / d%:R ^+ 2)
    (2%:R^-1).
Proof.
have k1 : 1 < 2%:R :> RR by rewrite ltr1n.
have := goe_sqnorm_cvg 2%:R 0 k1.
have -> : 2%:R^-1 + 2%:R * 0 ^+ 2 / (2%:R - 1) = 2%:R^-1 :> RR.
  by rewrite expr0n /= mulr0 mul0r addr0.
apply: cvg_prob_eq; exists 0%N => d _ a.
by rewrite /shift_mx !mul0r scale0r addr0 frobenius_sqr.
Qed.

Lemma cond_support_goe_cvg_inf (C : R) : 1 <= C ->
  cvg_prob (fun d => @gauss RR (d * d))
    (fun d a => cond_support C (vec_mx a : 'M[RR]_d) / d%:R)
    (Num.sqrt (2%:R^-1 -
       inf [set clip_energy threshold_law C t | t in [set t : R | 0 <= t <= 3]])).
Proof.
move=> C1.
have C0 : 0 <= C by apply: le_trans C1.
have := cvg_prob_sqrt (cvg_probB goe_sqnorm_half (cond_dist_goe_cvg C C1)).
apply: cvg_prob_eq; exists 1%N => d d0 a.
have Hs := goe_part_sym d (vec_mx a).
have dR : 0 < d%:R :> RR by rewrite ltr0n.
rewrite -mulrBl -(cond_support_sqr C1 Hs) /goe_part -cond_support_sym.
rewrite -expr_div_n sqrtr_sqr ger0_norm //.
by rewrite divr_ge0 ?ler0n // cond_support_ge0.
Qed.

(* The infimum of the clip energy over a window [0, T] that contains a
   minimizer is clip_value. *)
Lemma clip_inf_window (mu : probability (measurableTypeR R) R) (C T t0 : R) :
  0 <= t0 <= T -> clip_value mu C = clip_energy mu C t0 ->
  inf [set clip_energy mu C t | t in [set t : R | 0 <= t <= T]] =
  clip_value mu C.
Proof.
move=> /andP[t00 t0T] hv.
have lb : has_lbound [set clip_energy mu C t | t in [set t : R | 0 <= t <= T]].
  by exists 0 => _ [t _ <-]; exact: clip_energy_ge0.
apply/eqP; rewrite eq_le; apply/andP; split.
  by rewrite hv; apply: ge_inf => //; exists t0 => //=; rewrite t00 t0T.
apply: lb_le_inf; first by exists (clip_energy mu C t0), t0 => //=; rewrite t00.
by move=> _ [t /andP[t0' _] <-]; exact: clip_value_le.
Qed.
