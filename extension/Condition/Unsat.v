(* The unsatisfiable half of the condition-number threshold (20) at fourth
   moment three, for finite mixtures of product laws, at Stdlib's R: item
   Q8 of phase 8 (notes/three-extensions-plan.md, sections 2 (D2) and 5.2;
   lane A). The mirror of Condition/Sat.v.

   The event is universality_conditioned_fit_event (n d) d C: the sample
   has an exact fit of value 1 and of condition number at most C. The
   features are W_i = (x_i x_i^T - I) / sqrt d (sample_W), the Gaussian
   features are those of gaussian_feature_law 3 d, and the mean feature is
   W-bar = (1 / n) sum_i W_i = sample_adj x (1 / n, ..., 1 / n).

   Main results.
   - cond_fit_slice: an exact fit S of condition number at most C, scaled
     to R = (d / tr S) S, lies in cond_slice C (the trace-d slice of the
     cone of condition number C), and all the values <W_i, R> are equal,
     to b0 = (d / tr S - d) / sqrt d. common_value_adj: then
     b0 = <W-bar, R>, so |b0| <= |W-bar|_F |R|_F (common_value_le).
   - af_value_common: the value af_value of a slice pd_slice2 d a b that
     contains such an R is at most beta (Mk b + b0^2) + gamma Bar (R), the
     objective at (R, b0), whose loss is 0. af_value_gap: if every S of
     cond_slice Cp has sum_i (b - <Z_i, S>)^2 >= g n for every b, and the
     slice lies in cond_slice Cp (b <= Cp a, slice2_cond_slice of
     Condition/Cover.v), then af_value >= g / 2, since the ridge and the
     barrier are nonnegative.
   - mixture_adjoint_bound: the a priori estimate of Sat/Apriori.v
     (adjoint_bound_limit_flat) for finite mixtures of product laws: with
     probability tending to one, |sum_i z_i W_i|_F <= C_a sqrt d |z| for
     every z, with C_a = adj_const K 252 (alpha + 1). With z constant,
     |W-bar|_F <= C_a sqrt (d / n).
   - condition_unsat_gap: let K > 0, 1 < C < Cp and alpha > 0, and suppose
     the Gaussian gap: some g > 0 such that, for every eps > 0 and d large,
     outside an event of Gaussian probability at most eps, every S of
     cond_slice Cp and every b have sum_i (b - <G_i, S>)^2 >= g n (the
     statement of item Q4, taken as a hypothesis). Then for every finite
     mixture family of class K and fourth moment 3 and every n with
     n/d^2 -> alpha, the probability of the conditioned fit event at C
     tends to 0.
     Proof: cond_cover of Condition/Cover.v for C_0 = C, C_1 = Cp gives
     finitely many slices (a_j, b_j) with b_j < Cp a_j. On each slice, with
     the weights beta_j = sl_beta 3 b_j delta and t_j = beta_j / 8 of
     Condition/Slices.v, the Gaussian center is at least g / 4
     (af_center_ge with the gap event at probability 1/2), so the value of
     the data features is at least g / 4 - beta_j / 4 outside the event of
     Theorem 2.9 (af_conc, sl_err_small, sl_prob_small). An exact fit of
     condition number at most C gives a slice j and R with value at most
     beta_j (Mk b_j + b0^2) + B / sqrt d, with b0^2 <= 2 C_a^2 b_j / alpha
     outside the event of mixture_adjoint_bound. For delta small, given g,
     C_a and alpha, and d large, this is below g / 16, a contradiction.
     So the conditioned fit event lies in the union of the J events of
     Theorem 2.9 and of the event of the a priori estimate. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From mathcomp Require Import numfun measurable_realfun sequences.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.matrix Require Import nuclear condition_cone.
From GaussianAnalysis.probability Require Import lindeberg subgaussian mixture.
From GaussianAnalysis.convex Require Import logdet_barrier least_squares.
From GaussianAnalysis.convex Require Import ridge_comparison.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import Measurability.Fit Measurability.Balanced.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Features Require Import Definitions Regular Mixture.
From EllipsoidUniversality.Model Require Import Rows Measurability.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Unsat Require Import FourthMomentThree.
From EllipsoidUniversality.Sat Require Import Apriori ApproximateFit Universality.
From EllipsoidUniversality.Mixture Require Import Flat.
From EllipsoidUniversality.Condition Require Import Slices Cover Sat.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. From an exact fit of condition number at most C to a point of the
   trace slice of the cone, with a common value of the features. *)

Lemma pm_qf_col d (S : 'M[R]_d) (v : 'cV[R]_d) :
  paper_main_quadratic_form S v = mxdot v (S *m v).
Proof.
rewrite /paper_main_quadratic_form /mxdot; apply: eq_bigr => i _.
rewrite big_ord1 !mxE mulr_sumr; apply: eq_bigr => j _.
by rewrite mulrA.
Qed.

Lemma pm_sqnorm_col d (v : 'cV[R]_d) : pm_sqnorm d v = mxdot v v.
Proof. by rewrite /pm_sqnorm /mxdot; apply: eq_bigr => i _; rewrite big_ord1. Qed.

Lemma cond_fit_slice N d (x : paper_main_sample N d) (C : R) :
  (0 < d)%N -> universality_conditioned_fit_event N d C x ->
  exists (S : 'M[R]_d) (b0 : R),
    cond_slice C S /\ forall i, mxdot (sample_W x i) S = b0.
Proof.
move=> d0 [S [lm [lm0 [hlo [hhi hfit]]]]].
have [Ss Slo] := (uni_loewner_geP d lm S).1 hlo.
have [_ Shi] := (uni_loewner_leP d (C * lm) S).1 hhi.
have Ssym : S \is symmetricmx.
  by apply/symmetricmxP/matrixP => i j; rewrite mxE Ss.
have KS : cond_cone C S.
  split => //; exists lm; first exact: ltW.
  move=> v; apply/andP; split.
    by move: (Slo v); rewrite pm_qf_col pm_sqnorm_col.
  by move: (Shi v); rewrite pm_qf_col pm_sqnorm_col.
have S0 : S != 0.
  apply/eqP => S0.
  pose v : 'cV[R]_d := const_mx 1.
  have v0 : v != 0.
    apply/eqP => /matrixP /(_ (Ordinal d0) 0).
    by rewrite !mxE => /eqP; rewrite oner_eq0.
  have := Slo v; rewrite S0 pm_qf_col mul0mx mxdot0r.
  have := pm_sqnorm_gt0 d v v0 => hv h.
  by have := mulr_gt0 lm0 hv; rewrite ltNge h.
have [trS hR] := cond_cone_slice KS S0.
exists ((d%:R / \tr S) *: S), ((d%:R / \tr S - d%:R) / Num.sqrt d%:R).
split => // i.
have h := qf_sample_W N d x i ((d%:R / \tr S) *: S) d0.
rewrite uni_qf_scalemx hfit mulr1 in h.
have trR : \tr ((d%:R / \tr S) *: S) = d%:R by case: hR.
rewrite trR in h.
have sd : Num.sqrt (d%:R : RR) != 0 by rewrite gt_eqF // sqrtr_gt0 ltr0n.
move: h; set m := mxdot _ _ => h.
by rewrite h addrK mulrC mulKf.
Qed.

(* The common value is the Frobenius product with the mean feature. *)
Lemma common_value_adj N d (x : paper_main_sample N d) (S : 'M[R]_d)
    (b0 : R) : (0 < N)%N -> (forall i, mxdot (sample_W x i) S = b0) ->
  b0 = mxdot (sample_adj x (const_mx N%:R^-1)) S.
Proof.
move=> N0 h.
rewrite /sample_adj /coef_adj mxdot_suml.
have -> : \sum_(i < N) mxdot ((const_mx N%:R^-1 : 'rV[R]_N) 0 i *: sample_W x i)
    S = \sum_(i < N) N%:R^-1 * b0.
  by apply: eq_bigr => i _; rewrite mxdotZl mxE h.
rewrite sumr_const card_ord -mulr_natr.
have Nn : N%:R != 0 :> RR by rewrite pnatr_eq0 -lt0n.
by field.
Qed.

Lemma frobenius_const_row N : (0 < N)%N ->
  frobenius (const_mx N%:R^-1 : 'rV[R]_N) = (Num.sqrt N%:R)^-1.
Proof.
move=> N0.
have NR : 0 < N%:R :> RR by rewrite ltr0n.
rewrite /frobenius /mxdot big_ord1.
have -> : \sum_(j < N) (const_mx N%:R^-1 : 'rV[R]_N) 0 j *
    (const_mx N%:R^-1 : 'rV[R]_N) 0 j = N%:R^-1.
  under eq_bigr do rewrite !mxE.
  rewrite sumr_const card_ord -[LHS]mulr_natr.
  have Nn : N%:R != 0 :> RR by rewrite gt_eqF.
  by field.
by rewrite sqrtrV // ltW.
Qed.

Lemma common_value_le N d (x : paper_main_sample N d) (S : 'M[R]_d)
    (b0 c : R) : (0 < N)%N -> (forall i, mxdot (sample_W x i) S = b0) ->
  (forall z : 'rV[R]_N, frobenius (sample_adj x z) <= c * frobenius z) ->
  `|b0| <= c / Num.sqrt N%:R * frobenius S.
Proof.
move=> N0 h hc.
rewrite (common_value_adj N d x S b0 N0 h).
apply: le_trans (mxdot_le _ _) _.
apply: ler_wpM2r; first exact: frobenius_ge0.
by have := hc (const_mx N%:R^-1); rewrite frobenius_const_row.
Qed.

(* 2. The value of a slice at an exact fit, and on the Gaussian gap. *)

Lemma af_value_common (kappa m M : R) (d n : nat) (beta gamma : R)
    (Z : n.-tuple 'rV[RR]_(d * d)) (S : 'M[R]_d) (b0 : R) :
  1 < kappa -> (0 < d)%N -> 0 < m -> m < 1 < M -> 0 < beta -> 0 < gamma ->
  pd_slice2 d m M (mxvec S) -> (forall i, mxdot (tnth Z i) (mxvec S) = b0) ->
  af_value kappa m M d n beta gamma Z <=
    beta * (af_Mk kappa * M + b0 ^+ 2) +
    gamma * logdet_barrier2 d m M (mxvec S).
Proof.
move=> k1 d0 m0 mM b0' g0 DS hc.
have l0 := af_lam_gt0 kappa d k1 d0.
rewrite /af_value (sat_valueE m M d n _ beta gamma mM l0 b0' g0).
apply: le_trans (sat_minP m M d n _ beta gamma mM l0 b0' g0 predT Z
  (mxvec S) b0 DS) _.
rewrite /sat_obj /ls_barrier_objective /ls_ridge /ls_loss.
rewrite big1; first by move=> i _; rewrite hc subrr expr0n.
rewrite mulr0 add0r lerD2r.
apply: ler_wpM2l; first exact: ltW.
rewrite lerD2r.
have hF := slice2_frobenius d m M (mxvec S) (ltW m0) DS.
have hl := af_lam_le kappa d k1 d0.
have M0 : 0 < M by case/andP: mM => _ /(lt_trans ltr01).
apply: le_trans (ler_wpM2l (ltW l0) hF) _.
rewrite mulrCA [af_Mk kappa * M]mulrC; apply: ler_wpM2l; first exact: ltW.
exact: hl.
Qed.

Lemma af_value_gap (kappa m M Cp g : R) (d n : nat) (beta gamma : R)
    (Z : n.-tuple 'rV[RR]_(d * d)) :
  1 < kappa -> (0 < d)%N -> (0 < n)%N -> 0 < m -> m < 1 < M ->
  M <= Cp * m -> 0 < beta -> 0 < gamma ->
  (forall (S : 'M[R]_d) (b : R), cond_slice Cp S ->
     g * n%:R <= \sum_(i < n) (b - mxdot (tnth Z i) (mxvec S)) ^+ 2) ->
  g / 2 <= af_value kappa m M d n beta gamma Z.
Proof.
move=> k1 d0 n0 m0 mM MC b0 g0 hgap.
have l0 := af_lam_gt0 kappa d k1 d0.
rewrite /af_value (sat_valueE m M d n _ beta gamma mM l0 b0 g0).
have Dth := sat_min_in m M d n _ beta gamma mM l0 b0 g0 predT Z.
move: Dth.
set th := sat_min _ _ _ _ _ _ _ _ _ _ _ predT Z.
set b := sat_int _ _ _ _ _ _ _ _ _ _ _ predT Z => Dth.
have hS : cond_slice Cp (vec_mx th) := slice2_cond_slice Cp m M d th m0 MC Dth.
have := hgap (vec_mx th) b hS; rewrite vec_mxK => hL.
rewrite /sat_obj /ls_barrier_objective /ls_ridge /ls_loss.
have r0 : 0 <= beta * (opnorm (unsat_cov kappa d) * mxdot th th + b ^+ 2).
  by rewrite mulr_ge0 ?addr_ge0 ?sqr_ge0 ?mulr_ge0 ?mxdot_ge0 ?opnorm_ge0 //
    ltW.
have B0 : 0 <= gamma * logdet_barrier2 d m M th.
  by rewrite mulr_ge0 ?(ltW g0) // (sat_B0 m M d mM th Dth).
have nR : 0 < n%:R :> RR by rewrite ltr0n.
have hs : g / 2 <=
    (n%:R *+ 2)^-1 * \sum_(i < n | predT i) (b - mxdot (tnth Z i) th) ^+ 2.
  have -> : g / 2 = (n%:R *+ 2)^-1 * (g * n%:R).
    have nn : n%:R != 0 :> RR by rewrite gt_eqF.
    by rewrite -mulr_natr; field.
  by apply: ler_wpM2l; [exact: (sat_s0 n) | exact: hL].
move: hs r0 B0.
set u := (n%:R *+ 2)^-1 * _; set v := beta * _; set z := gamma * _.
by move=> hs r0 B0; lra.
Qed.

(* 3. The a priori estimate for finite mixtures of product laws. *)

Lemma mixture_adjoint_bound (K alpha : R) (N : nat -> nat)
    (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R) :
  mixture_family K N w mu -> 0 < alpha ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (mixture_probability (N d) (w d) (mu d) (n d) d E <= eps%:E)%E &
    forall x, ~ E x -> forall z : 'rV[R]_(n d),
      frobenius (sample_adj x z) <=
        adj_const K (252)%R (alpha + 1) * Num.sqrt d%:R * frobenius z].
Proof.
move=> hfam a0 n hn eps e0.
have [D hD] := adjoint_bound_limit_flat K alpha n a0 hn eps e0.
exists D => d dD.
have [w0 [w1 hmu]] := hfam d.
have hw : mixture_weights (fun t : 'I_(N d) => w d t).
  by split => // t; exact: w0.
have hws := @mixture_weights_prod _ _ _ (n d) hw.
pose P (s : (n d).-tuple 'I_(N d)) :=
  mixture_labelled_law (N d) (mu d) (n d) d s.
pose Q (x : paper_main_sample (n d) d) := forall z : 'rV[R]_(n d),
  frobenius (sample_adj x z) <=
    adj_const K (252)%R (alpha + 1) * Num.sqrt d%:R * frobenius z.
pose F := [set x : paper_main_sample (n d) d | ~ Q x].
have hE (s : (n d).-tuple 'I_(N d)) :
    exists E : set (paper_main_sample (n d) d),
    [/\ measurable E, F `<=` E & (P s E <= eps%:E)%E].
  have [E [mE PE hE]] := hD d dD _
    (labelled_component K (N d) (mu d) (n d) d s hmu).
  exists E; split => // x Fx; apply: contrapT => nE; apply: Fx.
  by have [_ h] := hE x nE.
pose E s := projT1 (cid (hE s)).
have mE s : measurable (E s) by case: (projT2 (cid (hE s))).
have FE s : F `<=` E s by case: (projT2 (cid (hE s))).
have PE s : (P s (E s) <= eps%:E)%E by case: (projT2 (cid (hE s))).
have [mI FI PI] := mixture_cover (P := P) hws mE FE PE.
exists (\bigcap_(s in [set: (n d).-tuple 'I_(N d)]) E s); split.
- exact: mI.
- by move: PI; rewrite mixtureE.
- by move=> x nx; apply: contrapT => hx; apply: nx; exact: FI.
Qed.

(* 4. Arithmetic for the choice of the constants. *)

Lemma cond_b0_bound (Ca b0 fR bj alpha : R) (d N : nat) :
  0 < alpha -> (0 < d)%N -> alpha / 2 * d%:R ^+ 2 <= N%:R ->
  `|b0| <= Ca * Num.sqrt d%:R / Num.sqrt N%:R * fR -> 0 <= fR ->
  fR ^+ 2 <= bj * d%:R -> 0 <= bj ->
  b0 ^+ 2 <= 2 * Ca ^+ 2 / alpha * bj.
Proof.
move=> a0 d0 hN hb fR0 hF bj0.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have nR : 0 < N%:R :> RR.
  apply: lt_le_trans hN; apply: mulr_gt0; [exact: divr_gt0 | exact: exprn_gt0].
have h1 : b0 ^+ 2 <= (Ca * Num.sqrt d%:R / Num.sqrt N%:R * fR) ^+ 2.
  rewrite -real_normK ?num_real //.
  by apply: lerXn2r; rewrite ?nnegrE ?normr_ge0 //; exact: le_trans hb.
apply: le_trans h1 _.
have -> : (Ca * Num.sqrt d%:R / Num.sqrt N%:R * fR) ^+ 2 =
    Ca ^+ 2 * d%:R / N%:R * fR ^+ 2.
  rewrite !exprMn exprVn !sqr_sqrtr ?ler0n //.
have c0 : 0 <= Ca ^+ 2 * d%:R / N%:R.
  by rewrite divr_ge0 ?ler0n // mulr_ge0 ?sqr_ge0 ?ler0n.
apply: le_trans (ler_wpM2l c0 hF) _.
have k : d%:R ^+ 2 / N%:R <= 2 / alpha.
  rewrite ler_pdivrMr //.
  have h2 : 0 <= 2 / alpha by rewrite divr_ge0 // ltW.
  have an : alpha != 0 by rewrite gt_eqF.
  have := ler_wpM2l h2 hN.
  by have -> : 2 / alpha * (alpha / 2 * d%:R ^+ 2) = d%:R ^+ 2 by field.
have -> : Ca ^+ 2 * d%:R / N%:R * (bj * d%:R) =
    Ca ^+ 2 * bj * (d%:R ^+ 2 / N%:R) by rewrite expr2; ring.
have -> : 2 * Ca ^+ 2 / alpha * bj = Ca ^+ 2 * bj * (2 / alpha) by ring.
by apply: ler_wpM2l; [rewrite mulr_ge0 ?sqr_ge0 | exact: k].
Qed.

Lemma cond_beta_bound (Mk bj cb delta : R) : 2 <= Mk -> 0 < bj -> 0 <= cb ->
  0 < delta ->
  delta / (2 * (Mk * bj + 1)) * (Mk * bj + cb * bj) <= delta * (1 + cb) / 2.
Proof.
move=> Mk2 bj0 cb0 dl0.
have A0 : 0 < Mk * bj + 1 by rewrite addr_gt0 // mulr_gt0 //; lra.
rewrite mulrAC ler_pdivrMr ?mulr_gt0 //.
have -> : delta * (1 + cb) / 2 * (2 * (Mk * bj + 1)) =
    delta * ((1 + cb) * (Mk * bj + 1)) by field.
apply: ler_wpM2l; first exact: ltW.
have h1 : cb * bj <= cb * (Mk * bj) by rewrite ler_wpM2l // ler_peMl //; lra.
have h2 : 0 <= cb * (Mk * bj) by rewrite mulr_ge0 // mulr_ge0 //; lra.
rewrite mulrDl mul1r mulrDr mulr1.
lra.
Qed.

Lemma cond_prob_sum_eps (J : nat) (p : 'I_J -> R) (e : R) : 0 < e ->
  (forall j, p j <= 1 / af_Q (e / J.+1%:R)) -> \sum_(j < J) p j <= e / 2.
Proof.
move=> e0 hp.
apply: le_trans (ler_sum _ (fun j _ => hp j)) _.
rewrite sumr_const card_ord.
have J0 : 0 < J.+1%:R :> RR by rewrite ltr0n.
set x := e / J.+1%:R.
have x0 : 0 < x by rewrite divr_gt0.
have hQ : 2 / x <= af_Q x by rewrite /af_Q le_max lexx orbT.
have Q0 : 0 < af_Q x by apply: lt_le_trans hQ; rewrite divr_gt0.
have hq : 1 / af_Q x <= x / 2.
  rewrite ler_pdivrMr // mulrC -ler_pdivrMr ?divr_gt0 //.
  have xn : x != 0 by rewrite gt_eqF.
  by have -> : 1 / (x / 2) = 2 / x by field.
rewrite -/x.
apply: le_trans (_ : (x / 2) *+ J <= _); first by rewrite lerMn2r hq orbT.
rewrite -[X in X <= _]mulr_natr /x.
have hJ : (J%:R : RR) / J.+1%:R <= 1 by rewrite ler_pdivrMr // mul1r ler_nat.
have -> : e / J.+1%:R / 2 * J%:R = e / 2 * (J%:R / J.+1%:R) by ring.
rewrite -[X in _ <= X]mulr1 ler_wpM2l //.
by rewrite divr_ge0 // ltW.
Qed.

(* The barrier term: gamma B (R) <= B / sqrt d. *)
Lemma cond_bar_small (d : nat) (Bv B g : R) : (0 < d)%N -> 0 < g ->
  Bv <= d%:R * B -> 32 * Num.max B 0 / g <= Num.sqrt d%:R ->
  af_gam d * Bv <= g / 32.
Proof.
move=> d0 g0 hB hd.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have sd : 0 < Num.sqrt (d%:R : RR) by rewrite sqrtr_gt0.
have Bp0 : 0 <= Num.max B 0 by rewrite le_max lexx orbT.
have g1 := af_gam_gt0 d d0.
apply: le_trans (_ : af_gam d * (d%:R * Num.max B 0) <= _).
  apply: ler_wpM2l; first exact: ltW.
  by apply: le_trans hB _; apply: ler_wpM2l; [exact: ltW | rewrite le_max lexx].
have -> : af_gam d * (d%:R * Num.max B 0) = Num.max B 0 / Num.sqrt d%:R.
  have dn : d%:R != 0 :> RR by rewrite gt_eqF.
  have sn : Num.sqrt (d%:R : RR) != 0 by rewrite gt_eqF.
  by rewrite /af_gam; field.
rewrite ler_pdivrMr // mulrC -ler_pdivrMr ?divr_gt0 //.
have gn : g != 0 by rewrite gt_eqF.
by have -> : Num.max B 0 / (g / 32) = 32 * Num.max B 0 / g by field.
Qed.

(* beta_j <= g / 32 for delta = g / (16 (1 + cb)). *)
Lemma cond_beta_small (Mk bj cb g : R) : 2 <= Mk -> 0 < bj -> 0 <= cb ->
  0 < g -> g / (16 * (1 + cb)) / (2 * (Mk * bj + 1)) <= g / 32.
Proof.
move=> Mk2 bj0 cb0 g0.
have A1 : 1 <= Mk * bj + 1.
  by rewrite lerDr mulr_ge0 // ltW // (lt_le_trans _ Mk2).
have c1 : 1 <= 1 + cb by rewrite lerDl.
have P1 : 0 < 16 * (1 + cb) by rewrite mulr_gt0 //; lra.
have P2 : 0 < 2 * (Mk * bj + 1) by rewrite mulr_gt0 //; lra.
rewrite -mulrA -invfM.
rewrite ler_pM2l // lef_pV2 ?posrE ?mulr_gt0 //; try lra.
nra.
Qed.

Lemma cond_quarter_half (e : R) : 0 <= e -> e / 4 + e / 2 <= e.
Proof. by move=> e0; lra. Qed.

Lemma cond_norm_lb (v c e : R) : ~ (e < `|v - c|) -> c - e <= v.
Proof. by move/negP; rewrite -leNgt => /ler_normlP [h1 _]; lra. Qed.

(* The final contradiction: the value of the data is at least
   g / 4 - beta / 4 and at most g / 16. *)
Lemma cond_unsat_arith (v c e t bs u g bar : R) : 0 < g ->
  c - (e + t) <= v -> g / 4 <= c -> e <= bs / 8 -> t = bs / 8 ->
  bs <= g / 32 -> v <= u + bar -> u <= g / 32 -> bar <= g / 32 -> False.
Proof. by move=> g0 h1 h2 h3 h4 h5 h6 h7 h8; lra. Qed.

(* 5. The unsatisfiable half of (20) from the Gaussian gap. *)

Theorem condition_unsat_gap (K C Cp alpha : R) :
  0 < K -> 1 < C -> C < Cp -> 0 < alpha ->
  (exists g : R, 0 < g /\
   forall n : nat -> nat, universality_density_tends_to n alpha ->
   forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
   exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
     (tuple_prod (fun=> gaussian_feature_law 3%:R d) (n d) E <= eps%:E)%E &
     forall Z, ~ E Z -> forall S : 'M[R]_d, cond_slice Cp S -> forall b : R,
       g * (n d)%:R <= \sum_(i < n d) (b - mxdot (tnth Z i) (mxvec S)) ^+ 2]) ->
  forall (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment 3%:R N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  paper_main_tends_to
    (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                (universality_conditioned_fit_event (n d) d C)) 0.
Proof.
move=> K0 C1 CCp a0 [g [g0 hgap]] N w mu hfam h4 n hn.
have k1 : 1 < 3%:R :> RR by rewrite ltr1n.
(* the cover of the trace slice of the cone of condition number C *)
have [J [a [b [B [hab hcov]]]]] := cond_cover C Cp (ltW C1) CCp.
pose a' (j : 'I_J) := a j.
pose b' (j : 'I_J) := b j.
have a'0 j : 0 < a' j by have [] := hab j (ltn_ord j).
have a'b' j : a' j < 1 < b' j.
  by have [_ h1 h2 _] := hab j (ltn_ord j); rewrite /a' /b' h1 h2.
have b'Cp j : b' j <= Cp * a' j.
  by have [_ _ _ h] := hab j (ltn_ord j); exact: ltW.
have b'0 j : 0 < b' j.
  by have /andP[_ h] := a'b' j; exact: lt_trans ltr01 h.
(* the regularity of the two laws of features, as in Condition/Sat.v *)
pose Kf : RR := 2 ^+ 10 * K ^+ 2 / Num.sqrt (3%:R - 1).
have Kf0 : 0 <= Kf.
  by rewrite /Kf divr_ge0 ?sqrtr_ge0 // mulr_ge0 // exprn_even_ge0.
pose tau d : RR := Num.sqrt (2 ^+ 31 * K ^+ 8 / d%:R + 16 * K ^+ 8 / d%:R).
pose Kg := Num.max Kf (3 `^ (1 / 4)).
pose taug d := Num.max (tau d) (Num.sqrt 2 * opnorm (unsat_cov 3%:R d)).
have hreg d : (0 < d)%N -> regular_feature Kg (taug d) (unsat_cov 3%:R d)
    (mix_feature_law K N w mu hfam d).
  move=> d0; apply: regular_feature_le
    (mix_feature_regular K N w mu hfam 3%:R h4 d k1 d0);
    by rewrite ?le_max ?lexx ?sqrtr_ge0.
have hG d : (0 < d)%N -> regular_feature Kg (taug d) (unsat_cov 3%:R d)
    (gaussian_feature_law 3%:R d).
  move=> d0; apply: regular_feature_le
    (gaussian_feature_regular 3%:R d k1 d0);
    rewrite ?le_max ?lexx ?orbT ?powR_ge0 //.
  by rewrite mulr_ge0 ?sqrtr_ge0 ?opnorm_ge0.
have taug0 d : 0 <= taug d by rewrite le_max sqrtr_ge0.
have htaug (eta : RR) : 0 < eta -> af_eventually (fun d => taug d <= eta).
  move=> eta0.
  have [D1 h1] := mix_tau_small K eta eta0.
  have [D2 h2] := af_ev_gauss_tau 3%:R eta k1 eta0.
  exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
  by rewrite ge_max h1 // h2.
(* the a priori estimate, with its constant Ca kept abstract; it gives
   b0^2 <= cb b_j *)
have [Ca hadj] : exists Ca : RR, forall eps : RR, 0 < eps ->
    exists D : nat, forall d, (D <= d)%N ->
    exists E : set (paper_main_sample (n d) d), [/\ measurable E,
      (mixture_probability (N d) (w d) (mu d) (n d) d E <= eps%:E)%E &
      forall x, ~ E x -> forall z : 'rV[R]_(n d),
        frobenius (sample_adj x z) <= Ca * Num.sqrt d%:R * frobenius z].
  exists (adj_const K (252)%R (alpha + 1)).
  exact: (mixture_adjoint_bound K alpha N w mu hfam a0 n hn).
pose cb : RR := 2 * Ca ^+ 2 / alpha.
have cb0 : 0 <= cb.
  rewrite /cb; apply: divr_ge0; last exact: ltW.
  by apply: mulr_ge0; [exact: ler0n | exact: sqr_ge0].
pose mixP d : probability (paper_main_sample (n d) d) RR :=
  mixture (fun s : (n d).-tuple 'I_(N d) =>
      mixture_labelled_law (N d) (mu d) (n d) d s)
    (mixture_weights_prod (n d) (mix_weights K N w mu hfam d)).
have mixPE d (A : set (paper_main_sample (n d) d)) :
    mixture_probability (N d) (w d) (mu d) (n d) d A = mixP d A by [].
have key (eps : RR) : 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    exists B0 : set (paper_main_sample (n d) d), [/\ measurable B0,
      (mixP d B0 <= eps%:E)%E &
      universality_conditioned_fit_event (n d) d C `<=` B0].
  move=> ep0.
  have e2 : 0 < eps / 2 by rewrite divr_gt0.
  have h12 : 0 < 1 / 2 :> RR by rewrite divr_gt0 // ltr0n.
  pose delta := g / (16 * (1 + cb)).
  have c1p : 0 < 1 + cb by apply: lt_le_trans ltr01 _; rewrite lerDl.
  have dl0 : 0 < delta by rewrite divr_gt0 // mulr_gt0 // ltr0n.
  pose bs j := sl_beta 3%:R (b' j) delta.
  pose ts j := sl_t 3%:R (b' j) delta.
  pose etas j := sl_eta 3%:R Kg (b' j) delta.
  pose P1s j := sl_P1 3%:R Kg (b' j) delta.
  pose epsQ : RR := eps / 2 / J.+1%:R.
  have bs0 j : 0 < bs j := sl_beta_gt0 3%:R (a' j) (b' j) (a'b' j) delta dl0.
  have ts0 j : 0 < ts j := sl_t_gt0 3%:R (a' j) (b' j) (a'b' j) delta dl0.
  have etas0 j : 0 < etas j.
    exact: (sl_eta_gt0 3%:R Kg (a' j) (b' j) (a'b' j) delta dl0).
  have te j : 0 < (3%:R - 1) * alpha * etas j / 4.
    by rewrite divr_gt0 // mulr_gt0 // mulr_gt0 // subr_gt0.
  have Mk2 : 2 <= af_Mk 3%:R by rewrite /af_Mk le_max lexx.
  have hbs j : bs j * (af_Mk 3%:R * b' j + cb * b' j) <= g / 32.
    apply: le_trans (cond_beta_bound (af_Mk 3%:R) (b' j) cb delta Mk2 (b'0 j)
      cb0 dl0) _.
    have c1 : 1 + cb != 0 := lt0r_neq0 c1p.
    by rewrite /delta le_eqVlt; apply/orP; left; apply/eqP; field.
  have hbs2 j : bs j <= g / 32.
    exact: (cond_beta_small (af_Mk 3%:R) (b' j) cb g Mk2 (b'0 j) cb0 g0).
  have [Dn hDn] := af_ev_density n alpha a0 hn.
  have [Dg hDg] := hgap n hn (1 / 2) h12.
  have [Dm hDm] := hadj (eps / 2) e2.
  have [D72 hD72] := af_ev_sqrt (72 / alpha).
  have [DB hDB] := af_ev_sqrt (32 * Num.max B 0 / g).
  have [Dt hDt] := af_ev_fin J
    (fun j d => taug d <= (3%:R - 1) * alpha * etas j / 4)
    (fun j => htaug _ (te j)).
  have [D4 hD4] := af_ev_fin J (fun j d => 4 / (alpha * etas j) <= d%:R)
    (fun j => af_ev_ge _).
  have [D5 hD5] := af_ev_fin J
    (fun j d => 2 / (alpha * etas j ^+ 2) <= Num.sqrt d%:R)
    (fun j => af_ev_sqrt _).
  have [D7 hD7] := af_ev_fin J
    (fun j d => 2 / alpha * P1s j * af_Q epsQ <= d%:R)
    (fun j => af_ev_ge _).
  exists (maxn (maxn (maxn Dn Dg) (maxn Dm D72))
    (maxn (maxn DB Dt) (maxn D4 (maxn D5 D7)))) => d.
  rewrite !geq_max => /andP[/andP[/andP[dn dg] /andP[dm d72]]
    /andP[/andP[dB dt] /andP[d4 /andP[d5 d7]]]].
  have [d0 [nlo nhi]] := hDn d dn.
  have dR : 0 < d%:R :> RR by rewrite ltr0n.
  have nR : 0 < (n d)%:R :> RR.
    apply: lt_le_trans nlo; apply: mulr_gt0; last exact: exprn_gt0.
    by apply: divr_gt0.
  have n0 : (0 < n d)%N by rewrite -(ltr_nat RR).
  have g1 := af_gam_gt0 d d0.
  have n36 := af_n36 alpha a0 d (n d) d0 nlo (hD72 d d72).
  (* the Gaussian centers are at least g / 4 *)
  have [EG [mEG PEG hEG]] := hDg d dg.
  have hcen j : g / 4 <= af_center 3%:R (a' j) (b' j) d (n d) (bs j) (af_gam d).
    have h := af_center_ge 3%:R Kg (a' j) (b' j) d (n d) (bs j) (af_gam d)
      (taug d) (a'b' j) (bs0 j) g1 (hG d d0) EG (g / 2) mEG PEG
      (fun Z nZ => af_value_gap 3%:R (a' j) (b' j) Cp g d (n d) (bs j)
        (af_gam d) Z k1 d0 n0 (a'0 j) (a'b' j) (b'Cp j) (bs0 j) g1
        (fun S b hS => hEG Z nZ S hS b)).
    by move: h; have -> : g / 2 / 2 = g / 4 by field.
  (* the events of Theorem 2.9 for the mixture features *)
  pose rho := mix_feature_law K N w mu hfam d.
  pose F j := [set Z : (n d).-tuple 'rV[RR]_(d * d) |
    (af_err 3%:R Kg (a' j) (b' j) d (n d) (bs j) (af_gam d) (taug d) + ts j <
     `|af_value 3%:R (a' j) (b' j) d (n d) (bs j) (af_gam d) Z -
       af_center 3%:R (a' j) (b' j) d (n d) (bs j) (af_gam d)|)%R].
  have mF j : measurable (F j).
    apply: measurable_set_lt; apply: measurableT_comp (@normr_measurable RR _) _.
    apply: measurable_funB => //.
    exact: (measurable_af_value 3%:R (a' j) (b' j) d (n d) (bs j) (af_gam d)
      (a'b' j) (bs0 j) g1).
  have PF j : (tuple_prod (fun=> rho) (n d) (F j) <=
      (af_prob 3%:R Kg (a' j) (b' j) d (n d) (bs j) (af_gam d) (ts j))%:E)%E.
    exact: (af_conc 3%:R Kg (a' j) (b' j) d (n d) (bs j) (af_gam d) (ts j)
      (taug d) n0 (a'b' j) (bs0 j) g1 (ts0 j) n36 (taug0 d) (hG d d0) rho
      (hreg d d0)).
  have [mU PU] := slice_union_le (tuple_prod (fun=> rho) (n d)) mF.
  have hpsum : \sum_(j < J) af_prob 3%:R Kg (a' j) (b' j) d (n d) (bs j)
      (af_gam d) (ts j) <= eps / 4.
    have := cond_prob_sum_eps J (fun j => af_prob 3%:R Kg (a' j) (b' j) d (n d)
      (bs j) (af_gam d) (ts j)) (eps / 2) e2
      (fun j => sl_prob_small 3%:R Kg alpha (a' j) (b' j) k1 a0 (a'b' j) delta
        epsQ dl0 d (n d) d0 nlo (hD7 d d7 j)).
    by have -> : eps / 2 / 2 = eps / 4 by field.
  pose FU := unsat_features (n d) d @^-1` (\big[setU/set0]_(j < J) F j).
  have mFU : measurable FU.
    by rewrite /FU -[X in measurable X]setTI; exact: measurable_unsat_features.
  have PFU : (mixP d FU <= (eps / 4)%:E)%E.
    rewrite /FU -mixPE (mixture_features_law K N w mu hfam (n d) d _ mU).
    apply: le_trans PU _.
    apply: le_trans (_ : (\sum_(j < J) (af_prob 3%:R Kg (a' j) (b' j) d (n d)
        (bs j) (af_gam d) (ts j))%:E <= _)%E).
      by apply: lee_sum => j _; exact: PF.
    by rewrite sumEFin lee_fin.
  have [Em [mEm PEm hEm]] := hDm d dm.
  rewrite mixPE in PEm.
  exists (FU `|` Em); split.
  - exact: measurableU.
  - apply: le_trans (measureU2 _ mFU mEm) _.
    apply: le_trans (leeD PFU PEm) _.
    by rewrite -EFinD lee_fin; exact: (cond_quarter_half eps (ltW ep0)).
  move=> x hx; apply: contrapT => hno.
  have nFU : ~ FU x by move=> h; apply: hno; left.
  have nEm : ~ Em x by move=> h; apply: hno; right.
  have [R [b0 [hR hc]]] := cond_fit_slice (n d) d x C d0 hx.
  have [j0 jJ [hj hBar]] := hcov d R d0 hR.
  pose j := Ordinal jJ.
  have hj' : pd_slice2 d (a' j) (b' j) (mxvec R) := hj.
  pose W := unsat_features (n d) d x.
  have hcW i : mxdot (tnth W i) (mxvec R) = b0.
    by rewrite /W -mxvec_sample_W mxdot_mxvec hc.
  (* the value at the fit is at most g / 16 *)
  have hup := af_value_common 3%:R (a' j) (b' j) d (n d) (bs j) (af_gam d) W
    R b0 k1 d0 (a'0 j) (a'b' j) (bs0 j) g1 hj' hcW.
  have hb := common_value_le (n d) d x R b0 (Ca * Num.sqrt d%:R) n0 hc
    (hEm x nEm).
  have hRF : frobenius R ^+ 2 <= b' j * d%:R.
    rewrite frobenius_sqr -mxdot_mxvec.
    exact: (slice2_frobenius d (a' j) (b' j) (mxvec R) (ltW (a'0 j)) hj').
  have hb02 := cond_b0_bound Ca b0 (frobenius R) (b' j) alpha d (n d) a0 d0
    nlo hb (frobenius_ge0 R) hRF (ltW (b'0 j)).
  have hu : bs j * (af_Mk 3%:R * b' j + b0 ^+ 2) <= g / 32.
    apply: le_trans (hbs j).
    by apply: ler_wpM2l; [exact: ltW | rewrite lerD2l].
  have hbar := cond_bar_small d (logdet_barrier2 d (a' j) (b' j) (mxvec R)) B g
    d0 g0 hBar (hDB d dB).
  (* the value of the data is at least g / 4 - beta_j / 4 *)
  have nFj : ~ F j W.
    by move=> h; apply: nFU; rewrite /FU /=; exact: af_in_bigsetU h.
  have hlo : af_center 3%:R (a' j) (b' j) d (n d) (bs j) (af_gam d) -
      (af_err 3%:R Kg (a' j) (b' j) d (n d) (bs j) (af_gam d) (taug d) + ts j)
      <= af_value 3%:R (a' j) (b' j) d (n d) (bs j) (af_gam d) W.
    exact: cond_norm_lb nFj.
  have herr := sl_err_small 3%:R Kg alpha (a' j) (b' j) k1 a0 (a'b' j) delta
    dl0 d (n d) (taug d) d0 n0 (taug0 d) nlo (hDt d dt j) (hD4 d d4 j)
    (hD5 d d5 j).
  exact: (cond_unsat_arith _ _ _ _ _ _ _ _ g0 hlo (hcen j) herr erefl
    (hbs2 j) hup hu hbar).
move=> eps ep0.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have [D hD] := key (eps / 2) e2.
exists D => d dD.
have [B0 [mB PB hB]] := hD d dD.
have mC := measurable_conditioned_fit_event (n d) d C.
have hle : (mixP d (universality_conditioned_fit_event (n d) d C) <=
    (eps / 2)%:E)%E.
  by apply: le_trans PB; apply: le_measure => //; rewrite inE.
rewrite mixPE sube0 gee0_abs; first exact: measure_ge0.
by apply: le_lt_trans hle _; rewrite lte_fin; exact: sat_half.
Qed.
