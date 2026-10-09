(* The approximate Gaussian witness below the threshold alpha_C, at Stdlib's
   R: item Q3 of phase 8 (notes/three-extensions-plan.md, section 2, G3).

   Setting. For C > 1, cond_cone_vec C is the cone of the symmetric d x d
   matrices of condition number at most C and cond_slice_vec C its slice of
   trace d, in the coordinates of mxvec (library/matrix/condition_cone.v);
   K and B are their transposes, sets of column vectors (tr_set of
   library/comparison/cgmt.v). The support function of the cone is
   cond_support C, and cond_support C (vec_mx h) / d tends to
   sqrt (condition_alpha C) in probability for h of law gauss (d * d)
   (item Q2, a hypothesis here).

   1. The cone and its base. cond_K0, cond_K_closed, cond_K_cone,
      cond_B_base, cond_B_sub, cond_B_closed, cond_B_convex, cond_B_neq0:
      the hypotheses of library/comparison/cone_escape.v; cond_B_le,
      cond_B_ge: sqrt d <= |x| <= sqrt (C d) on B; cond_cone_supE: the
      support function cone_sup K h of cone_escape.v is
      cond_support C (vec_mx h).
   2. The auxiliary event. For n d / d^2 -> alpha < condition_alpha C,
      |g| / d -> sqrt alpha (gnorm_density_cvg, from gauss_sqnorm_cvg of
      Gaussian/FittingError) and cond_support C (vec_mx h) / d ->
      sqrt (condition_alpha C), so the probability that
      |g| < cone_sup K h, for z = (g, h) of law gauss (n d + d * d), tends
      to one (cond_aux_event).
   3. The witness. features_mul, escape_features_le: for the Gaussian
      features Z_i of the rows a_i of an n x d^2 Gaussian matrix A
      (gaussian_features of Gaussian/FittingError, of law
      gaussian_feature_law 3 d), <Z_i, v> = sqrt (2 / d) <a_i, v> for v in
      the slice (gaussian_feature_vec_dot and cone_map3); sum_features_sqr:
      sum_i <Z_i, v>^2 = |Z v^T|^2. gaussian_witness_n: cone_escape_zero_tail
      with u = 4 rho, rho = sqrt (C d), gives inf_(x in B) |A x| < 9 rho
      outside an event of probability at most 2 exp (- 8) <= 1/4, so some
      S of the slice has sum_i <Z_i, mxvec S>^2 < (2 / d) (9 rho)^2 =
      162 C. gaussian_witness states this, with c0 = 162 C, in the form
      that the satisfiable half (item Q7, Condition/Sat) takes as its
      hypothesis. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis Require Import euclidean measurable_matrix gauss.
From GaussianAnalysis Require Import gauss_law gauss_smoothing escape cgmt.
From GaussianAnalysis Require Import cone_escape moreau condition_cone.
From GaussianAnalysis Require Import gauss_matrix_law lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality.Features Require Import Definitions.
From EllipsoidUniversality.Gaussian Require Import Cones Representation.
From EllipsoidUniversality.Gaussian Require Import InProbability FittingError.
From EllipsoidUniversality.Gaussian Require Import Subcritical.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. The cone and its base, as sets of column vectors. *)

Section cone_base.
Variables (C : R) (d : nat).
Hypothesis C1 : 1 < C.

Local Notation K := (tr_set (@cond_cone_vec RR d C)).
Local Notation B := (tr_set (@cond_slice_vec RR d C)).

Let C0 : 0 < C. Proof. exact: lt_trans ltr01 C1. Qed.

Lemma cond_K0 : K 0.
Proof. exact: (tr_set0 (@cond_cone_vec0 RR d C)). Qed.

Lemma cond_K_closed : closed K.
Proof. exact: closed_tr_set (cond_cone_vec_closed (n := d) (ltW C0)). Qed.

Lemma cond_K_cone x (a : R) : K x -> 0 <= a -> K (a *: x).
Proof. by apply: tr_set_cone => y b Ky b0; exact: cond_cone_vecZ. Qed.

Lemma cond_B_base x : K x -> x != 0 -> exists2 a : R, 0 < a & B (a *: x).
Proof. by apply: tr_set_base => y Ky y0; exact: cond_cone_vec_slice. Qed.

Lemma cond_B_sub x : B x -> K x.
Proof. by apply: tr_set_sub => y [] . Qed.

Lemma cond_B_closed : closed B.
Proof. exact: closed_tr_set (cond_slice_vec_closed (n := d) (ltW C0)). Qed.

Lemma cond_B_convex x y (t : R) : B x -> B y -> 0 <= t <= 1 ->
  B (x + t *: (y - x)).
Proof.
by apply: convex_tr_set => u v s Bu Bv s01; exact: cond_slice_vec_convex.
Qed.

Lemma cond_B_neq0 : (0 < d)%N -> B !=set0.
Proof.
move=> d0; apply: tr_set_neq0; exists (mxvec (1%:M : 'M[RR]_d)).
by rewrite /cond_slice_vec /= mxvecK; exact: cond_slice1 (ltW C1).
Qed.

Lemma cond_B_le x : B x -> frobenius x <= Num.sqrt (C * d%:R).
Proof.
move=> [v Bv <-]; rewrite frobenius_trmx /frobenius.
have /andP[_ h] := cond_slice_vec_frobenius C0 Bv.
exact: ler_wsqrtr h.
Qed.

Lemma cond_B_ge x : B x -> Num.sqrt d%:R <= frobenius x.
Proof.
move=> [v Bv <-]; rewrite frobenius_trmx /frobenius.
have /andP[h _] := cond_slice_vec_frobenius C0 Bv.
exact: ler_wsqrtr h.
Qed.

(* The support function of K is cond_support C. *)
Lemma cond_cone_supE (h : 'rV[RR]_(d * d)) :
  cone_sup K h = cond_support C (vec_mx h).
Proof.
rewrite (cone_sup_proj (cond_cone_vec_closed (n := d) (ltW C0))
  (@cond_cone_vec0 RR d C) (@cond_cone_vec_convex RR d C)
  (@cond_cone_vecZ RR d C)).
by rewrite cond_support_proj // ltW.
Qed.

End cone_base.

(* 2. The auxiliary event. *)

Section aux_event.
Variables (C alpha : R) (n : nat -> nat).
Hypotheses (C1 : 1 < C) (a0 : 0 < alpha).
Hypothesis hn : universality_density_tends_to n alpha.
Hypothesis hQ2 : cvg_prob (fun d => @gauss RR (d * d))
  (fun d a => cond_support C (vec_mx a : 'M[RR]_d) / d%:R)
  (Num.sqrt (condition_alpha C)).

Let hN (eps : R) : 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  `|(n d)%:R / d%:R ^+ 2 - alpha| < eps.
Proof.
move=> e0; have [D hD] := hn eps e0; exists D => d dD.
by have := hD d dD; rewrite /paper_main_density.
Qed.

(* |g| / d -> sqrt alpha for g of law gauss (n d). *)
Lemma gnorm_density_cvg : cvg_prob (fun d => @gauss RR (n d + d * d))
  (fun d z => frobenius (lsubmx z) / d%:R) (Num.sqrt alpha).
Proof.
have h := cvg_prob_sqrt (gauss_sqnorm_cvg n alpha hN).
have h3 := @cvg_prob_gauss_lsubmx (fun d => d * d) n _ _ h.
apply: cvg_prob_eq h3; exists 1%N => d d1 z /=.
have dR : 0 < d%:R :> R by rewrite ltr0n.
by rewrite -expr_div_n sqrtr_sqr ger0_norm // divr_ge0 ?frobenius_ge0 ?ler0n.
Qed.

(* cond_support C (vec_mx h) / d -> sqrt alpha_C for h = rsubmx z. *)
Lemma support_density_cvg : cvg_prob (fun d => @gauss RR (n d + d * d))
  (fun d z => cond_support C (vec_mx (rsubmx z) : 'M[RR]_d) / d%:R)
  (Num.sqrt (condition_alpha C)).
Proof. exact: (@cvg_prob_gauss_rsubmx (fun d => d * d) n _ _ hQ2). Qed.

(* Below the threshold, |g| < cond_support C (vec_mx h) outside an event
   of small probability. *)
Lemma cond_aux_event : alpha < condition_alpha C ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists A : set 'rV[RR]_(n d + d * d), [/\ measurable A,
    (gauss (n d + d * d) A <= eps%:E)%E &
    forall z, ~ A z ->
      frobenius (lsubmx z) < cond_support C (vec_mx (rsubmx z) : 'M[RR]_d)].
Proof.
move=> aC eps e0.
have sa : Num.sqrt alpha < Num.sqrt (condition_alpha C).
  by rewrite ltr_sqrt // (lt_trans a0 aC).
set del := (Num.sqrt (condition_alpha C) - Num.sqrt alpha) / 2%:R.
have del0 : 0 < del by rewrite divr_gt0 // subr_gt0.
have [D hD] := negligibleU (gnorm_density_cvg del del0)
  (support_density_cvg del del0) eps e0.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d1].
have [A [mA PA EA]] := hD d dD.
exists A; split => // z nA.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have h1 : `|frobenius (lsubmx z) / d%:R - Num.sqrt alpha| < del.
  by rewrite ltNge; apply/negP => h; apply: nA; apply: EA; left.
have h2 : `|cond_support C (vec_mx (rsubmx z) : 'M[RR]_d) / d%:R -
    Num.sqrt (condition_alpha C)| < del.
  by rewrite ltNge; apply/negP => h; apply: nA; apply: EA; right.
have : frobenius (lsubmx z) / d%:R <
    cond_support C (vec_mx (rsubmx z) : 'M[RR]_d) / d%:R.
  move: h1 h2; rewrite !ltr_norml /del => /andP[_ h1] /andP[h2 _].
  lra.
by rewrite ltr_pM2r // invr_gt0.
Qed.

End aux_event.

(* 3. The witness. *)

Section features_slice.
Variables (C : R) (N d : nat).
Hypothesis C1 : 1 < C.

Local Notation B := (tr_set (@cond_slice_vec RR d C)).

(* <Z_i, v> = sqrt (2 / d) <a_i, v> for the features Z of the rows a_i of
   vec_mx a and v in the slice (a symmetric matrix). *)
Lemma features_mul (a : 'rV[RR]_(N * (d * d))) (x : 'cV[RR]_(d * d)) : B x ->
  tuple_mx (gaussian_features 3%:R N d a) *m x =
  Num.sqrt (2%:R / d%:R) *: ((vec_mx a : 'M[RR]_(N, d * d)) *m x).
Proof.
move=> [v [[Ss _] _] <-].
apply/matrixP => i j; rewrite ord1 [RHS]mxE !mulmx_trE row_tuple_mx.
rewrite /gaussian_features tnth_mktuple -[v in LHS]vec_mxK.
rewrite (gaussian_feature_vec_dot _ _ _ _ (symmetric_paper _ _ Ss)).
by rewrite cone_map3 linearZ /= vec_mxK mxdotZr.
Qed.

Lemma escape_features_le (a : 'rV[RR]_(N * (d * d))) : (0 < d)%N ->
  escape_inf B (tuple_mx (gaussian_features 3%:R N d a)) <=
  Num.sqrt (2%:R / d%:R) * escape_inf B (vec_mx a : 'M[RR]_(N, d * d)).
Proof.
move=> d0; have B0 := cond_B_neq0 C d C1 d0.
have s0 : 0 < Num.sqrt (2%:R / d%:R) :> RR.
  by rewrite sqrtr_gt0 divr_gt0 // ltr0n.
rewrite -ler_pdivrMl //; apply: escape_inf_ge => // x Bx.
rewrite ler_pdivrMl //; apply: le_trans (escape_inf_le _ Bx) _.
by rewrite features_mul // frobeniusZ ger0_norm // sqrtr_ge0.
Qed.

(* sum_i <Z_i, v>^2 = |Z v^T|^2. *)
Lemma sum_features_sqr (Z : N.-tuple 'rV[RR]_(d * d)) (v : 'rV[RR]_(d * d)) :
  \sum_(i < N) mxdot (tnth Z i) v ^+ 2 = frobenius (tuple_mx Z *m v^T) ^+ 2.
Proof.
rewrite frobenius_sqr [in RHS]/mxdot; apply: eq_bigr => i _.
by rewrite big_ord1 -expr2 mulmx_trE row_tuple_mx.
Qed.

Lemma measurable_escape_features : (0 < d)%N ->
  measurable_fun setT
    (fun Z : N.-tuple 'rV[RR]_(d * d) => escape_inf B (tuple_mx Z) : RR).
Proof.
move=> d0.
have m2 := measurable_escape_inf (N := N) (cond_B_neq0 C d C1 d0)
  (cond_B_le C d C1).
have -> : (fun Z : N.-tuple 'rV[RR]_(d * d) => escape_inf B (tuple_mx Z)) =
    (fun Z => escape_inf B (vec_mx (mxvec (tuple_mx Z)) : 'M[RR]_(N, d * d))).
  by apply/funext => Z; rewrite mxvecK.
apply: measurableT_comp m2 _.
exact: measurableT_comp (@measurable_mxvec _ _ _) (@measurable_tuple_mx _ _ _).
Qed.

End features_slice.

Section witness.
Variables (C alpha : R) (n : nat -> nat).
Hypotheses (C1 : 1 < C) (a0 : 0 < alpha) (aC : alpha < condition_alpha C).
Hypothesis hn : universality_density_tends_to n alpha.
Hypothesis hQ2 : cvg_prob (fun d => @gauss RR (d * d))
  (fun d a => cond_support C (vec_mx a : 'M[RR]_d) / d%:R)
  (Num.sqrt (condition_alpha C)).

Let C0 : 0 < C. Proof. exact: lt_trans ltr01 C1. Qed.

Let ln4 : Num.sqrt (ln 4%:R) <= 2%:R :> RR.
Proof.
have h : ln 4%:R <= 2%:R ^+ 2 :> RR.
  rewrite -[X in _ <= X]expRK ler_ln ?posrE ?expR_gt0 ?ltr0n //.
  apply: le_trans (expR_ge1Dx _).
  by rewrite -natrX -[(1 : RR)]/(1%:R) -natrD ler_nat.
apply: le_trans (ler_wsqrtr h) _.
by rewrite sqrtr_sqr ger0_norm ?ler0n.
Qed.

Let exp8 : 2 * expR (- 8%:R) <= 4%:R^-1 :> RR.
Proof.
have h : 8%:R <= expR 8%:R :> RR by have := expR_ge1Dx (8%:R : RR); lra.
rewrite expRN; apply: (@le_trans _ _ (2 * 8%:R^-1)).
  by rewrite ler_wpM2l // lef_pV2 ?posrE ?expR_gt0 ?ltr0n.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

(* The witness for one sequence n: outside an event of Gaussian probability
   at most 1/4, some S of the trace-d slice of the cone of condition number
   C has sum_i <Z_i, mxvec S>^2 <= 162 C. *)
Lemma gaussian_witness_n : exists D : nat, forall d, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law 3%:R d) (n d) E <=
     (4%:R^-1)%:E)%E &
    forall Z, ~ E Z -> exists2 S : 'M[RR]_d, cond_slice C S &
      \sum_(i < n d) mxdot (tnth Z i) (mxvec S) ^+ 2 <= 162%:R * C].
Proof.
have e4 : (0 : RR) < 4%:R^-1 by rewrite invr_gt0 ltr0n.
have [D1 hD1] := cond_aux_event C alpha n a0 hn hQ2 aC _ e4.
have a2 : 0 < alpha / 2%:R by rewrite divr_gt0.
have [D2 hD2] := hn _ a2.
exists (maxn (maxn D1 D2) 1) => d.
rewrite !geq_max => /andP[/andP[dD1 dD2] d1].
have [A [mA PA nA]] := hD1 d dD1.
(* n d > 0, since n d / d^2 is near alpha > 0 *)
have N0 : (0 < n d)%N.
  have := hD2 d dD2; rewrite /paper_main_density lt0n.
  apply: contraTneq => ->.
  rewrite RdivE mulr0n mul0r sub0r normrN ger0_norm ?(ltW a0) // -leNgt.
  lra.
set K := tr_set (@cond_cone_vec RR d C).
set B := tr_set (@cond_slice_vec RR d C).
pose rho : RR := Num.sqrt (C * d%:R).
have rho0 : 0 < rho by rewrite /rho sqrtr_gt0 mulr_gt0 // ltr0n.
have K0 : K 0 := cond_K0 C d.
have B0 : B !=set0 := cond_B_neq0 C d C1 d1.
have Bb : forall x, B x -> frobenius x <= rho := cond_B_le C d C1.
have Kc : closed K := cond_K_closed C d C1.
have Bbase := cond_B_base C d.
have Bc : closed B := cond_B_closed C d C1.
have Bcvx := cond_B_convex C d.
(* the event |g| < sigma_K(h): measurable, of probability > 1/2 *)
pose F (z : 'rV[RR]_(n d + d * d)) : RR :=
  cone_sup K (rsubmx z) - frobenius (lsubmx z).
have FL (z z' : 'rV[RR]_(n d + d * d)) :
    `|F z - F z'| <= 2%:R * frobenius (z - z').
  have h1 := cone_sup_lipschitz K0 (rsubmx z) (rsubmx z').
  have h2 := ler_frobeniusB (lsubmx z) (lsubmx z').
  have h3 := frobenius_rsubmx_le (z - z').
  have h4 := frobenius_lsubmx_le (z - z').
  rewrite !linearB /= in h3 h4.
  have -> : F z - F z' = (cone_sup K (rsubmx z) - cone_sup K (rsubmx z')) -
      (frobenius (lsubmx z) - frobenius (lsubmx z')) by rewrite /F; ring.
  apply: le_trans (ler_normB _ _) _.
  apply: le_trans (lerD (le_trans h1 h3) (le_trans h2 h4)) _.
  by rewrite mulr_natl mulr2n.
have mF : measurable_fun setT F :=
  continuous_measurable_mx (lipschitz_frobenius_continuous FL).
have mev : measurable [set z : 'rV[RR]_(n d + d * d) |
    frobenius (lsubmx z) < cone_sup K (rsubmx z)].
  have -> : [set z : 'rV[RR]_(n d + d * d) |
      frobenius (lsubmx z) < cone_sup K (rsubmx z)] = [set z | 0 < F z].
    by apply/seteqP; split => z /=; rewrite /F subr_gt0.
  exact: measurable_gt_set mF.
have fA : gauss (n d + d * d) A \is a fin_num := fin_num_measure _ A mA.
have PC : ((1 - 4%:R^-1)%:E <= gauss (n d + d * d) (~` A))%E.
  rewrite probability_setC // -(fineK fA) -EFinB lee_fin lerD2l lerN2.
  by rewrite -lee_fin fineK.
have hz : ((2^-1)%:E < gauss (n d + d * d)
    [set z | frobenius (lsubmx z) < cone_sup K (rsubmx z)]%R)%E.
  apply: (lt_le_trans _ (le_trans PC _)); first by rewrite lte_fin; lra.
  apply: le_measure; rewrite ?inE; [exact: measurableC|exact: mev|].
  by move=> z /= nz; rewrite /K cond_cone_supE //; exact: nA.
(* the CGMT on the cone, with u = 4 rho *)
have u0 : 0 <= 4%:R * rho by rewrite mulr_ge0 // ltW.
have tail := cone_escape_zero_tail K0 B0 Bb N0 rho0 Kc Bbase Bc Bcvx u0 hz.
set thr := rho * (1 + 2 * Num.sqrt (ln 4%:R)) + 4%:R * rho.
pose s2 : RR := Num.sqrt (2%:R / d%:R).
have s20 : 0 < s2 by rewrite /s2 sqrtr_gt0 divr_gt0 // ltr0n.
have mPhiZ := measurable_escape_features C (n d) d C1 d1.
have mE : measurable [set Z : (n d).-tuple 'rV[RR]_(d * d) |
    s2 * thr <= escape_inf B (tuple_mx Z)] :=
  measurable_ge_set _ (s2 * thr) mPhiZ.
exists [set Z | s2 * thr <= escape_inf B (tuple_mx Z)]; split => //.
  rewrite gaussian_features_law //.
  apply: le_trans (le_trans _ tail) _.
    apply: le_measure; rewrite ?inE.
    - have := measurable_gaussian_features 3%:R (n d) d measurableT _ mE.
      by rewrite setTI.
    - have mPhi := measurable_escape_inf (N := n d) B0 Bb.
      exact: measurable_ge_set _ thr mPhi.
    - move=> a /= ha.
      have := escape_features_le C (n d) d C1 a d1; rewrite -/B -/s2 => hle.
      by rewrite -(ler_pM2l s20); apply: le_trans hle.
  rewrite lee_fin; have rn : rho != 0 by rewrite gt_eqF.
  have -> : - (4%:R * rho) ^+ 2 / (2 * rho ^+ 2) = - 8%:R :> RR by field.
  exact: exp8.
(* outside the event, a witness of the slice *)
move=> Z nE.
have hlt : escape_inf B (tuple_mx Z) < s2 * thr by rewrite ltNge; apply/negP.
have Bn : [set frobenius (tuple_mx Z *m x) | x in B] !=set0.
  by case: B0 => x Bx; exists (frobenius (tuple_mx Z *m x)), x.
have [_ [x [v Bv xE] <-] hx] := inf_lt Bn hlt.
exists (vec_mx v) => //.
rewrite vec_mxK sum_features_sqr xE.
have thr0 : 0 <= thr.
  apply: addr_ge0; last by rewrite mulr_ge0 // ltW.
  by rewrite mulr_ge0 ?(ltW rho0) // addr_ge0 // mulr_ge0 // sqrtr_ge0.
have thr9 : thr <= 9%:R * rho.
  have h5 : rho * (1 + 2 * Num.sqrt (ln 4%:R)) <= rho * 5%:R.
    by apply: ler_wpM2l; [exact: ltW | move: ln4; lra].
  by move: h5; rewrite /thr; lra.
have rho2 : rho ^+ 2 = C * d%:R.
  by rewrite /rho sqr_sqrtr // mulr_ge0 // ?ler0n // ltW.
have s22 : s2 ^+ 2 = 2%:R / d%:R by rewrite /s2 sqr_sqrtr // divr_ge0 ?ler0n.
have h1 : frobenius (tuple_mx Z *m x) ^+ 2 <= (s2 * thr) ^+ 2.
  by rewrite ler_sqr ?nnegrE ?frobenius_ge0 ?mulr_ge0 ?(ltW s20) // ltW.
apply: le_trans h1 _; rewrite exprMn s22.
have t2 : thr ^+ 2 <= (9%:R * rho) ^+ 2.
  by rewrite ler_sqr ?nnegrE ?mulr_ge0 ?(ltW rho0).
rewrite exprMn rho2 in t2.
apply: le_trans (ler_wpM2l _ t2) _; first by rewrite divr_ge0 ?ler0n.
have dn : (d%:R : RR) != 0 by rewrite pnatr_eq0 -lt0n.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

End witness.

(* Item Q3, in the form that the satisfiable half (item Q7, Condition/Sat)
   takes as its hypothesis: below alpha_C, with the constant c0 = 162 C.
   The hypothesis on cond_support is the limit of item Q2. *)
Theorem gaussian_witness (C alpha : R) :
  1 < C -> 0 < alpha -> alpha < condition_alpha C ->
  cvg_prob (fun d => @gauss RR (d * d))
    (fun d a => cond_support C (vec_mx a : 'M[RR]_d) / d%:R)
    (Num.sqrt (condition_alpha C)) ->
  exists c0 : R, 0 <= c0 /\
   forall n : nat -> nat, universality_density_tends_to n alpha ->
   exists D : nat, forall d, (D <= d)%N ->
   exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
     (tuple_prod (fun=> gaussian_feature_law 3%:R d) (n d) E <=
       (1 / 4)%:E)%E &
     forall Z, ~ E Z -> exists S : 'M[R]_d, cond_slice C S /\
       \sum_(i < n d) mxdot (tnth Z i) (mxvec S) ^+ 2 <= c0].
Proof.
move=> C1 a0 aC hQ2; exists (162%:R * C); split.
  by rewrite mulr_ge0 // ltW // (lt_trans ltr01 C1).
move=> n hn.
have [D hD] := gaussian_witness_n C alpha n C1 a0 aC hn hQ2.
exists D => d dD; have [E [mE PE hE]] := hD d dD.
exists E; split => //; first by rewrite mul1r.
by move=> Z nE; have [S hS hL] := hE Z nE; exists S.
Qed.
