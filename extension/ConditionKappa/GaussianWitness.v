(* The approximate Gaussian witness below the threshold alpha(C, kappa), at
   Stdlib's R: item G1 of phase 11, first half (notes/phase11-plan.md,
   sections 3.4, 5 and 6; lane B). The model is Condition/GaussianWitness.v,
   which treats kappa = 3.

   Setting. kappa > 1, c = (kappa - 3) / 2, a0 = min(1, 1 + c); C > 1. The
   cone T K_C, its base and its support function sigma_{C,kappa} are those
   of Cone (item B1). The Gaussian features are those of
   gaussian_feature_law kappa d: T_kappa stays in the step features_mul,
   through gaussian_feature_vec_dot (Gaussian/Representation.v), where the
   case kappa = 3 used cone_map3. The constants come from the bounds
   sqrt (a0 d) <= |T S|_F <= sqrt (max(1, 1 + c) C d) on the base, in place
   of sqrt d and sqrt (C d); they may depend on C, kappa and alpha.

   Interface I1, a hypothesis of the lemmas here: for C > 1,
     cvg_prob (fun d => gauss (d * d))
       (fun d a => sigma_{C,kappa}(vec_mx a) / d)
       (sqrt (condition_kappa_alpha C kappa)),
   the hypothesis hQ2 of Condition/GaussianWitness.v with sigma_{C,kappa}
   in place of cond_support C and alpha(C, kappa) in place of
   condition_alpha C. I1 is kcond_support_cvg of GaussianLimit.v
   (item M5). gaussian_kappa_witness keeps it as a hypothesis, and so does
   condition_kappa_sat of Sat.v, which applies the witness;
   condition_kappa_statement_of_I3 of Theorem.v discharges it with
   kcond_support_cvg.

   Output, interface I4 (the witness), for item D1 (Sat): for 1 < Cm and
   0 < alpha < alpha(Cm, kappa), some c0 >= 0 such that, for every n with
   n/d^2 -> alpha and every large d, outside a measurable set E of n d
   Gaussian features with
   tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= 1/4, some S
   of cond_slice Cm has sum_i <Z_i, mxvec S>^2 <= c0. S lies in the
   original trace-d slice: its condition number is measured on S, before
   T_kappa. This is the hypothesis of condition_sat_witness of
   Condition/Sat.v with gaussian_feature_law kappa d in place of
   gaussian_feature_law 3 d and alpha(Cm, kappa) in place of
   condition_alpha Cm.

   Proved.
   1. The auxiliary event. ksupport_density_cvg: interface I1 carried to
      z = (g, h) of law gauss (n d + d * d); kcond_aux_event: for
      n/d^2 -> alpha < alpha(C, kappa), |g| < sigma_{C,kappa}(vec_mx h)
      outside an event of small probability (with gnorm_density_cvg of
      Condition/GaussianWitness).
   2. The features. kfeatures_mul: for S symmetric,
      Z (mxvec S)^T = sqrt (2 / d) A (mxvec (T S))^T for the Gaussian
      features Z of the rows of A = vec_mx a (gaussian_feature_vec_dot).
      kescape_features_le: the infimum of |Z x| over the original slice
      (tr_set (cond_slice_vec C)) is at most sqrt (2 / d) times the infimum
      of |A x| over the base tr_set (kcond_slice_vec kappa C d) of Cone.
   3. The witness. kgaussian_witness_n: cone_escape_zero_tail on T K_C and
      its base, with rho = sqrt (max(1, 1 + c) C d) (kcond_B_le) and
      u = 4 rho, gives inf_(x in base) |A x| < 9 rho outside an event of
      probability at most 2 exp (- 8) <= 1/4, so some S of cond_slice C has
      sum_i <Z_i, mxvec S>^2 < (2 / d) (9 rho)^2 = 162 max(1, 1 + c) C.
      gaussian_kappa_witness states this with c0 = 162 max(1, 1 + c) C, as
      the theorem whose hypothesis is interface I1 and whose conclusion is
      the output above. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
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
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
From EllipsoidUniversality.Features Require Import Definitions.
From EllipsoidUniversality.Gaussian Require Import Cones Representation.
From EllipsoidUniversality.Gaussian Require Import InProbability FittingError.
From EllipsoidUniversality.Gaussian Require Import Subcritical.
From EllipsoidUniversality.Condition Require Import GaussianWitness.
From EllipsoidUniversality.ConditionKappa Require Import Cone.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. The auxiliary event. *)

Section kaux_event.
Variables (kappa C alpha : R) (n : nat -> nat).
Hypothesis a0 : 0 < alpha.
Hypothesis hn : universality_density_tends_to n alpha.
Hypothesis hQ2 : cvg_prob (fun d => @gauss RR (d * d))
  (fun d a => kcond_support kappa C (vec_mx a : 'M[RR]_d) / d%:R)
  (Num.sqrt (condition_kappa_alpha C kappa)).

(* sigma_{C,kappa}(vec_mx h) / d -> sqrt alpha(C, kappa) for h = rsubmx z. *)
Lemma ksupport_density_cvg : cvg_prob (fun d => @gauss RR (n d + d * d))
  (fun d z => kcond_support kappa C (vec_mx (rsubmx z) : 'M[RR]_d) / d%:R)
  (Num.sqrt (condition_kappa_alpha C kappa)).
Proof. exact: (@cvg_prob_gauss_rsubmx (fun d => d * d) n _ _ hQ2). Qed.

(* Below the threshold, |g| < sigma_{C,kappa}(vec_mx h) outside an event
   of small probability. *)
Lemma kcond_aux_event : alpha < condition_kappa_alpha C kappa ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists A : set 'rV[RR]_(n d + d * d), [/\ measurable A,
    (gauss (n d + d * d) A <= eps%:E)%E &
    forall z, ~ A z -> frobenius (lsubmx z) <
      kcond_support kappa C (vec_mx (rsubmx z) : 'M[RR]_d)].
Proof.
move=> aC eps e0.
have sa : Num.sqrt alpha < Num.sqrt (condition_kappa_alpha C kappa).
  by rewrite ltr_sqrt // (lt_trans a0 aC).
set del := (Num.sqrt (condition_kappa_alpha C kappa) - Num.sqrt alpha) / 2%:R.
have del0 : 0 < del by rewrite divr_gt0 // subr_gt0.
have [D hD] := negligibleU (gnorm_density_cvg alpha n hn del del0)
  (ksupport_density_cvg del del0) eps e0.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d1].
have [A [mA PA EA]] := hD d dD.
exists A; split => // z nA.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have h1 : `|frobenius (lsubmx z) / d%:R - Num.sqrt alpha| < del.
  by rewrite ltNge; apply/negP => h; apply: nA; apply: EA; left.
have h2 : `|kcond_support kappa C (vec_mx (rsubmx z) : 'M[RR]_d) / d%:R -
    Num.sqrt (condition_kappa_alpha C kappa)| < del.
  by rewrite ltNge; apply/negP => h; apply: nA; apply: EA; right.
have : frobenius (lsubmx z) / d%:R <
    kcond_support kappa C (vec_mx (rsubmx z) : 'M[RR]_d) / d%:R.
  move: h1 h2; rewrite !ltr_norml /del => /andP[_ h1] /andP[h2 _].
  lra.
by rewrite ltr_pM2r // invr_gt0.
Qed.

End kaux_event.

(* 2. The features: T_kappa stays in the product. *)

(* Z (mxvec S)^T = sqrt (2 / d) A (mxvec (T S))^T for the Gaussian features
   Z of the rows of A = vec_mx a and S symmetric. *)
Lemma kfeatures_mul (kappa : R) (N d : nat) (a : 'rV[RR]_(N * (d * d)))
    (S : 'M[RR]_d) : S \is symmetricmx ->
  tuple_mx (gaussian_features kappa N d a) *m (mxvec S)^T =
  Num.sqrt (2%:R / d%:R) *:
    ((vec_mx a : 'M[RR]_(N, d * d)) *m (mxvec (cone_map kappa S))^T).
Proof.
move=> Ss.
apply/matrixP => i j; rewrite ord1 [RHS]mxE !mulmx_trE row_tuple_mx.
rewrite /gaussian_features tnth_mktuple.
rewrite (gaussian_feature_vec_dot _ _ _ _ (symmetric_paper _ _ Ss)).
by rewrite linearZ /= mxdotZr.
Qed.

(* The infimum over the original slice of the features is at most
   sqrt (2 / d) times the infimum over the base of T K_C of the Gaussian
   matrix. *)
Lemma kescape_features_le (kappa C : R) (N d : nat)
    (a : 'rV[RR]_(N * (d * d))) : 1 < C -> (0 < d)%N ->
  escape_inf (tr_set (@cond_slice_vec RR d C))
    (tuple_mx (gaussian_features kappa N d a)) <=
  Num.sqrt (2%:R / d%:R) * escape_inf (tr_set (kcond_slice_vec kappa C d))
    (vec_mx a : 'M[RR]_(N, d * d)).
Proof.
move=> C1 d0; have B0 := kcond_B_neq0 kappa C d C1.
have s0 : 0 < Num.sqrt (2%:R / d%:R) :> RR.
  by rewrite sqrtr_gt0 divr_gt0 // ltr0n.
rewrite -ler_pdivrMl //; apply: escape_inf_ge => // _ [_ [S BS <-] <-].
have Ss : S \is symmetricmx by case: BS => [[]].
have B'S : tr_set (@cond_slice_vec RR d C) (mxvec S)^T.
  by exists (mxvec S) => //; rewrite /cond_slice_vec /= mxvecK.
rewrite ler_pdivrMl //; apply: le_trans (escape_inf_le _ B'S) _.
by rewrite kfeatures_mul // frobeniusZ ger0_norm // sqrtr_ge0.
Qed.

(* 3. The witness. *)

Lemma kwitness_ln4 : Num.sqrt (ln 4%:R) <= 2%:R :> RR.
Proof.
have h : ln 4%:R <= 2%:R ^+ 2 :> RR.
  rewrite -[X in _ <= X]expRK ler_ln ?posrE ?expR_gt0 ?ltr0n //.
  apply: le_trans (expR_ge1Dx _).
  by rewrite -natrX -[(1 : RR)]/(1%:R) -natrD ler_nat.
apply: le_trans (ler_wsqrtr h) _.
by rewrite sqrtr_sqr ger0_norm ?ler0n.
Qed.

Lemma kwitness_exp8 : 2 * expR (- 8%:R) <= 4%:R^-1 :> RR.
Proof.
have h : 8%:R <= expR 8%:R :> RR by have := expR_ge1Dx (8%:R : RR); lra.
rewrite expRN; apply: (@le_trans _ _ (2 * 8%:R^-1)).
  by rewrite ler_wpM2l // lef_pV2 ?posrE ?expR_gt0 ?ltr0n.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

Lemma kwitness_half : 2^-1 < 1 - 4%:R^-1 :> RR.
Proof. lra. Qed.

Lemma kwitness_five (x : RR) : x <= 2%:R -> 1 + 2 * x <= 5%:R.
Proof. lra. Qed.

Lemma kwitness_thr9 (x rho : RR) : x <= rho * 5%:R ->
  x + 4%:R * rho <= 9%:R * rho.
Proof. lra. Qed.

Lemma kwitness_const (M C D : RR) : D != 0 ->
  2%:R / D * (9%:R ^+ 2 * (M * C * D)) = 162%:R * M * C.
Proof. by move=> Dn; field. Qed.

Section kwitness.
Variables (kappa C alpha : R) (n : nat -> nat).
Hypotheses (k1 : 1 < kappa) (C1 : 1 < C) (a0 : 0 < alpha).
Hypothesis aC : alpha < condition_kappa_alpha C kappa.
Hypothesis hn : universality_density_tends_to n alpha.
Hypothesis hQ2 : cvg_prob (fun d => @gauss RR (d * d))
  (fun d a => kcond_support kappa C (vec_mx a : 'M[RR]_d) / d%:R)
  (Num.sqrt (condition_kappa_alpha C kappa)).

(* The witness for one sequence n: outside an event of Gaussian probability
   at most 1/4, some S of the trace-d slice of the cone of condition number
   C has sum_i <Z_i, mxvec S>^2 <= 162 max(1, 1 + c) C. *)
Lemma kgaussian_witness_n : exists D : nat, forall d, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <=
     (4%:R^-1)%:E)%E &
    forall Z, ~ E Z -> exists2 S : 'M[RR]_d, cond_slice C S &
      \sum_(i < n d) mxdot (tnth Z i) (mxvec S) ^+ 2 <=
      162%:R * Num.max 1 (1 + cone_shift kappa) * C].
Proof.
have e4 : (0 : RR) < 4%:R^-1 by rewrite invr_gt0 ltr0n.
have [D1 hD1] := kcond_aux_event kappa C alpha n a0 hn hQ2 aC _ e4.
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
set K := tr_set (kcond_cone_vec kappa C d).
set B := tr_set (kcond_slice_vec kappa C d).
set B' := tr_set (@cond_slice_vec RR d C).
have C0 : 0 < C := lt_trans ltr01 C1.
have M1 : 1 <= Num.max 1 (1 + cone_shift kappa) by rewrite le_max lexx.
pose rho : RR := Num.sqrt (Num.max 1 (1 + cone_shift kappa) * C * d%:R).
have rho0 : 0 < rho.
  rewrite /rho sqrtr_gt0 !mulr_gt0 // ?ltr0n //.
  exact: lt_le_trans ltr01 M1.
have K0 : K 0 := kcond_K0 kappa C d.
have B0 : B !=set0 := kcond_B_neq0 kappa C d C1.
have Bb : forall x, B x -> frobenius x <= rho := kcond_B_le kappa C d k1 C1.
have Kc : closed K := kcond_K_closed kappa C d k1 C1.
have Bbase := kcond_B_base kappa C d.
have Bc : closed B := kcond_B_closed kappa C d k1 C1.
have Bcvx := kcond_B_convex kappa C d.
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
  apply: (lt_le_trans _ (le_trans PC _)).
    by rewrite lte_fin; exact: kwitness_half.
  apply: le_measure; rewrite ?inE; [exact: measurableC|exact: mev|].
  by move=> z /= nz; rewrite /K kcond_cone_supE; exact: nA.
(* the CGMT on the cone, with u = 4 rho *)
have u0 : 0 <= 4%:R * rho by rewrite mulr_ge0 // ltW.
have tail := cone_escape_zero_tail K0 B0 Bb N0 rho0 Kc Bbase Bc Bcvx u0 hz.
set thr := rho * (1 + 2 * Num.sqrt (ln 4%:R)) + 4%:R * rho.
pose s2 : RR := Num.sqrt (2%:R / d%:R).
have s20 : 0 < s2 by rewrite /s2 sqrtr_gt0 divr_gt0 // ltr0n.
have mPhiZ := measurable_escape_features C (n d) d C1 d1.
have mE : measurable [set Z : (n d).-tuple 'rV[RR]_(d * d) |
    s2 * thr <= escape_inf B' (tuple_mx Z)] :=
  measurable_ge_set _ (s2 * thr) mPhiZ.
exists [set Z | s2 * thr <= escape_inf B' (tuple_mx Z)]; split => //.
  rewrite gaussian_features_law //.
  apply: le_trans (le_trans _ tail) _.
    apply: le_measure; rewrite ?inE.
    - have := measurable_gaussian_features kappa (n d) d measurableT _ mE.
      by rewrite setTI.
    - have mPhi := measurable_escape_inf (N := n d) B0 Bb.
      exact: measurable_ge_set _ thr mPhi.
    - move=> a /= ha.
      have := kescape_features_le kappa C (n d) d a C1 d1.
      rewrite -/B -/B' -/s2 => hle.
      by rewrite -(ler_pM2l s20); apply: le_trans hle.
  rewrite lee_fin; have rn : rho != 0 by rewrite gt_eqF.
  have -> : - (4%:R * rho) ^+ 2 / (2 * rho ^+ 2) = - 8%:R :> RR by field.
  exact: kwitness_exp8.
(* outside the event, a witness of the original slice *)
move=> Z nE.
have hlt : escape_inf B' (tuple_mx Z) < s2 * thr.
  by rewrite ltNge; apply/negP.
have B'0 : B' !=set0 := cond_B_neq0 C d C1 d1.
have Bn : [set frobenius (tuple_mx Z *m x) | x in B'] !=set0.
  by case: B'0 => x Bx; exists (frobenius (tuple_mx Z *m x)), x.
have [_ [x [v Bv xE] <-] hx] := inf_lt Bn hlt.
exists (vec_mx v) => //.
rewrite vec_mxK sum_features_sqr xE.
have thr0 : 0 <= thr.
  apply: addr_ge0; last by rewrite mulr_ge0 // ltW.
  by rewrite mulr_ge0 ?(ltW rho0) // addr_ge0 // mulr_ge0 // sqrtr_ge0.
have thr9 : thr <= 9%:R * rho.
  have h5 : rho * (1 + 2 * Num.sqrt (ln 4%:R)) <= rho * 5%:R.
    by apply: ler_wpM2l; [exact: ltW | exact: kwitness_five kwitness_ln4].
  exact: kwitness_thr9 h5.
have rho2 : rho ^+ 2 = Num.max 1 (1 + cone_shift kappa) * C * d%:R.
  rewrite /rho sqr_sqrtr // !mulr_ge0 ?ler0n ?(ltW C0) //.
  exact: le_trans ler01 M1.
have s22 : s2 ^+ 2 = 2%:R / d%:R by rewrite /s2 sqr_sqrtr // divr_ge0 ?ler0n.
have h1 : frobenius (tuple_mx Z *m x) ^+ 2 <= (s2 * thr) ^+ 2.
  by rewrite ler_sqr ?nnegrE ?frobenius_ge0 ?mulr_ge0 ?(ltW s20) // ltW.
apply: le_trans h1 _; rewrite exprMn s22.
have t2 : thr ^+ 2 <= (9%:R * rho) ^+ 2.
  by rewrite ler_sqr ?nnegrE ?mulr_ge0 ?(ltW rho0).
rewrite exprMn rho2 in t2.
apply: le_trans (ler_wpM2l _ t2) _; first by rewrite divr_ge0 ?ler0n.
have dn : (d%:R : RR) != 0 by rewrite pnatr_eq0 -lt0n.
by rewrite kwitness_const.
Qed.

End kwitness.

(* Item G1, the witness, in the form that the satisfiable half (item D1,
   Sat) takes as its hypothesis: below alpha(C, kappa), with the constant
   c0 = 162 max(1, 1 + c) C. The hypothesis on kcond_support is
   interface I1, kcond_support_cvg of GaussianLimit.v, which
   condition_kappa_statement_of_I3 of Theorem.v supplies. *)
Theorem gaussian_kappa_witness (kappa C alpha : R) :
  1 < kappa -> 1 < C -> 0 < alpha -> alpha < condition_kappa_alpha C kappa ->
  cvg_prob (fun d => @gauss RR (d * d))
    (fun d a => kcond_support kappa C (vec_mx a : 'M[RR]_d) / d%:R)
    (Num.sqrt (condition_kappa_alpha C kappa)) ->
  exists c0 : R, 0 <= c0 /\
   forall n : nat -> nat, universality_density_tends_to n alpha ->
   exists D : nat, forall d, (D <= d)%N ->
   exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
     (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <=
       (1 / 4)%:E)%E &
     forall Z, ~ E Z -> exists S : 'M[R]_d, cond_slice C S /\
       \sum_(i < n d) mxdot (tnth Z i) (mxvec S) ^+ 2 <= c0].
Proof.
move=> k1 C1 a0 aC hQ2.
exists (162%:R * Num.max 1 (1 + cone_shift kappa) * C); split.
  rewrite !mulr_ge0 ?ler0n // ?(ltW (lt_trans ltr01 C1)) //.
  by rewrite le_max ler01.
move=> n hn.
have [D hD] := kgaussian_witness_n kappa C alpha n k1 C1 a0 aC hn hQ2.
exists D => d dD; have [E [mE PE hE]] := hD d dD.
exists E; split => //; first by rewrite mul1r.
by move=> Z nE; have [S hS hL] := hE Z nE; exists S.
Qed.
