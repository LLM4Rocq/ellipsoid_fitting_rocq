(* The unsatisfiable phase at fourth moment 3: the first conjunct of
   Theorem 1.2 (ii) of Koehler and Sohn (arXiv 2608.27372, lines 164-190 of
   arxiv_v1.tex) for coordinate laws of fourth moment 3, by the paper's
   route (lines 1602-1635), at Stdlib's R. It is the theorem of stage 1 of
   phase 5 (AGENTS.md).

   Statement to prove (names come with the proofs): for K > 0 and
   alpha > 1/4, for every family nu of laws with
   universality_coordinate_law 3 K (nu d j) for j < d, and every n with
   universality_density_tends_to n alpha,
     paper_main_tends_to
       (fun d => universality_probability (nu d) (n d) d
                   (paper_main_fit_event (n d) d)) 0.
   With universality_alpha_star3 (Gaussian/Threshold), the same holds for
   every alpha > universality_alpha_star 3.

   Proved:
   1. fit_unsat_value: for d >= 1, if some S >= 0 fits the points with
      value d, then unsat_value of their features is at most 0: the
      optimal squared fitting error is 0 (fit_fitting_error, with
      (d / tr S) S, of trace d and constant values; tr S > 0 by
      psd_trace0_form) and it is 2 unsat_value (unsat_fitting_error of
      Unsat/LeastSquares).
   2. fit_event_vanishes: if the values of the data features (law
      data_feature_law (nu d) d) and of the Gaussian features (law
      gaussian_feature_law 3 d) concentrate around the same c d, and the
      Gaussian values are rarely below some e > 0 (goe_unsat_value_lower of
      Unsat/GoeBridge), then the probability of the fit event tends to 0:
      c d >= 3 e / 4 for every large d (concentration_lower), so a fitted
      sample, whose features have value 0, is farther than e / 4 from c d,
      an event of probability tending to 0 (sample_features_law of
      Model/Rows).
   3. The hypotheses of Corollary 2.13 (ii) (Unsat/Regularized) and of
      Lemma 2.12 (Unsat/Ridge) for the two laws, with common constants: both
      are regular features with the constants fmt_K K and fmt_tau K d
      (fmt_regular_data, fmt_regular_gauss, from data_feature_regular and
      gaussian_feature_regular of Features/Regular and the monotonicity
      regular_feature_le), fmt_tau K d <= fmt_C0 K / (ln d)^3 for every
      d > e (fmt_tau_le, by (ln d)^6 <= 720 d), and their quadratic forms
      <W, v^T v>, |v| <= 1, are subexponential with constant
      fmt_L0 K / sqrt d (fmt_subexp_data, fmt_subexp_gauss).

   To do: the stage theorem, from 2 and Corollary 2.13 (ii) applied to the
   two laws with the hypotheses of 3, once Lemma 2.12 asks its hypotheses
   for d >= 1 only (requests/b-to-c.md). *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.probability Require Import lindeberg subgaussian.
From GaussianAnalysis.convex Require Import least_squares ridge_comparison.
From EllipsoidFitting Require Import PaperMainDefinitions Measurability.Fit.
From EllipsoidFitting Require Import Geometry.Psd Geometry.Homogeneous
  Geometry.HeadSpectral Geometry.HeadCorrection.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares Regularized.
From EllipsoidUniversality.Unsat Require Import GoeBridge.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Model Require Import Rows.
Import GRing.Theory Num.Theory Order.TTheory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Stdlib's reals seen through their realType structure, which carries the
   measurable structure of MathComp-Analysis on matrices. *)
Local Notation RR := (R : realType).

(* 1. A fit makes the optimal squared fitting error zero. *)

Lemma quadratic_formE d (S : 'M[RR]_d) (v : 'cV[RR]_d) :
  paper_main_quadratic_form S v = mxdot v (S *m v).
Proof. by rewrite paper_main_quadratic_formE mxdot_colE mulmxA. Qed.

(* A positive semidefinite matrix of trace 0 has the quadratic form 0. *)
Lemma psd_trace0_form d (S : 'M[RR]_d) (v : 'cV[RR]_d) :
  paper_main_psd S -> paper_main_trace S = 0 ->
  paper_main_quadratic_form S v = 0.
Proof.
case=> Ss Sp tr0.
have Ssym : S \is symmetricmx.
  by apply/symmetricmxP/matrixP => i j; rewrite mxE Ss.
have [P Po [dd SE]] := symmetric_spectral Ssym.
have dd0 i : 0 <= dd 0 i.
  move: i; apply/(spectral_psd Po SE) => x; rewrite -quadratic_formE.
  exact: Sp.
have := spectral_trace Po SE; rewrite (_ : \tr S = paper_main_trace S) // tr0.
move=> /esym/eqP h.
have ddz i : dd 0 i = 0.
  move: h; rewrite psumr_eq0; first by move=> j _; exact: dd0.
  by move=> /allP/(_ i (mem_index_enum i))/eqP.
rewrite quadratic_formE (spectral_form _ SE) big1 // => i _.
by rewrite ddz mul0r.
Qed.

(* If some S >= 0 fits the points with value d, then
   universality_fitting_error is at most 0: (d / tr S) S has trace d and
   the constant values d^2 / tr S. *)
Lemma fit_fitting_error n d (x : paper_main_sample n d) : (0 < d)%N ->
  paper_main_fit_event n d x -> universality_fitting_error n d x <= 0.
Proof.
move=> d0 [S [Spsd Sfit]]; rewrite /universality_fitting_error.
apply: ge_inf.
  exists 0 => _ [S' [r [_ [_ [_ ->]]]]].
  by rewrite divr_ge0 ?ler0n // sumr_ge0 // => i _; exact: sqr_ge0.
case: n x Sfit => [|n] x Sfit.
  exists 1%:M, 0; split; first exact: pmh_psd_id.
  by rewrite trace1 big_ord0 mul0r.
have trS : 0 < paper_main_trace S.
  rewrite lt_neqAle pmh_trace_psd_ge0 // andbT eq_sym; apply/eqP => tr0.
  have := Sfit ord0; rewrite psd_trace0_form // => /eqP.
  by rewrite eq_sym pnatr_eq0 => /eqP d00; move: d0; rewrite d00.
set c := d%:R / paper_main_trace S.
have c0 : 0 <= c by rewrite divr_ge0 ?ler0n // ltW.
exists (c *: S), (c * d%:R / Num.sqrt d%:R).
split; first exact: paper_main_psd_scale.
split.
  rewrite /paper_main_trace; under eq_bigr do rewrite mxE.
  by rewrite -mulr_sumr /c -/(paper_main_trace S) mulfVK ?gt_eqF.
split.
  by apply: divr_ge0; [exact: mulr_ge0 c0 (ler0n _ _)|exact: sqrtr_ge0].
rewrite big1 ?mul0r // => i _.
by rewrite paper_main_form_scale Sfit subrr expr0n.
Qed.

(* So the least squares value of the features of a fitted sample is at
   most 0 (unsat_fitting_error of Unsat/LeastSquares). *)
Lemma fit_unsat_value n d (x : paper_main_sample n d) : (0 < d)%N ->
  paper_main_fit_event n d x -> unsat_value n d (unsat_features n d x) <= 0.
Proof.
move=> d0 fx; have := fit_fitting_error n d x d0 fx.
by rewrite unsat_fitting_error // pmulr_rle0.
Qed.

(* 2. From the concentration of the values to the vanishing of the fit
   event. *)

(* The events of a small or of a remote value are measurable. *)
Lemma measurable_unsat_value_lt n d (e : R) :
  measurable [set Z : n.-tuple 'rV[RR]_(d * d) | (unsat_value n d Z < e)%R].
Proof.
have -> : [set Z : n.-tuple 'rV[RR]_(d * d) | (unsat_value n d Z < e)%R] =
    (fun Z => unsat_value n d Z : RR) @^-1` `]-oo, e[%classic.
  by apply/seteqP; split => Z /=; rewrite in_itv.
rewrite -[X in measurable X]setTI.
by apply: measurable_unsat_value => //; exact: measurable_itv.
Qed.

Lemma measurable_unsat_value_far n d (c eps : R) :
  measurable [set Z : n.-tuple 'rV[RR]_(d * d) |
    (eps < `|unsat_value n d Z - c|)%R].
Proof.
apply: (measurable_set_lt (f := fun Z : n.-tuple 'rV[RR]_(d * d) =>
  `|unsat_value n d Z - c| : RR)).
apply: (measurableT_comp (f := fun r : RR => `|r|)) => //.
by apply: measurable_funB => //; exact: measurable_unsat_value.
Qed.

Section concentration.
Local Open Scope ereal_scope.

(* A probability of an event that tends to 0 is eventually below any
   bound. *)
Lemma tends_to0_lt (p : nat -> \bar R) (eps : R) : (0 < eps)%R ->
  (forall d, 0 <= p d) -> paper_main_tends_to p 0 ->
  exists D, forall d, (D <= d)%N -> p d < eps%:E.
Proof.
move=> eps0 p0 hp; have [D hD] := hp _ eps0; exists D => d dD.
by have := hD d dD; rewrite sube0 gee0_abs.
Qed.

(* If the values concentrate around c d and are rarely below e, then
   c d >= e - eps for every large d. *)
Lemma concentration_lower (n : nat -> nat)
    (P : forall d, probability ((n d).-tuple 'rV[RR]_(d * d)%N) RR)
    (c : nat -> R) (e eps : R) : (0 < eps)%R ->
  paper_main_tends_to
    (fun d => P d [set Z | (unsat_value (n d) d Z < e)%R]) 0 ->
  paper_main_tends_to
    (fun d => P d [set Z | (eps < `|unsat_value (n d) d Z - c d|)%R]) 0 ->
  exists D, forall d, (D <= d)%N -> (e - eps <= c d)%R.
Proof.
move=> eps0 h1 h2.
have h0 : (0 < 2^-1 :> RR)%R by rewrite invr_gt0.
have [D1 hD1] := tends_to0_lt _ _ h0 (fun d => measure_ge0 _ _) h1.
have [D2 hD2] := tends_to0_lt _ _ h0 (fun d => measure_ge0 _ _) h2.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
rewrite leNgt; apply/negP => hc.
have m1 := measurable_unsat_value_lt (n d) d e.
have m2 := measurable_unsat_value_far (n d) d (c d) eps.
have cover : [set: (n d).-tuple 'rV[RR]_(d * d)%N] `<=`
    [set Z | (unsat_value (n d) d Z < e)%R] `|`
    [set Z | (eps < `|unsat_value (n d) d Z - c d|)%R].
  move=> Z _; have [h|h] := ltP eps (`|unsat_value (n d) d Z - c d|)%R.
    by right.
  left => /=; move: h; rewrite ler_norml => /andP[_ h].
  by apply: le_lt_trans (_ : c d + eps < e)%R;
    [rewrite -lerBlDl|rewrite -ltrBrDr].
have : P d [set: _] <= P d [set Z | (unsat_value (n d) d Z < e)%R] +
    P d [set Z | (eps < `|unsat_value (n d) d Z - c d|)%R].
  apply: le_trans (measureU2 _ m1 m2).
  by apply: le_measure cover; rewrite inE //; exact: measurableU.
rewrite probability_setT; apply/negP; rewrite -ltNge.
apply: lt_le_trans (lteD (hD1 d d1) (hD2 d d2)) _.
by rewrite -EFinD lee_fin (_ : (2^-1 + 2^-1)%R = 1%R) //; field.
Qed.

(* The fit event vanishes when the values of the data features and of the
   Gaussian features concentrate around the same c d, and the Gaussian
   values are rarely below e > 0. *)
Theorem fit_event_vanishes
    (nu : nat -> nat -> probability (measurableTypeR R) R) (n : nat -> nat)
    (c : nat -> R) (e : R) : (0 < e)%R ->
  paper_main_tends_to (fun d => tuple_prod (fun=> gaussian_feature_law 3%:R d)
    (n d) [set Z | (unsat_value (n d) d Z < e)%R]) 0 ->
  (forall eps : R, (0 < eps)%R -> paper_main_tends_to
    (fun d => tuple_prod (fun=> gaussian_feature_law 3%:R d) (n d)
       [set Z | (eps < `|unsat_value (n d) d Z - c d|)%R]) 0) ->
  (forall eps : R, (0 < eps)%R -> paper_main_tends_to
    (fun d => tuple_prod (fun=> data_feature_law (nu d) d) (n d)
       [set Z | (eps < `|unsat_value (n d) d Z - c d|)%R]) 0) ->
  paper_main_tends_to (fun d => universality_probability (nu d) (n d) d
    (paper_main_fit_event (n d) d)) 0.
Proof.
move=> e0 hg hcg hcd.
pose q := (e / 4%:R)%R.
have q0 : (0 < q)%R by rewrite divr_gt0.
have [D0 hD0] := concentration_lower n _ c e q q0 hg (hcg _ q0).
move=> eps eps0.
have [D1 hD1] := tends_to0_lt _ _ eps0 (fun d => measure_ge0 _ _) (hcd _ q0).
exists (maxn (maxn D0 D1) 1) => d; rewrite !geq_max => /andP[/andP[d0 d1] dp].
rewrite sube0 gee0_abs ?measure_ge0 //; apply: le_lt_trans (hD1 d d1).
rewrite /universality_probability.
(* a fitted sample has features of value 0 < e / 2 *)
pose h := (e / 2%:R)%R.
have mlt := measurable_unsat_value_lt (n d) d h.
apply: le_trans (_ : universality_sample_law (nu d) (n d) d
    (unsat_features (n d) d @^-1` [set Z | (unsat_value (n d) d Z < h)%R])
    <= _).
  apply: le_measure; rewrite ?inE //; first exact: pm_fit_event_measurable.
    rewrite -[X in measurable X]setTI.
    by apply: measurable_unsat_features => //.
  move=> x fx /=; apply: le_lt_trans (fit_unsat_value _ _ _ dp fx) _.
  by rewrite divr_gt0.
(* and a value below e / 2 is farther than e / 4 from c d >= 3 e / 4 *)
rewrite sample_features_law //.
apply: le_measure; rewrite ?inE //; first exact: measurable_unsat_value_far.
move=> Z /= hZ; have := hD0 d d0 => hc.
apply: lt_le_trans (_ : q < c d - unsat_value (n d) d Z)%R _.
  by move: hc hZ; rewrite /q /h; set V := unsat_value _ _ _ => hc hZ; lra.
by rewrite distrC ler_norm.
Qed.

End concentration.

(* 3. The two laws of features at fourth moment 3 are regular with common
   constants, as Corollary 2.13 (ii) (Unsat/Regularized) asks. *)

(* Regularity is monotone in its constants. *)
Lemma regular_feature_le N (K K' tau tau' : R) (S : 'M[RR]_N)
    (mu : probability 'rV[RR]_N RR) :
  0 <= K -> K <= K' -> 0 <= tau -> tau <= tau' ->
  regular_feature K tau S mu -> regular_feature K' tau' S mu.
Proof.
move=> K0 KK t0 tt [l0 F1 m0 cov F2]; split => //.
  move=> th; apply: le_trans (F1 th) _; rewrite lee_fin.
  rewrite ler_wpM2r ?exprn_ge0 ?mxdot_ge0 //.
  rewrite ler_wpM2r ?exprn_ge0 ?opnorm_ge0 //.
  by rewrite lerXn2r // nnegrE // (le_trans K0).
move=> T sT; apply: le_trans (F2 T sT) _; rewrite lee_fin.
rewrite ler_wpM2r ?exprn_ge0 ?frobenius_ge0 //.
by rewrite lerXn2r // nnegrE // (le_trans t0).
Qed.

(* The constants: the maxima of those of Proposition 2.6 (Features/Regular,
   data_feature_regular) and of (2.10) (gaussian_feature_regular). *)
Definition fmt_K (K : R) : R :=
  Num.max (2 ^+ 10 * K ^+ 2 / Num.sqrt (3%:R - 1)) (3 `^ (1 / 4)).

Definition fmt_tau (K : R) (d : nat) : R :=
  Num.max (Num.sqrt (2 ^+ 31 * K ^+ 8 / d%:R))
          (Num.sqrt 2 * opnorm (unsat_cov 3%:R d)).

Lemma fmt_tau_ge0 K d : 0 <= fmt_tau K d.
Proof. by rewrite le_max sqrtr_ge0. Qed.

Lemma fmt_regular_data (K : R) (nu : nat -> probability (measurableTypeR R) R)
    d : (forall j, (j < d)%N -> universality_coordinate_law 3%:R K (nu j)) ->
  (0 < d)%N ->
  regular_feature (fmt_K K) (fmt_tau K d) (unsat_cov 3%:R d)
    (data_feature_law nu d).
Proof.
move=> hnu d0.
have := data_feature_regular 3%:R K d nu hnu (ltr1n _ _) d0.
apply: regular_feature_le; rewrite ?le_max ?lexx ?sqrtr_ge0 //.
apply: divr_ge0; last exact: sqrtr_ge0.
by apply: mulr_ge0; [exact: exprn_ge0 | exact: sqr_ge0].
Qed.

Lemma fmt_regular_gauss (K : R) d : (0 < d)%N ->
  regular_feature (fmt_K K) (fmt_tau K d) (unsat_cov 3%:R d)
    (gaussian_feature_law 3%:R d).
Proof.
move=> d0; have := gaussian_feature_regular 3%:R d (ltr1n _ _) d0.
apply: regular_feature_le; rewrite ?le_max ?lexx ?orbT ?powR_ge0 //.
by rewrite mulr_ge0 ?sqrtr_ge0 ?opnorm_ge0.
Qed.

(* (ln x)^6 <= 720 x for x >= 1, from the exponential series. *)
Lemma ln_pow6_le (x : RR) : 1 <= x -> ln x ^+ 6 <= 720%:R * x.
Proof.
move=> x1; have x0 : 0 < x by apply: lt_le_trans x1.
have := expR_ge1Dxn 5 (ln_ge0 x1); rewrite lnK ?posrE // => h.
have : ln x ^+ 6 / 6`!%:R <= x by apply: le_trans h; rewrite lerDr.
by rewrite ler_pdivrMr ?ltr0n ?fact_gt0 // mulrC.
Qed.

(* ln d >= 1 once d > e. *)
Lemma ln_ge1 (d : nat) : ((archimedean.Num.truncn (expR (1 : RR))).+1 <= d)%N ->
  1 <= ln (d%:R : RR).
Proof.
move=> hd; have h : expR (1 : RR) < d%:R.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
rewrite -[X in X <= _](expRK (1 : RR)) ler_ln ?posrE ?expR_gt0 //.
  exact: lt_trans (expR_gt0 1) h.
exact: ltW.
Qed.

Definition fmt_C0 (K : R) : R :=
  Num.max (Num.sqrt (2 ^+ 31 * K ^+ 8 * 720%:R)) (2 * Num.sqrt 2 * 720%:R).

Lemma fmt_C0_ge0 K : 0 <= fmt_C0 K.
Proof. by rewrite le_max sqrtr_ge0. Qed.

(* fmt_tau K d <= fmt_C0 K / (ln d)^3 for every d > e. *)
Lemma fmt_tau_le (K : R) : exists D : nat, forall d : nat, (D <= d)%N ->
  fmt_tau K d <= fmt_C0 K / ln (d%:R : RR) ^+ 3.
Proof.
exists (archimedean.Num.truncn (expR (1 : RR))).+1 => d hd.
have L1 := ln_ge1 d hd.
have d0 : (0 < d)%N by apply: leq_trans hd.
have dR : (0 : RR) < d%:R by rewrite ltr0n.
set L := ln (d%:R : RR) in L1 *.
have L0 : 0 < L by apply: lt_le_trans L1.
have L3 : 0 < L ^+ 3 by rewrite exprn_gt0.
have h6 : L ^+ 6 <= 720%:R * d%:R by apply: ln_pow6_le; rewrite ler1n.
rewrite /fmt_tau ge_max; apply/andP; split.
  (* the data part: sqrt (a / d) (ln d)^3 <= sqrt (720 a) *)
  rewrite ler_pdivlMr //.
  apply: le_trans (_ : Num.sqrt (2 ^+ 31 * K ^+ 8 * 720%:R) <= _);
    last by rewrite le_max lexx.
  have a0 : (0 : RR) <= 2 ^+ 31 * K ^+ 8.
    apply: mulr_ge0; first exact: exprn_ge0.
    by rewrite (_ : 8 = 4 * 2)%N // exprM sqr_ge0.
  have L3' : 0 <= L ^+ 3 by exact: ltW.
  rewrite -[L ^+ 3](ger0_norm L3') -sqrtr_sqr -sqrtrM ?divr_ge0 ?ler0n //.
  apply: ler_wsqrtr; set a := 2 ^+ 31 * K ^+ 8.
  rewrite -exprM /= -mulrA; apply: ler_wpM2l; first exact: a0.
  by rewrite mulrC ler_pdivrMr.
(* the Gaussian part: sqrt 2 lambda (ln d)^3 <= sqrt 2 (2 / d) 720 d *)
have hl := unsat_lambda_bounds 3%:R d (ltr1n _ _) d0.
have h31 : (3%:R - 1 = 2 :> RR)%R by clear; ring.
move: hl => /andP[_]; rewrite h31 maxxx /unsat_lambda => hl.
rewrite ler_pdivlMr //.
apply: le_trans (_ : 2 * Num.sqrt 2 * 720%:R <= _);
  last by rewrite le_max lexx orbT.
set l := opnorm _ in hl *.
have l0 : 0 <= l by exact: opnorm_ge0.
have L3le : L ^+ 3 <= 720%:R * d%:R.
  apply: le_trans h6.
  rewrite (_ : 6 = 3 + 3)%N // exprD ler_peMr ?exprn_ege1 //.
  exact: ltW.
apply: le_trans (_ : Num.sqrt 2 * l * (720%:R * d%:R) <= _).
  by apply: ler_wpM2l => //; rewrite mulr_ge0 ?sqrtr_ge0.
rewrite (_ : Num.sqrt 2 * l * (720%:R * d%:R) =
  Num.sqrt 2 * 720%:R * (l * d%:R)); first by ring.
rewrite [X in _ <= X](_ : 2 * Num.sqrt 2 * 720%:R =
  Num.sqrt 2 * 720%:R * 2); first by ring.
apply: ler_wpM2l; last exact: hl.
apply: mulr_ge0; [exact: sqrtr_ge0|exact: ler0n].
Qed.

(* The quadratic forms <W, v^T v> of the two features, |v| <= 1, are
   subexponential with the common constant fmt_L0 K / sqrt d, as Lemma 2.12
   (Unsat/Ridge) asks. *)
Definition fmt_L0 (K : R) : R :=
  Num.max (48 * K ^+ 2) (4 * Num.sqrt (3%:R + 1)).

Lemma fmt_subexp_data (K : R) (nu : nat -> probability (measurableTypeR R) R)
    d (v : 'rV[RR]_d) :
  (forall j, (j < d)%N -> universality_coordinate_law 3%:R K (nu j)) ->
  (0 < d)%N -> mxdot v v <= 1 ->
  subexponential (data_feature_law nu d)
    (fun z => mxdot z (mxvec (v^T *m v)) : RR) (fmt_L0 K / Num.sqrt d%:R).
Proof.
move=> hnu d0 v1.
apply: subexponential_le
  (data_feature_quad_subexponential 3%:R K d nu hnu v d0 v1) _.
by rewrite ler_pM2r ?invr_gt0 ?sqrtr_gt0 ?ltr0n // le_max lexx.
Qed.

Lemma fmt_subexp_gauss (K : R) d (v : 'rV[RR]_d) :
  (0 < d)%N -> mxdot v v <= 1 ->
  subexponential (gaussian_feature_law 3%:R d)
    (fun z => mxdot z (mxvec (v^T *m v)) : RR) (fmt_L0 K / Num.sqrt d%:R).
Proof.
move=> d0 v1.
apply: subexponential_le
  (gaussian_feature_quad_subexponential 3%:R d v (ler1n _ _) d0 v1) _.
by rewrite ler_pM2r ?invr_gt0 ?sqrtr_gt0 ?ltr0n // le_max lexx orbT.
Qed.
