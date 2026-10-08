(* The unsatisfiable phase for every fourth moment kappa > 1: Theorem 1.7
   and the second conjunct of Theorem 1.2 (ii) of Koehler and Sohn (arXiv
   2608.27372, lines 1602-1635 of arxiv_v1.tex), at Stdlib's R. It is item
   U10 of stage 2 of phase 5 (AGENTS.md), after the stage 1 theorem at
   kappa = 3 (Unsat/FourthMomentThree). For kappa > 1, alpha > 0, every
   family nu of laws with universality_coordinate_law kappa K (nu d j) for
   j < d, and every n with universality_density_tends_to n alpha:

   1. The two laws of features, data_feature_law (nu d) d and
      gaussian_feature_law kappa d, are regular features with the common
      constants uni_K and uni_tau d (uni_regular_data, uni_regular_gauss,
      from data_feature_regular and gaussian_feature_regular of
      Features/Regular), with uni_tau d <= uni_C0 / (ln d)^3 for d > e
      (uni_tau_le), and their quadratic forms <W, v^T v>, |v| <= 1, are
      subexponential with constant uni_L0 / sqrt d (uni_subexp_data,
      uni_subexp_gauss). So Corollary 2.13 (ii) (unsat_value_concentration_law
      of Unsat/Regularized) applies: the values of both laws concentrate
      around the center uni_center of the Gaussian features
      (uni_concentration). This is the construction of FourthMomentThree
      with kappa in place of 3.
   2. gaussian_value_limit is Proposition 1.4 (ii) in the form that
      Gaussian/Limit (item G8, lane C) announces: 2 unsat_value of the
      Gaussian features tends to e*(alpha, kappa) in probability. Under it:
      - uni_center_limit: 2 uni_center (n d) d tends to e*(alpha, kappa),
        since the Gaussian values concentrate around the center and have
        e* as limit;
      - universality_error_cvg, Theorem 1.7: the optimal squared fitting
        error, which is 2 unsat_value of the features for d >= 1
        (unsat_fitting_error of Unsat/LeastSquares), tends to
        e*(alpha, kappa) in probability under the sample law
        (sample_features_law of Model/Rows);
      - universality_unsat_of_gaussian: the second conjunct of
        universality_statement for alpha > alpha*(kappa): e* > 0
        (universality_e_star_gt0 of Gaussian/Threshold), the events are
        measurable (pm_fit_event_measurable, measurable_error_event of
        Model/Measurability), a fit makes the fitting error at most 0
        (fit_fitting_error of Unsat/FourthMomentThree) and so lies in the
        error event at e* / 2, and the error events vanish by Theorem 1.7.
   What remains for the stage 2 theorem is gaussian_value_limit itself,
   from Lemma 5.16 and Proposition 5.15 (Gaussian/Limit). *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.probability Require Import lindeberg subgaussian.
From GaussianAnalysis.convex Require Import least_squares ridge_comparison.
From EllipsoidFitting Require Import PaperMainDefinitions Measurability.Fit.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares Regularized.
From EllipsoidUniversality.Unsat Require Import FourthMomentThree.
From EllipsoidUniversality.Gaussian Require Import Threshold.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Model Require Import Rows Measurability.
Import GRing.Theory Num.Theory Order.TTheory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. The two laws of features are regular with common constants for every
   kappa > 1, as Corollary 2.13 (ii) (Unsat/Regularized) asks; the same
   construction as for kappa = 3 in Unsat/FourthMomentThree. *)

Section constants.
Variables (kappa K : R).
Hypothesis k1 : 1 < kappa.

Definition uni_K : R :=
  Num.max (2 ^+ 10 * K ^+ 2 / Num.sqrt (kappa - 1)) (3 `^ (1 / 4)).

Definition uni_tau (d : nat) : R :=
  Num.max (Num.sqrt (2 ^+ 31 * K ^+ 8 / d%:R))
          (Num.sqrt 2 * opnorm (unsat_cov kappa d)).

Definition uni_C0 : R :=
  Num.max (Num.sqrt (2 ^+ 31 * K ^+ 8 * 720%:R))
          (Num.sqrt 2 * Num.max 2 (kappa - 1) * 720%:R).

Definition uni_L0 : R := Num.max (48 * K ^+ 2) (4 * Num.sqrt (kappa + 1)).

Lemma uni_tau_ge0 d : 0 <= uni_tau d.
Proof. by rewrite le_max sqrtr_ge0. Qed.

Lemma uni_K_gt0 : 0 < uni_K.
Proof. by rewrite lt_max powR_gt0 ?orbT. Qed.

Lemma uni_C0_ge0 : 0 <= uni_C0.
Proof. by rewrite le_max sqrtr_ge0. Qed.

Lemma uni_L0_gt0 : 0 < uni_L0.
Proof.
rewrite /uni_L0 lt_max; apply/orP; right; rewrite mulr_gt0 // sqrtr_gt0.
by apply: addr_gt0 => //; exact: lt_trans ltr01 k1.
Qed.

Lemma uni_regular_data (nu : nat -> probability (measurableTypeR R) R) d :
  (forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j)) ->
  (0 < d)%N ->
  regular_feature uni_K (uni_tau d) (unsat_cov kappa d) (data_feature_law nu d).
Proof.
move=> hnu d0; have := data_feature_regular kappa K d nu hnu k1 d0.
apply: regular_feature_le; rewrite ?le_max ?lexx ?sqrtr_ge0 //.
apply: divr_ge0; last exact: sqrtr_ge0.
by apply: mulr_ge0; [exact: exprn_ge0 | exact: sqr_ge0].
Qed.

Lemma uni_regular_gauss d : (0 < d)%N ->
  regular_feature uni_K (uni_tau d) (unsat_cov kappa d)
    (gaussian_feature_law kappa d).
Proof.
move=> d0; have := gaussian_feature_regular kappa d k1 d0.
apply: regular_feature_le; rewrite ?le_max ?lexx ?orbT ?powR_ge0 //.
by rewrite mulr_ge0 ?sqrtr_ge0 ?opnorm_ge0.
Qed.

(* uni_tau d <= uni_C0 / (ln d)^3 for every d > e. *)
Lemma uni_tau_le : exists D : nat, forall d : nat, (D <= d)%N ->
  uni_tau d <= uni_C0 / ln (d%:R : RR) ^+ 3.
Proof.
exists (archimedean.Num.truncn (expR (1 : RR))).+1 => d hd.
have L1 := ln_ge1 d hd.
have d0 : (0 < d)%N by apply: leq_trans hd.
have dR : (0 : RR) < d%:R by rewrite ltr0n.
set L := ln (d%:R : RR) in L1 *.
have L0 : 0 < L by apply: lt_le_trans L1.
have L3 : 0 < L ^+ 3 by rewrite exprn_gt0.
have h6 : L ^+ 6 <= 720%:R * d%:R by apply: ln_pow6_le; rewrite ler1n.
rewrite /uni_tau ge_max; apply/andP; split.
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
have hl := unsat_lambda_bounds kappa d k1 d0.
move: hl => /andP[_]; rewrite /unsat_lambda => hl.
rewrite ler_pdivlMr //.
apply: le_trans (_ : Num.sqrt 2 * Num.max 2 (kappa - 1) * 720%:R <= _);
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
rewrite [X in _ <= X](_ : Num.sqrt 2 * Num.max 2 (kappa - 1) * 720%:R =
  Num.sqrt 2 * 720%:R * Num.max 2 (kappa - 1)); first by ring.
apply: ler_wpM2l; last exact: hl.
apply: mulr_ge0; [exact: sqrtr_ge0|exact: ler0n].
Qed.

Lemma uni_subexp_data (nu : nat -> probability (measurableTypeR R) R)
    d (v : 'rV[RR]_d) :
  (forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j)) ->
  (0 < d)%N -> mxdot v v <= 1 ->
  subexponential (data_feature_law nu d)
    (fun z => mxdot z (mxvec (v^T *m v)) : RR) (uni_L0 / Num.sqrt d%:R).
Proof.
move=> hnu d0 v1.
apply: subexponential_le
  (data_feature_quad_subexponential kappa K d nu hnu v d0 v1) _.
by rewrite ler_pM2r ?invr_gt0 ?sqrtr_gt0 ?ltr0n // le_max lexx.
Qed.

Lemma uni_subexp_gauss d (v : 'rV[RR]_d) :
  (0 < d)%N -> mxdot v v <= 1 ->
  subexponential (gaussian_feature_law kappa d)
    (fun z => mxdot z (mxvec (v^T *m v)) : RR) (uni_L0 / Num.sqrt d%:R).
Proof.
move=> d0 v1.
apply: subexponential_le
  (gaussian_feature_quad_subexponential kappa d v (ltW k1) d0 v1) _.
by rewrite ler_pM2r ?invr_gt0 ?sqrtr_gt0 ?ltr0n // le_max lexx orbT.
Qed.

(* The center of the Gaussian features. *)
Definition uni_center (n d : nat) : R :=
  unsat_center kappa n d (gaussian_feature_law kappa d)
    (unsat_beta d) (unsat_gamma d).

(* Corollary 2.13 (ii): the values of features with these constants
   concentrate around the center of the Gaussian features. *)
Lemma uni_concentration (alpha : R) (n : nat -> nat)
    (rho : forall d, probability 'rV[RR]_(d * d) RR) :
  0 < alpha -> universality_density_tends_to n alpha ->
  (forall d, (0 < d)%N ->
     regular_feature uni_K (uni_tau d) (unsat_cov kappa d) (rho d)) ->
  (forall d (v : 'rV[RR]_d), (0 < d)%N -> mxdot v v <= 1 ->
     subexponential (rho d) (fun z => mxdot z (mxvec (v^T *m v)) : RR)
       (uni_L0 / Num.sqrt d%:R)) ->
  forall eps : R, 0 < eps ->
    paper_main_tends_to (fun d => tuple_prod (fun=> rho d) (n d)
      [set Z | eps < `|unsat_value (n d) d Z - uni_center (n d) d|]) 0.
Proof.
move=> a0 hn hreg hsub.
exact: (unsat_value_concentration_law kappa alpha uni_K uni_C0 uni_L0 n rho
  (gaussian_feature_law kappa) uni_tau k1 a0 uni_K_gt0 uni_C0_ge0 uni_L0_gt0
  hn hreg uni_regular_gauss hsub uni_tau_ge0 uni_tau_le).
Qed.

End constants.


(* 2. Theorem 1.7 and the unsatisfiable phase, from Proposition 1.4 (ii). *)

Section universality.
Variables (kappa K alpha : R).
Hypotheses (k1 : 1 < kappa) (a0 : 0 < alpha).

Local Notation e := (universality_e_star alpha kappa).

(* Proposition 1.4 (ii) in the form that extension/Gaussian/Limit.v (item
   G8, lane C) announces: the value 2 unsat_value of the Gaussian features
   tends to e*(alpha, kappa) in probability. *)
Definition gaussian_value_limit : Prop :=
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
    [set Z | eps < `|2 * unsat_value (n d) d Z - e|] `<=` E].

Hypothesis hG : gaussian_value_limit.

(* Twice the center of the Gaussian features tends to e. *)
Lemma uni_center_limit (n : nat -> nat) :
  universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    `|2 * uni_center kappa (n d) d - e| <= eps.
Proof.
move=> hn eps eps0.
have e4 : 0 < eps / 4 by rewrite divr_gt0 // ltr0n.
pose q := Num.min (eps / 4) (1 / 4).
have q0 : 0 < q by rewrite lt_min e4 divr_gt0 // ltr0n.
have qe : q <= eps / 4 by rewrite ge_min lexx.
have q4 : q <= 1 / 4 by rewrite ge_min lexx orbT.
have [D1 hD1] := hG n hn q q0.
have hc := @uni_concentration kappa K k1 alpha n (gaussian_feature_law kappa)
  a0 hn (uni_regular_gauss kappa K k1)
  (fun d v d0 v1 => uni_subexp_gauss kappa K k1 d v d0 v1) (eps / 4)%R e4.
have h2 : (0 < 2^-1 :> RR) by rewrite invr_gt0.
have [D2 hD2] := tends_to0_lt _ _ h2 (fun d => measure_ge0 _ _) hc.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have [E [mE PE sub]] := hD1 d d1.
rewrite leNgt; apply/negP => hfar.
set c := uni_center kappa (n d) d in hfar.
have mF := measurable_unsat_value_far (n d) d c (eps / 4)%R.
have cover : [set: (n d).-tuple 'rV[RR]_(d * d)] `<=`
    E `|` [set Z | eps / 4 < `|unsat_value (n d) d Z - c|].
  move=> Z _; have [h|h] := ltP (eps / 4) (`|unsat_value (n d) d Z - c|).
    by right.
  left; apply: sub => /=; set u := unsat_value (n d) d Z in h *.
  have t := ler_normD (2 * c - 2 * u) (2 * u - e).
  rewrite (_ : 2 * c - 2 * u + (2 * u - e) = 2 * c - e) in t; first by ring.
  have tu : `|2 * c - 2 * u| = 2 * `|u - c|.
    by rewrite -mulrBr normrM gtr0_norm ?ltr0n // distrC.
  rewrite tu in t; move: hfar t h qe.
  move: (`|2 * c - e|) (`|2 * u - e|) (`|u - c|) => a b f; lra.
have : (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) [set: _] <=
    tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E +
    tuple_prod (fun=> gaussian_feature_law kappa d) (n d)
      [set Z | (eps / 4 < `|unsat_value (n d) d Z - c|)%R])%E.
  apply: (le_trans _ (measureU2 _ mE mF)).
  by apply: le_measure cover; rewrite inE //; exact: measurableU.
rewrite probability_setT; apply/negP; rewrite -ltNge.
apply: le_lt_trans (leeD PE (ltW (hD2 d d2))) _.
by rewrite -EFinD lte_fin; lra.
Qed.

(* Theorem 1.7: the optimal squared fitting error tends to e*(alpha, kappa)
   in probability, for every family of coordinate laws. *)
Theorem universality_error_cvg
    (nu : nat -> nat -> probability (measurableTypeR R) R) :
  (forall d j : nat, (j < d)%N ->
     universality_coordinate_law kappa K (nu d j)) ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps ->
    paper_main_tends_to (fun d => universality_probability (nu d) (n d) d
      (universality_error_event (n d) d e eps)) 0.
Proof.
move=> hnu n hn eps eps0.
have e2 : 0 < eps / 2 by rewrite divr_gt0 // ltr0n.
have e4 : 0 < eps / 4 by rewrite divr_gt0 // ltr0n.
have [D0 hD0] := uni_center_limit n hn (eps / 2)%R e2.
have hcd := @uni_concentration kappa K k1 alpha n
  (fun d => data_feature_law (nu d) d) a0 hn
  (fun d d0 => uni_regular_data kappa K k1 (nu d) d (fun j jd => hnu d j jd) d0)
  (fun d v d0 v1 => uni_subexp_data kappa K (nu d) d v
     (fun j jd => hnu d j jd) d0 v1) (eps / 4)%R e4.
move=> eta eta0.
have [D1 hD1] := tends_to0_lt _ _ eta0 (fun d => measure_ge0 _ _) hcd.
exists (maxn (maxn D0 D1) 1) => d; rewrite !geq_max => /andP[/andP[d0 d1] dp].
rewrite sube0 gee0_abs ?measure_ge0 //; apply: le_lt_trans (hD1 d d1).
rewrite /universality_probability.
set c := uni_center kappa (n d) d.
have mfar := measurable_unsat_value_far (n d) d c (eps / 4)%R.
apply: le_trans (_ : (universality_sample_law (nu d) (n d) d
    (unsat_features (n d) d @^-1`
      [set Z | (eps / 4 < `|unsat_value (n d) d Z - c|)%R]) <= _)%E).
  apply: le_measure; rewrite ?inE //; first exact: measurable_error_event.
    rewrite -[X in measurable X]setTI.
    by apply: measurable_unsat_features => //.
  move=> x /=; rewrite /universality_error_event /= unsat_fitting_error //.
  set u := unsat_value (n d) d (unsat_features (n d) d x) => hx.
  have hc := hD0 d d0; rewrite -/c in hc.
  have t := ler_normD (2 * u - 2 * c) (2 * c - e).
  rewrite (_ : 2 * u - 2 * c + (2 * c - e) = 2 * u - e) in t; first by ring.
  have tu : `|2 * u - 2 * c| = 2 * `|u - c|.
    by rewrite -mulrBr normrM gtr0_norm ?ltr0n.
  rewrite tu in t; move: hx t hc.
  move: (`|2 * u - e|) (`|u - c|) (`|2 * c - e|) => a b f; lra.
by rewrite sample_features_law.
Qed.

(* The second conjunct of universality_statement (Theorem 1.2 (ii)), given
   Proposition 1.4 (ii). *)
Theorem universality_unsat_of_gaussian : universality_alpha_star kappa < alpha ->
  0 < e /\
  (forall n d : nat, measurable (paper_main_fit_event n d)) /\
  (forall (n d : nat) (eps : R), measurable (universality_error_event n d e eps)) /\
  (forall nu : nat -> nat -> probability (measurableTypeR R) R,
    (forall d j : nat, (j < d)%N -> universality_coordinate_law kappa K (nu d j)) ->
    forall n : nat -> nat, universality_density_tends_to n alpha ->
      paper_main_tends_to
        (fun d => universality_probability (nu d) (n d) d
                    (paper_main_fit_event (n d) d)) 0 /\
      forall eps : R, 0 < eps ->
        paper_main_tends_to
          (fun d => universality_probability (nu d) (n d) d
                      (universality_error_event (n d) d e eps)) 0).
Proof.
move=> ha; have e0 : 0 < e by rewrite universality_e_star_gt0.
split => //; split; first by move=> n d; exact: pm_fit_event_measurable.
split; first by move=> n d eps; exact: measurable_error_event.
move=> nu hnu n hn; split; last exact: universality_error_cvg nu hnu n hn.
have e2 : 0 < e / 2 by rewrite divr_gt0 // ltr0n.
have h := universality_error_cvg nu hnu n hn (e / 2)%R e2.
move=> eta eta0; have [D hD] := h eta eta0.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD dp].
apply: le_lt_trans (hD d dD).
rewrite !sube0 !gee0_abs ?measure_ge0 //.
apply: le_measure; rewrite ?inE //; first exact: pm_fit_event_measurable.
  exact: measurable_error_event.
move=> x fx; have := fit_fitting_error (n d) d x dp fx.
rewrite /universality_error_event /=.
move: (universality_fitting_error (n d) d x) => g g0.
rewrite distrC ger0_norm; first by rewrite subr_ge0 (le_trans g0) // ltW.
by move: g0 e0; lra.
Qed.

End universality.
