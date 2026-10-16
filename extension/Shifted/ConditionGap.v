(* Retaining the squared loss in the condition-number UNSAT comparison.
   Source: doc/shifted-gaussian.tex, the small-shift upper-threshold proof.
   This module extends the supporting inequalities of Condition/Unsat.v
   without changing its theorem or any frozen definition. The objective
   estimate holds for approximate fits, and the empirical-mean bound does
   not require an exact fit. *)

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
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.
From EllipsoidFitting Require Import Measurability.Fit Measurability.Balanced.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
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

From EllipsoidUniversality.Condition Require Import Unsat Curve GaussianCone GaussianGap.
From EllipsoidUniversality.Shifted Require Import GaussianInputs.
From EllipsoidUniversality.Gaussian Require Import Representation.

Lemma af_value_residual (kappa m M : R) (d n : nat) (beta gamma : R)
    (Z : n.-tuple 'rV[RR]_(d * d)) (S : 'M[R]_d) (b0 : R) :
  1 < kappa -> (0 < d)%N -> 0 < m -> m < 1 < M -> 0 < beta -> 0 < gamma ->
  pd_slice2 d m M (mxvec S) ->
  af_value kappa m M d n beta gamma Z <=
    (n%:R *+ 2)^-1 *
      \sum_(i < n) (b0 - mxdot (tnth Z i) (mxvec S)) ^+ 2 +
    beta * (af_Mk kappa * M + b0 ^+ 2) +
    gamma * logdet_barrier2 d m M (mxvec S).
Proof.
move=> k1 d0 m0 mM b0' g0 DS.
have l0 := af_lam_gt0 kappa d k1 d0.
rewrite /af_value (sat_valueE m M d n _ beta gamma mM l0 b0' g0).
apply: le_trans (sat_minP m M d n _ beta gamma mM l0 b0' g0 predT Z
  (mxvec S) b0 DS) _.
rewrite /sat_obj /ls_barrier_objective /ls_ridge /ls_loss.
rewrite lerD2r lerD2l.
apply: ler_wpM2l; first exact: ltW.
rewrite lerD2r.
have hF := slice2_frobenius d m M (mxvec S) (ltW m0) DS.
have hl := af_lam_le kappa d k1 d0.
have M0 : 0 < M by case/andP: mM => _ /(lt_trans ltr01).
apply: le_trans (ler_wpM2l (ltW l0) hF) _.
rewrite mulrCA [af_Mk kappa * M]mulrC; apply: ler_wpM2l; first exact: ltW.
exact: hl.
Qed.

Definition sample_feature_mean N d (x : paper_main_sample N d)
    (S : 'M[R]_d) : R :=
  mxdot (sample_adj x (const_mx N%:R^-1)) S.

Lemma sample_feature_meanE N d (x : paper_main_sample N d) (S : 'M[R]_d) :
  sample_feature_mean N d x S =
    N%:R^-1 * \sum_(i < N) mxdot (sample_W x i) S.
Proof.
rewrite /sample_feature_mean /sample_adj /coef_adj mxdot_suml mulr_sumr.
by apply: eq_bigr => i _; rewrite mxdotZl mxE.
Qed.

Lemma sample_feature_mean_le N d (x : paper_main_sample N d)
    (S : 'M[R]_d) (c : R) :
  (0 < N)%N ->
  (forall z : 'rV[R]_N, frobenius (sample_adj x z) <= c * frobenius z) ->
  `|sample_feature_mean N d x S| <= c / Num.sqrt N%:R * frobenius S.
Proof.
move=> N0 hc; rewrite /sample_feature_mean.
apply: le_trans (mxdot_le _ _) _.
apply: ler_wpM2r; first exact: frobenius_ge0.
by have := hc (const_mx N%:R^-1); rewrite frobenius_const_row.
Qed.


Lemma sample_feature_mean_min N d (x : paper_main_sample N d)
    (S : 'M[R]_d) (b : R) : (0 < N)%N ->
  \sum_(i < N) (sample_feature_mean N d x S - mxdot (sample_W x i) S) ^+ 2 <=
  \sum_(i < N) (b - mxdot (sample_W x i) S) ^+ 2.
Proof.
move=> N0.
pose v : 'rV[R]_N := \row_i mxdot (sample_W x i) S.
have hm : (\sum_(i < N) v 0 i) / N%:R = sample_feature_mean N d x S.
  rewrite sample_feature_meanE /v.
  under eq_bigr do rewrite mxE.
  by rewrite mulrC.
have h := centered_sq_le N v b N0.
rewrite (centered_sqE N v N0) hm in h.
move: h; rewrite /v.
under [X in X <= _]eq_bigr do rewrite mxE.
by under [X in _ <= X]eq_bigr do rewrite mxE.
Qed.

Lemma cond_residual_arith (v c e t bs u g bar loss : R) : 0 < g ->
  c - (e + t) <= v -> g / 4 <= c -> e <= bs / 8 -> t = bs / 8 ->
  bs <= g / 32 -> v <= loss + u + bar -> u <= g / 32 ->
  bar <= g / 32 -> g / 8 <= loss.
Proof. by move=> g0 h1 h2 h3 h4 h5 h6 h7 h8; lra. Qed.

(* The exceptional set is independent of the candidate matrix and of the
   intercept. This is the quantitative consequence needed for shifted
   samples, whereas the frozen theorem only records nonexistence. *)
Theorem condition_residual_gap (K C Cp alpha g : R) :
  0 < K -> 1 < C -> C < Cp -> 0 < alpha -> 0 < g ->
  (forall n : nat -> nat, universality_density_tends_to n alpha ->
   forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
   exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
     (tuple_prod (fun=> gaussian_feature_law 3%:R d) (n d) E <= eps%:E)%E &
     forall Z, ~ E Z -> forall S : 'M[R]_d, cond_slice Cp S -> forall b : R,
       g * (n d)%:R <= \sum_(i < n d) (b - mxdot (tnth Z i) (mxvec S)) ^+ 2]) ->
  forall (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment 3%:R N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (mixture_probability (N d) (w d) (mu d) (n d) d E <= eps%:E)%E &
    forall x, ~ E x -> forall S : 'M[R]_d, cond_slice C S -> forall b : R,
      g / 4 * (n d)%:R <=
        \sum_(i < n d) (b - mxdot (sample_W x i) S) ^+ 2].
Proof.
move=> K0 C1 CCp a0 g0 hgap N w mu hfam h4 n hn.
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
      forall x, ~ B0 x -> forall S : 'M[R]_d, cond_slice C S -> forall b : R,
        g / 4 * (n d)%:R <=
          \sum_(i < n d) (b - mxdot (sample_W x i) S) ^+ 2].
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
  move=> x hno R hR b1.
  have nFU : ~ FU x by move=> h; apply: hno; left.
  have nEm : ~ Em x by move=> h; apply: hno; right.
  pose b0 := sample_feature_mean (n d) d x R.
  have [j0 jJ [hj hBar]] := hcov d R d0 hR.
  pose j := Ordinal jJ.
  have hj' : pd_slice2 d (a' j) (b' j) (mxvec R) := hj.
  pose W := unsat_features (n d) d x.
  pose loss := \sum_(i < n d) (b0 - mxdot (sample_W x i) R) ^+ 2.
  have lossW : \sum_(i < n d) (b0 - mxdot (tnth W i) (mxvec R)) ^+ 2 = loss.
    by apply: eq_bigr => i _; rewrite /W -mxvec_sample_W mxdot_mxvec.
  have hup := af_value_residual 3%:R (a' j) (b' j) d (n d) (bs j)
    (af_gam d) W R b0 k1 d0 (a'0 j) (a'b' j) (bs0 j) g1 hj'.
  rewrite lossW in hup.
  have hb := sample_feature_mean_le (n d) d x R (Ca * Num.sqrt d%:R) n0
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
  have hraw : g / 8 <= ((n d)%:R *+ 2)^-1 * loss.
    exact: (cond_residual_arith _ _ _ _ _ _ _ _ _ g0 hlo (hcen j) herr
      erefl (hbs2 j) hup hu hbar).
  have hscaled : g / 4 * (n d)%:R <= loss.
    have hn2 : (0 : RR) < (n d)%:R *+ 2 by rewrite mulrn_wgt0.
    have heq : g / 4 * (n d)%:R = g / 8 * ((n d)%:R *+ 2).
      by rewrite -mulr_natr; field.
    rewrite heq -ler_pdivlMr //.
    by rewrite [loss / _]mulrC.
  apply: le_trans hscaled _.
  exact: (sample_feature_mean_min (n d) d x R b1 n0).
move=> eps ep0.
have [D hD] := key eps ep0.
exists D => d dD.
have [E [mE PE hE]] := hD d dD.
by exists E; split; [exact: mE | rewrite mixPE | exact: hE].
Qed.


Corollary gaussian_condition_residual_gap (C alpha : R) :
  1 < C -> 0 < alpha -> condition_alpha C < alpha ->
  exists eta : R, 0 < eta /\
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (gaussian_product_law (n d * d) E <= eps%:E)%E &
    forall x, ~ E x -> forall S : 'M[R]_d, cond_slice C S -> forall b : R,
      eta * (n d)%:R <=
        \sum_(i < n d) (b - mxdot (sample_W x i) S) ^+ 2].
Proof.
move=> C1 a0 aC.
have [Cp CCp aCp] := condition_alpha_right _ _ C1 aC.
have Cp1 := lt_trans C1 CCp.
have [g [g0 hgap]] := gaussian_gap Cp alpha Cp1 a0 aCp
  (cond_support_goe_cvg Cp Cp1).
exists (g / 4); split; first by rewrite divr_gt0 // ltr0n.
move=> n hn eps ep0.
have K0 : (0 : R) < 2%:R by rewrite ltr0n.
have [D hD] := condition_residual_gap 2%:R C Cp alpha g K0 C1 CCp a0 g0
  hgap (fun=> 1%N) (fun _ _ => 1) (fun _ _ _ => gaussian_law_probability)
  gaussian_mixture_family gaussian_mixture_fourth_moment n hn eps ep0.
exists D => d dD.
have [E [mE PE hE]] := hD d dD.
rewrite gaussian_mixture_probability in PE.
by exists E; split.
Qed.
