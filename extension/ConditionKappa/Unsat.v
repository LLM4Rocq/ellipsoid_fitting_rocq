(* The unsatisfiable half of the threshold at fourth moment kappa, for
   finite mixtures of product laws, at Stdlib's R: item D2 of phase 11
   (notes/phase11-plan.md, sections 3.4, 5 and 6; lane B). The model is
   Condition/Unsat.v, which treats kappa = 3; Condition/Cover.v and
   Condition/Slices.v are reused as they are.

   Result to prove here: for K > 0, kappa > 1, C > 1 and
   alpha(C, kappa) < alpha, every finite mixture family with
   mixture_family K N w mu and mixture_fourth_moment kappa N w mu, and every
   n with n/d^2 -> alpha, the probability of
   universality_conditioned_fit_event (n d) d C tends to 0. This covers
   every alpha > alpha(C, kappa), alpha >= 1/2 included.

   Interfaces used.
   - I3, from item S3 (Curve, lane C): the analogue of condition_alpha_right
     of Condition/Curve.v for alpha(C, kappa), which gives some Cp > C with
     alpha(Cp, kappa) < alpha.
   - I4 (the gap), from item G1 (GaussianGap), at Cp: the hypothesis of
     condition_unsat_gap of Condition/Unsat.v with
     gaussian_feature_law kappa d, uniform in the intercept; see the header
     of GaussianGap. Until G1 lands, the first conditional lemma takes it
     as a hypothesis.
   Constants by their role, as in Sat: the regularity constant of the
   mixture features depends on kappa, the 3^(1/4) of the Gaussian
   regularity bound does not.

   Proved.
   1. condition_kappa_unsat_gap: condition_unsat_gap of Condition/Unsat.v
      at fourth moment kappa. Its proof is that of Condition/Unsat.v with
      kappa in place of 3: the slices of Condition/Slices.v and Theorem 2.9
      at kappa, the regularity of the mixture features with
      Kf = 2^10 K^2 / sqrt (kappa - 1) and of the Gaussian features with
      3^(1/4), the a priori estimate mixture_adjoint_bound, and interface
      I4 (the gap at Cp) for the Gaussian features of
      gaussian_feature_law kappa d.
   2. condition_kappa_unsat: the result above, from interface I3 (the
      analogue of condition_alpha_right) and interface I1 for every
      C' > 1, through gaussian_kappa_gap (GaussianGap, item G1) at Cp. Both
      interfaces are explicit hypotheses until items S3 and M5 land. *)

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
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.matrix Require Import nuclear condition_cone.
From GaussianAnalysis.probability Require Import lindeberg subgaussian mixture.
From GaussianAnalysis.convex Require Import logdet_barrier least_squares.
From GaussianAnalysis.convex Require Import ridge_comparison.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import Measurability.Fit Measurability.Balanced.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
From EllipsoidUniversality.Features Require Import Definitions Regular Mixture.
From EllipsoidUniversality.Model Require Import Rows Measurability.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Unsat Require Import FourthMomentThree.
From EllipsoidUniversality.Sat Require Import Apriori ApproximateFit.
From EllipsoidUniversality.Sat Require Import Universality.
From EllipsoidUniversality.Gaussian Require Import InProbability.
From EllipsoidUniversality.Mixture Require Import Flat.
From EllipsoidUniversality.Condition Require Import Slices Cover Sat Unsat.
From EllipsoidUniversality.ConditionKappa Require Import Cone GaussianGap.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. The unsatisfiable half from the Gaussian gap on the trace slice of
   the cone of condition number Cp > C, at fourth moment kappa. *)

Theorem condition_kappa_unsat_gap (K kappa C Cp alpha : R) :
  0 < K -> 1 < kappa -> 1 < C -> C < Cp -> 0 < alpha ->
  (exists g : R, 0 < g /\
   forall n : nat -> nat, universality_density_tends_to n alpha ->
   forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
   exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
     (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
     forall Z, ~ E Z -> forall S : 'M[R]_d, cond_slice Cp S -> forall b : R,
       g * (n d)%:R <= \sum_(i < n d) (b - mxdot (tnth Z i) (mxvec S)) ^+ 2]) ->
  forall (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  paper_main_tends_to
    (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                (universality_conditioned_fit_event (n d) d C)) 0.
Proof.
move=> K0 k1 C1 CCp a0 [g [g0 hgap]] N w mu hfam h4 n hn.
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
pose Kf : RR := 2 ^+ 10 * K ^+ 2 / Num.sqrt (kappa - 1).
have Kf0 : 0 <= Kf.
  by rewrite /Kf divr_ge0 ?sqrtr_ge0 // mulr_ge0 // exprn_even_ge0.
pose tau d : RR := Num.sqrt (2 ^+ 31 * K ^+ 8 / d%:R + 16 * K ^+ 8 / d%:R).
pose Kg := Num.max Kf (3 `^ (1 / 4)).
pose taug d := Num.max (tau d) (Num.sqrt 2 * opnorm (unsat_cov kappa d)).
have hreg d : (0 < d)%N -> regular_feature Kg (taug d) (unsat_cov kappa d)
    (mix_feature_law K N w mu hfam d).
  move=> d0; apply: regular_feature_le
    (mix_feature_regular K N w mu hfam kappa h4 d k1 d0);
    by rewrite ?le_max ?lexx ?sqrtr_ge0.
have hG d : (0 < d)%N -> regular_feature Kg (taug d) (unsat_cov kappa d)
    (gaussian_feature_law kappa d).
  move=> d0; apply: regular_feature_le
    (gaussian_feature_regular kappa d k1 d0);
    rewrite ?le_max ?lexx ?orbT ?powR_ge0 //.
  by rewrite mulr_ge0 ?sqrtr_ge0 ?opnorm_ge0.
have taug0 d : 0 <= taug d by rewrite le_max sqrtr_ge0.
have htaug (eta : RR) : 0 < eta -> af_eventually (fun d => taug d <= eta).
  move=> eta0.
  have [D1 h1] := mix_tau_small K eta eta0.
  have [D2 h2] := af_ev_gauss_tau kappa eta k1 eta0.
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
  pose bs j := sl_beta kappa (b' j) delta.
  pose ts j := sl_t kappa (b' j) delta.
  pose etas j := sl_eta kappa Kg (b' j) delta.
  pose P1s j := sl_P1 kappa Kg (b' j) delta.
  pose epsQ : RR := eps / 2 / J.+1%:R.
  have bs0 j : 0 < bs j := sl_beta_gt0 kappa (a' j) (b' j) (a'b' j) delta dl0.
  have ts0 j : 0 < ts j := sl_t_gt0 kappa (a' j) (b' j) (a'b' j) delta dl0.
  have etas0 j : 0 < etas j.
    exact: (sl_eta_gt0 kappa Kg (a' j) (b' j) (a'b' j) delta dl0).
  have te j : 0 < (kappa - 1) * alpha * etas j / 4.
    by rewrite divr_gt0 // mulr_gt0 // mulr_gt0 // subr_gt0.
  have Mk2 : 2 <= af_Mk kappa by rewrite /af_Mk le_max lexx.
  have hbs j : bs j * (af_Mk kappa * b' j + cb * b' j) <= g / 32.
    apply: le_trans (cond_beta_bound (af_Mk kappa) (b' j) cb delta Mk2 (b'0 j)
      cb0 dl0) _.
    have c1 : 1 + cb != 0 := lt0r_neq0 c1p.
    by rewrite /delta le_eqVlt; apply/orP; left; apply/eqP; field.
  have hbs2 j : bs j <= g / 32.
    exact: (cond_beta_small (af_Mk kappa) (b' j) cb g Mk2 (b'0 j) cb0 g0).
  have [Dn hDn] := af_ev_density n alpha a0 hn.
  have [Dg hDg] := hgap n hn (1 / 2) h12.
  have [Dm hDm] := hadj (eps / 2) e2.
  have [D72 hD72] := af_ev_sqrt (72 / alpha).
  have [DB hDB] := af_ev_sqrt (32 * Num.max B 0 / g).
  have [Dt hDt] := af_ev_fin J
    (fun j d => taug d <= (kappa - 1) * alpha * etas j / 4)
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
  have hcen j :
      g / 4 <= af_center kappa (a' j) (b' j) d (n d) (bs j) (af_gam d).
    have h := af_center_ge kappa Kg (a' j) (b' j) d (n d) (bs j) (af_gam d)
      (taug d) (a'b' j) (bs0 j) g1 (hG d d0) EG (g / 2) mEG PEG
      (fun Z nZ => af_value_gap kappa (a' j) (b' j) Cp g d (n d) (bs j)
        (af_gam d) Z k1 d0 n0 (a'0 j) (a'b' j) (b'Cp j) (bs0 j) g1
        (fun S b hS => hEG Z nZ S hS b)).
    by move: h; have -> : g / 2 / 2 = g / 4 by field.
  (* the events of Theorem 2.9 for the mixture features *)
  pose rho := mix_feature_law K N w mu hfam d.
  pose F j := [set Z : (n d).-tuple 'rV[RR]_(d * d) |
    (af_err kappa Kg (a' j) (b' j) d (n d) (bs j) (af_gam d) (taug d) + ts j <
     `|af_value kappa (a' j) (b' j) d (n d) (bs j) (af_gam d) Z -
       af_center kappa (a' j) (b' j) d (n d) (bs j) (af_gam d)|)%R].
  have mF j : measurable (F j).
    apply: measurable_set_lt.
    apply: measurableT_comp (@normr_measurable RR _) _.
    apply: measurable_funB => //.
    exact: (measurable_af_value kappa (a' j) (b' j) d (n d) (bs j) (af_gam d)
      (a'b' j) (bs0 j) g1).
  have PF j : (tuple_prod (fun=> rho) (n d) (F j) <=
      (af_prob kappa Kg (a' j) (b' j) d (n d) (bs j) (af_gam d) (ts j))%:E)%E.
    exact: (af_conc kappa Kg (a' j) (b' j) d (n d) (bs j) (af_gam d) (ts j)
      (taug d) n0 (a'b' j) (bs0 j) g1 (ts0 j) n36 (taug0 d) (hG d d0) rho
      (hreg d d0)).
  have [mU PU] := slice_union_le (tuple_prod (fun=> rho) (n d)) mF.
  have hpsum : \sum_(j < J) af_prob kappa Kg (a' j) (b' j) d (n d) (bs j)
      (af_gam d) (ts j) <= eps / 4.
    have := cond_prob_sum_eps J (fun j => af_prob kappa Kg (a' j) (b' j) d (n d)
      (bs j) (af_gam d) (ts j)) (eps / 2) e2
      (fun j => sl_prob_small kappa Kg alpha (a' j) (b' j) k1 a0 (a'b' j) delta
        epsQ dl0 d (n d) d0 nlo (hD7 d d7 j)).
    by have -> : eps / 2 / 2 = eps / 4 by field.
  pose FU := unsat_features (n d) d @^-1` (\big[setU/set0]_(j < J) F j).
  have mFU : measurable FU.
    by rewrite /FU -[X in measurable X]setTI; exact: measurable_unsat_features.
  have PFU : (mixP d FU <= (eps / 4)%:E)%E.
    rewrite /FU -mixPE (mixture_features_law K N w mu hfam (n d) d _ mU).
    apply: le_trans PU _.
    apply: le_trans (_ : (\sum_(j < J) (af_prob kappa Kg (a' j) (b' j) d (n d)
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
  have hup := af_value_common kappa (a' j) (b' j) d (n d) (bs j) (af_gam d) W
    R b0 k1 d0 (a'0 j) (a'b' j) (bs0 j) g1 hj' hcW.
  have hb := common_value_le (n d) d x R b0 (Ca * Num.sqrt d%:R) n0 hc
    (hEm x nEm).
  have hRF : frobenius R ^+ 2 <= b' j * d%:R.
    rewrite frobenius_sqr -mxdot_mxvec.
    exact: (slice2_frobenius d (a' j) (b' j) (mxvec R) (ltW (a'0 j)) hj').
  have hb02 := cond_b0_bound Ca b0 (frobenius R) (b' j) alpha d (n d) a0 d0
    nlo hb (frobenius_ge0 R) hRF (ltW (b'0 j)).
  have hu : bs j * (af_Mk kappa * b' j + b0 ^+ 2) <= g / 32.
    apply: le_trans (hbs j).
    by apply: ler_wpM2l; [exact: ltW | rewrite lerD2l].
  have hbar := cond_bar_small d (logdet_barrier2 d (a' j) (b' j) (mxvec R)) B g
    d0 g0 hBar (hDB d dB).
  (* the value of the data is at least g / 4 - beta_j / 4 *)
  have nFj : ~ F j W.
    by move=> h; apply: nFU; rewrite /FU /=; exact: af_in_bigsetU h.
  have hlo : af_center kappa (a' j) (b' j) d (n d) (bs j) (af_gam d) -
      (af_err kappa Kg (a' j) (b' j) d (n d) (bs j) (af_gam d) (taug d) + ts j)
      <= af_value kappa (a' j) (b' j) d (n d) (bs j) (af_gam d) W.
    exact: cond_norm_lb nFj.
  have herr := sl_err_small kappa Kg alpha (a' j) (b' j) k1 a0 (a'b' j) delta
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

(* 2. The unsatisfiable half above alpha(C, kappa), with interfaces I3 and
   I1 as hypotheses. *)

Theorem condition_kappa_unsat (K kappa C alpha : R) :
  0 < K -> 1 < kappa -> 1 < C -> 0 < alpha ->
  condition_kappa_alpha C kappa < alpha ->
  (forall C' alpha' : R, 1 < C' -> condition_kappa_alpha C' kappa < alpha' ->
     exists2 Cp : R, C' < Cp & condition_kappa_alpha Cp kappa < alpha') ->
  (forall C' : R, 1 < C' -> cvg_prob (fun d => @gauss RR (d * d))
     (fun d a => kcond_support kappa C' (vec_mx a : 'M[RR]_d) / d%:R)
     (Num.sqrt (condition_kappa_alpha C' kappa))) ->
  forall (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  paper_main_tends_to
    (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                (universality_conditioned_fit_event (n d) d C)) 0.
Proof.
move=> K0 k1 C1 a0 aC hright hI1 N w mu hfam h4 n hn.
have [Cp CCp aCp] := hright C alpha C1 aC.
have Cp1 := lt_trans C1 CCp.
exact: (condition_kappa_unsat_gap K kappa C Cp alpha K0 k1 C1 CCp a0
  (gaussian_kappa_gap kappa Cp alpha k1 Cp1 a0 aCp (hI1 Cp Cp1))
  N w mu hfam h4 n hn).
Qed.
