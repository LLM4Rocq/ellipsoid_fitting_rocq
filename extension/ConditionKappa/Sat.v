(* The satisfiable half of the threshold at fourth moment kappa, for finite
   mixtures of product laws, at Stdlib's R: item D1 of phase 11
   (notes/phase11-plan.md, sections 3.4, 5 and 6; lane B). The model is
   Condition/Sat.v, which treats kappa = 3; Condition/Cover.v and
   Condition/Slices.v are reused as they are.

   The result: for K > 0, kappa > 1, C > 1 and
   0 < alpha < alpha(C, kappa), every finite mixture family with
   mixture_family K N w mu and mixture_fourth_moment kappa N w mu, and every
   n with n/d^2 -> alpha, the probability of
   universality_conditioned_fit_event (n d) d C tends to 1.

   Interfaces used.
   - I3, in the forms of condition_kappa_alpha_left and
     condition_kappa_alpha_half of Curve.v (item S3): the analogue of
     condition_alpha_left of Condition/Curve.v for alpha(C, kappa), which
     gives some Cm with 1 < Cm < C and alpha < alpha(Cm, kappa); and
     alpha(Cm, kappa) < alpha*(kappa) < 1/2, which gives the alpha < 1/2 of
     the mixture interpolation (in place of condition_alpha_le).
   - I4 (the witness) at Cm: the hypothesis of condition_sat_witness of
     Condition/Sat.v with gaussian_feature_law kappa d; see the header of
     GaussianWitness. condition_kappa_sat_witness takes it as a
     hypothesis, and condition_kappa_sat supplies it by
     gaussian_kappa_witness of GaussianWitness.v (item G1).
   Constants by their role: the constant Kf = 2^10 K^2 / sqrt (3 - 1) of
   Condition/Sat.v is that of mix_feature_regular at the data fourth
   moment and becomes 2^10 K^2 / sqrt (kappa - 1); the 3^(1/4) of the
   Gaussian regularity bound gaussian_feature_regular holds for every kappa
   and stays.

   Proved.
   1. condition_kappa_sat_cover: condition_sat_cover of Condition/Sat.v at
      fourth moment kappa. Its proof is that of Condition/Sat.v with kappa
      in place of 3: the slices of Condition/Slices.v, Theorem 2.9 and the
      center choice at kappa, the regularity of the mixture features with
      Kf = 2^10 K^2 / sqrt (kappa - 1) (mix_feature_regular) and of the
      Gaussian features with 3^(1/4) (gaussian_feature_regular), and the
      witness of the Gaussian features of gaussian_feature_law kappa d.
   2. condition_kappa_sat_witness: the satisfiable half for
      1 < Cm < C and 0 < alpha < alpha(Cm, kappa) < 1/2, from interface I4
      (the witness at Cm) and the finite cover cond_cover of
      Condition/Cover.v for C_0 = Cm, C_1 = C.
   3. condition_kappa_sat: the result above, from interface I3 (the
      analogue of condition_alpha_left and alpha(C', kappa) < 1/2 for every
      C' > 1) and interface I1 for every C' > 1, through
      gaussian_kappa_witness (GaussianWitness, item G1) at Cm. These
      three hypotheses stay explicit here and are discharged where (20) is
      assembled: I1 by kcond_support_cvg of GaussianLimit.v in
      condition_kappa_statement_of_I3 of Theorem.v, and the two forms of I3
      by condition_kappa_alpha_left and condition_kappa_alpha_half of
      Curve.v in ConditionKappaTheorem.v. *)

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
From GaussianAnalysis.matrix Require Import condition_cone.
From GaussianAnalysis.probability Require Import lindeberg subgaussian mixture.
From GaussianAnalysis.probability Require Import variational.
From GaussianAnalysis.convex Require Import logdet_barrier least_squares.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import Measurability.Fit Measurability.Balanced.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
From EllipsoidUniversality.Features Require Import Definitions Regular Mixture.
From EllipsoidUniversality.Model Require Import Rows Measurability.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Unsat Require Import FourthMomentThree.
From EllipsoidUniversality.Sat Require Import Apriori ApproximateFit.
From EllipsoidUniversality.Sat Require Import Universality.
From EllipsoidUniversality.Gaussian Require Import Threshold InProbability.
From EllipsoidUniversality.Mixture Require Import Interpolation.
Require Import EllipsoidUniversality.Mixture.Theorem.
From EllipsoidUniversality.Condition Require Import Slices Cover Sat.
From EllipsoidUniversality.ConditionKappa Require Import Cone GaussianWitness.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. The satisfiable half from a Gaussian witness on finitely many
   slices, at fourth moment kappa. *)

Section condition_kappa_sat_cover.
Variables (K kappa C alpha : R) (J : nat) (a b : 'I_J -> R) (cb c0 : R).
Hypotheses (K0 : 0 < K) (k1 : 1 < kappa) (Cgt1 : 1 < C).
Hypotheses (a0 : 0 < alpha) (ah : alpha < 2^-1).
Hypotheses (a_pos : forall j, 0 < a j) (ab : forall j, a j < 1 < b j).
Hypotheses (bC : forall j, b j < C * a j) (cb0 : 0 <= cb) (c00 : 0 <= c0).
Hypothesis hwit : forall n : nat -> nat,
  universality_density_tends_to n alpha ->
  af_eventually (fun d =>
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= (1 / 4)%:E)%E &
    forall Z, ~ E Z -> exists (j : 'I_J) (S : 'M[R]_d), [/\
      pd_slice2 d (a j) (b j) (mxvec S),
      logdet_barrier2 d (a j) (b j) (mxvec S) <= cb * d%:R &
      \sum_(i < n d) mxdot (tnth Z i) (mxvec S) ^+ 2 <= c0]]).

Theorem condition_kappa_sat_cover (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : mixture_family K N w mu) :
  mixture_fourth_moment kappa N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  paper_main_tends_to
    (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                (universality_conditioned_fit_event (n d) d C)) 1.
Proof.
move=> h4 n hn.
pose Kf : RR := 2 ^+ 10 * K ^+ 2 / Num.sqrt (kappa - 1).
pose Ls : RR := 252 * K ^+ 2.
have Ls0 : 0 < Ls by rewrite mulr_gt0 ?exprn_gt0.
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
have C0 : 0 < C by exact: lt_trans ltr01 Cgt1.
(* the margin e of the condition number on every slice *)
have hpos j : 0 < (C * a j - b j) / (C + 1).
  by apply: divr_gt0; [rewrite subr_gt0 | exact: addr_gt0].
have [e e0 he] := fin_pos_min J (fun j => (C * a j - b j) / (C + 1)) hpos.
have hej j : e < a j /\ b j + e <= C * (a j - e).
  have := he j; have /andP[_ b1] := ab j; have := a_pos j.
  rewrite ler_pdivlMr ?addr_gt0 // => ha hej.
  by split; nra.
have [C1 [C10 hI]] := mixture_small_residual K alpha K0 a0 ah.
have [q [q1 hZq]] := mixture_points_nonzero_holds K K0 N w mu hfam.
pose mixP d : probability (paper_main_sample (n d) d) RR :=
  mixture (fun s : (n d).-tuple 'I_(N d) =>
      mixture_labelled_law (N d) (mu d) (n d) d s)
    (mixture_weights_prod (n d) (mix_weights K N w mu hfam d)).
have mixPE d (A : set (paper_main_sample (n d) d)) :
    mixture_probability (N d) (w d) (mu d) (n d) d A = mixP d A by [].
have key (eps : RR) : 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    exists B : set (paper_main_sample (n d) d), [/\ measurable B,
      (mixP d B <= eps%:E)%E &
      ~` universality_conditioned_fit_event (n d) d C `<=` B].
  move=> ep0.
  have e4 : 0 < eps / 4 by rewrite divr_gt0.
  have e2 : 0 < 2 * e by rewrite mulr_gt0.
  pose delta := (2 * e / (4 * C1)) ^+ 2 / (2 * alpha).
  have dl0 : 0 < delta.
    apply: divr_gt0; last by rewrite mulr_gt0.
    by apply: exprn_gt0; apply: divr_gt0 => //; rewrite mulr_gt0.
  have hs2 k d : (0 < d)%N -> k%:R <= 2 * alpha * d%:R ^+ 2 ->
      C1 * (Num.sqrt (delta * k%:R) / d%:R) <= e / 2.
    move=> d0 hk; have := sat_small2 C1 (2 * e)%R alpha k d d0 C10 e2 a0 hk.
    by have -> : 2 * e / 4 = e / 2 by field.
  pose bs j := sl_beta kappa (b j) delta.
  pose ts j := sl_t kappa (b j) delta.
  pose etas j := sl_eta kappa Kg (b j) delta.
  pose P1s j := sl_P1 kappa Kg (b j) delta.
  pose Cs j := sl_C kappa Ls (b j).
  pose epsJ : RR := J.+1%:R^-1.
  have bs0 j : 0 < bs j := sl_beta_gt0 kappa (a j) (b j) (ab j) delta dl0.
  have ts0 j : 0 < ts j := sl_t_gt0 kappa (a j) (b j) (ab j) delta dl0.
  have etas0 j : 0 < etas j.
    exact: (sl_eta_gt0 kappa Kg (a j) (b j) (ab j) delta dl0).
  have Cs0 j : 0 < Cs j := sl_C_gt0 kappa Ls (a j) (b j) Ls0 (ab j).
  have te j : 0 < (kappa - 1) * alpha * etas j / 4.
    by rewrite divr_gt0 // mulr_gt0 // mulr_gt0 // subr_gt0.
  have [Dn hDn] := af_ev_density n alpha a0 hn.
  have [Dw hDw] := hwit n hn.
  have [D2 hD2] := hI N w mu hfam n hn (eps / 4)%R e4.
  have [N0 hN0] := sat_expr_small q (eps / 4)%R q1 e4.
  have [Dq hDq] := af_ev_ge (2 * N0%:R / alpha).
  have [D72 hD72] := af_ev_sqrt (72 / alpha).
  have [D8 hD8] := af_ev_ge (8 * alpha / (eps / 4)).
  have [Dt hDt] := af_ev_fin J
    (fun j d => taug d <= (kappa - 1) * alpha * etas j / 4)
    (fun j => htaug _ (te j)).
  have [D4 hD4] := af_ev_fin J (fun j d => 4 / (alpha * etas j) <= d%:R)
    (fun j => af_ev_ge _).
  have [D5 hD5] := af_ev_fin J
    (fun j d => 2 / (alpha * etas j ^+ 2) <= Num.sqrt d%:R)
    (fun j => af_ev_sqrt _).
  have [D7 hD7] := af_ev_fin J
    (fun j d => 2 / alpha * P1s j * af_Q (eps / 4)%R <= d%:R)
    (fun j => af_ev_ge _).
  have [D7' hD7'] := af_ev_fin J
    (fun j d => 2 / alpha * P1s j * af_Q epsJ <= d%:R)
    (fun j => af_ev_ge _).
  have [Dc hDc] := af_ev_fin J (fun j d => 8 * c0 / (alpha * bs j) <= d%:R)
    (fun j => af_ev_ge _).
  have [Db hDb] := af_ev_fin J (fun j d => 8 * cb / bs j <= Num.sqrt d%:R)
    (fun j => af_ev_sqrt _).
  have hsm j : af_eventually (fun d => (0 < d)%N ->
      C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * (Cs j * ln (d%:R : RR)))
        <= e / 2).
    apply: (af_ev_mono _ _ _ (af_ev_sqrt
      ((4 * C1 * Cs j * Num.sqrt (2 ^+ 10 * 10`!%:R) / (2 * e)) ^+ 2))).
    move=> d hd d0.
    have := sat_small1 C1 (Cs j) (2 * e)%R d d0 C10 (Cs0 j) e2 hd.
    by have -> : 2 * e / 4 = e / 2 by field.
  have [Ds hDs] := af_ev_fin J _ hsm.
  pose Dl := (archimedean.Num.truncn (expR (1 : RR))).+1.
  exists (maxn (maxn (maxn (maxn Dn Dw) (maxn D2 Dq)) (maxn (maxn D72 D8)
    (maxn Dt D4))) (maxn (maxn (maxn D5 D7) (maxn D7' Dc))
    (maxn (maxn Db Ds) Dl))) => d.
  rewrite !geq_max => /andP[/andP[/andP[/andP[dn dw] /andP[d2 dq]]
    /andP[/andP[d72 d8] /andP[dt d4]]] /andP[/andP[/andP[d5 d7]
    /andP[d7' dc]] /andP[/andP[db ds] dl]]].
  have [d0 [nlo nhi]] := hDn d dn.
  have dR : 0 < d%:R :> RR by rewrite ltr0n.
  have nR : 0 < (n d)%:R :> RR.
    apply: lt_le_trans nlo; apply: mulr_gt0; last exact: exprn_gt0.
    by apply: divr_gt0.
  have n0 : (0 < n d)%N by rewrite -(ltr_nat RR).
  have g0 := af_gam_gt0 d d0.
  have n36 := af_n36 alpha a0 d (n d) d0 nlo (hD72 d d72).
  (* the choice of the slice, from the Gaussian witness *)
  have [EG [mEG PEG hEG]] := hDw d dw.
  have hval Z : ~ EG Z -> exists j,
      af_value kappa (a j) (b j) d (n d) (bs j) (af_gam d) Z <=
        bs j * af_Mk kappa * b j + bs j / 4.
    move=> nZ; have [j [S [hS hB hL]]] := hEG Z nZ; exists j.
    apply: le_trans (af_value_approx kappa (a j) (b j) d (n d) (bs j)
      (af_gam d) k1 d0 (a_pos j) (ab j) (bs0 j) g0 Z S hS) _.
    have hw := cond_witness_small alpha c0 cb (bs j) d (n d) a0 c00 cb0
      (bs0 j) d0 nlo (hDc d dc j) (hDb d db j).
    have n2 : 0 <= ((n d)%:R *+ 2)^-1 :> RR by rewrite invr_ge0 mulrn_wge0.
    have h1 := ler_wpM2l n2 hL.
    have h2 := ler_wpM2l (ltW g0) hB.
    clear -h1 h2 hw.
    move: h1 h2 hw; set x := (_ * \sum_(i < n d) _).
    set z := (af_gam d * logdet_barrier2 _ _ _ _); set y := bs j * _ * _.
    by move=> h1 h2 hw; lra.
  have hpsum : \sum_(j < J) af_prob kappa Kg (a j) (b j) d (n d) (bs j)
      (af_gam d) (ts j) <= 1 / 2.
    apply: cond_prob_sum => j.
    exact: (sl_prob_small kappa Kg alpha (a j) (b j) k1 a0 (ab j) delta epsJ
      dl0 d (n d) d0 nlo (hD7' d d7' j)).
  have [j hj] := af_center_choice kappa Kg d (n d) J a b bs ts (af_gam d)
    (taug d) n0 ab bs0 g0 ts0 n36 (taug0 d) (hG d d0) EG
    (fun j => bs j * af_Mk kappa * b j + bs j / 4) mEG PEG hpsum hval.
  (* the approximate fit on the slice j *)
  have [E1 [mE1 PE1 hE1]] := slice_at_d kappa Kg Ls alpha (a j) (b j) k1 Ls0
    a0 (a_pos j) (ab j) delta (eps / 4)%R dl0 e4 d (n d) (taug d)
    (mix_feature_law K N w mu hfam d) (hreg d d0) (hG d d0) (taug0 d)
    (fun A L L0 hL => mix_feature_subexponential K N w mu hfam d A L d0 L0 hL)
    d0 nlo nhi (hDt d dt j) (hD4 d d4 j) (hD5 d d5 j) (hD72 d d72)
    (hD7 d d7 j) (hD8 d d8) (ln_ge1 d dl) hj.
  (* Theorem 1.9 and the nonzero points *)
  have [E2 [mE2 PE2 hE2]] := hD2 d d2.
  rewrite mixPE in PE2.
  have [G [mG PG hGz]] := hZq (n d) d d0.
  rewrite mixPE in PG.
  have nN0 := sat_count_ge alpha N0 (n d) d d0 a0 (hDq d dq) nlo.
  have PG' : (mixP d G <= (eps / 4)%:E)%E.
    apply: le_trans PG _; rewrite lee_fin.
    exact: le_trans (ler_norm _) (ltW (hN0 _ nN0)).
  have [F1 [mF1 PF1 hF1]] : exists F1 : set (paper_main_sample (n d) d),
      [/\ measurable F1, (mixP d F1 <= (eps / 4)%:E)%E &
        unsat_features (n d) d @^-1` E1 `<=` F1].
    exists (unsat_features (n d) d @^-1` E1); split => //.
      by rewrite -[X in measurable X]setTI; exact: measurable_unsat_features.
    rewrite -mixPE (mixture_features_law K N w mu hfam (n d) d E1 mE1).
    exact: PE1.
  exists (F1 `|` E2 `|` G); split.
  - by apply: measurableU => //; exact: measurableU.
  - apply: le_trans (measureU2 _ (measurableU _ _ mF1 mE2) mG) _.
    apply: le_trans (leeD (measureU2 _ mF1 mE2) (lexx _)) _.
    apply: le_trans (leeD (leeD PF1 PE2) PG') _.
    by rewrite -!EFinD lee_fin; exact: sat_quarters (ltW ep0).
  move=> x hx; apply: contrapT => hno; apply: hx.
  have [ej hCj] := hej j.
  apply: (cond_at_d (a j) (b j) e C (Cs j) C1 delta (n d) d E1 E2 G d0
    (ltW e0) ej hCj (ltW C10) hE1 hE2 hGz (hDs d ds j d0)
    (hs2 (n d) d d0 nhi) x) => h; apply: hno.
  - by left; left; exact: hF1.
  - by left; right.
  - by right.
move=> eps ep0.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have [D hD] := key (eps / 2) e2.
exists D => d dD.
have [B [mB PB hB]] := hD d dD.
have h := prob_close_one _ _ (mixP d) _ B (eps / 2)
  (measurable_conditioned_fit_event (n d) d C) mB hB PB.
rewrite mixPE; apply: le_lt_trans h _.
by rewrite lte_fin; exact: sat_half.
Qed.

End condition_kappa_sat_cover.

(* 2. The satisfiable half from the Gaussian witness in the trace slice of
   the cone of condition number Cm < C, through the cover of
   Condition/Cover.v. *)

Theorem condition_kappa_sat_witness (K kappa C Cm alpha : R) :
  0 < K -> 1 < kappa -> 1 < Cm -> Cm < C -> 0 < alpha ->
  alpha < condition_kappa_alpha Cm kappa ->
  condition_kappa_alpha Cm kappa < 2^-1 ->
  (exists c0 : R, 0 <= c0 /\
   forall n : nat -> nat, universality_density_tends_to n alpha ->
   exists D : nat, forall d, (D <= d)%N ->
   exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
     (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <=
       (1 / 4)%:E)%E &
     forall Z, ~ E Z -> exists S : 'M[R]_d, cond_slice Cm S /\
       \sum_(i < n d) mxdot (tnth Z i) (mxvec S) ^+ 2 <= c0]) ->
  forall (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  paper_main_tends_to
    (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                (universality_conditioned_fit_event (n d) d C)) 1.
Proof.
move=> K0 k1 Cm1 CmC a0 aC aCh [c0 [c00 hW]] N w mu hfam h4 n hn.
have Cgt1 : 1 < C := lt_trans Cm1 CmC.
have ah : alpha < 2^-1 := lt_trans aC aCh.
have [J [a [b [B [hab hcov]]]]] := cond_cover Cm C (ltW Cm1) CmC.
pose a' (j : 'I_J) := a j.
pose b' (j : 'I_J) := b j.
have a'0 j : 0 < a' j by have [] := hab j (ltn_ord j).
have a'b' j : a' j < 1 < b' j.
  by have [_ h1 h2 _] := hab j (ltn_ord j); rewrite /a' /b' h1 h2.
have b'C j : b' j < C * a' j by have [] := hab j (ltn_ord j).
have cb0 : 0 <= Num.max B 0 by rewrite le_max lexx orbT.
apply: (condition_kappa_sat_cover K kappa C alpha J a' b' (Num.max B 0) c0 K0
  k1 Cgt1 a0 ah a'0 a'b' b'C cb0 c00 _ N w mu hfam h4 n hn).
move=> n' hn'.
have [D hD] := hW n' hn'.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d1].
have [E [mE PE hE]] := hD d dD.
exists E; split => // Z nZ.
have [S [hS hL]] := hE Z nZ.
have [j jJ [hj hB]] := hcov d S d1 hS.
exists (Ordinal jJ), S; split => //.
apply: le_trans hB _; rewrite mulrC.
by apply: ler_wpM2r; [exact: ler0n | rewrite le_max lexx].
Qed.

(* 3. The satisfiable half below alpha(C, kappa), with interfaces I3 and I1
   as hypotheses. *)

Theorem condition_kappa_sat (K kappa C alpha : R) :
  0 < K -> 1 < kappa -> 1 < C -> 0 < alpha ->
  alpha < condition_kappa_alpha C kappa ->
  (forall C' alpha' : R, 1 < C' -> alpha' < condition_kappa_alpha C' kappa ->
     exists2 Cm : R, 1 < Cm < C' & alpha' < condition_kappa_alpha Cm kappa) ->
  (forall C' : R, 1 < C' -> condition_kappa_alpha C' kappa < 2^-1) ->
  (forall C' : R, 1 < C' -> cvg_prob (fun d => @gauss RR (d * d))
     (fun d a => kcond_support kappa C' (vec_mx a : 'M[RR]_d) / d%:R)
     (Num.sqrt (condition_kappa_alpha C' kappa))) ->
  forall (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  paper_main_tends_to
    (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                (universality_conditioned_fit_event (n d) d C)) 1.
Proof.
move=> K0 k1 C1 a0 aC hleft hhalf hI1 N w mu hfam h4 n hn.
have [Cm /andP[Cm1 CmC] aCm] := hleft C alpha C1 aC.
exact: (condition_kappa_sat_witness K kappa C Cm alpha K0 k1 Cm1 CmC a0 aCm
  (hhalf Cm Cm1)
  (gaussian_kappa_witness kappa Cm alpha k1 Cm1 a0 aCm (hI1 Cm Cm1))
  N w mu hfam h4 n hn).
Qed.
