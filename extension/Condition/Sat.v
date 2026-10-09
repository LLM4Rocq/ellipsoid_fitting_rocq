(* The satisfiable half of the condition-number threshold (20) at fourth
   moment three, for finite mixtures of product laws, at Stdlib's R: item
   Q7 of phase 8 (notes/three-extensions-plan.md, sections 2 (D1) and 5.2;
   lane A).

   The event is universality_conditioned_fit_event (n d) d C: the sample
   has an exact fit of value 1 and of condition number at most C. The
   features are W_i = (x_i x_i^T - I) / sqrt d (sample_W), and the
   Gaussian features are those of gaussian_feature_law 3 d.

   Main results.
   - sat_fit_cond: the deterministic step, a variant of sat_fit_det of
     Sat/Universality.v. If R0 lies in pd_slice2 d a b, Delta is symmetric
     with opnorm Delta <= e < a, b + e <= C (a - e), all the values
     <W_i, R0 + Delta> are equal and some point is not zero, then the
     sample has a fit of condition number at most C. cond_at_d combines it
     with an approximate fit on the slice and with Theorem 1.9 for the
     residuals, as sat_at_d does.
   - af_ev_fin, fin_pos_min, cond_witness_small, cond_prob_sum: finitely
     many slices share a dimension threshold and a margin e > 0; the
     Gaussian value at a witness S of a slice, with barrier at most cb d and
     sum_i <G_i, S>^2 <= c0, is at most beta Mk b + beta / 4 for d large;
     the probabilities of Theorem 2.9 for J slices sum to at most 1/2 when
     each is at most 1 / af_Q (1 / (J + 1)).
   - condition_sat_cover: let (a_j, b_j), j < J, be slices with
     0 < a_j < 1 < b_j and b_j < C a_j. Suppose that, for d large, outside
     an event of Gaussian probability at most 1/4, some slice j holds a
     matrix S with barrier at most cb d and sum_i <G_i, S>^2 <= c0. Then,
     for K > 0, C > 1, 0 < alpha < 1/2, every finite mixture family of
     class K and fourth moment 3 and every n with n/d^2 -> alpha, the
     probability of the conditioned fit event tends to one.
     Proof: at each d, af_center_choice of Condition/Slices.v picks a slice
     j whose Gaussian center is small; slice_at_d gives on it an
     approximate fit of the mixture features outside an event of
     probability eps / 4; mixture_small_residual corrects it by a Delta
     with opnorm Delta <= e, e the margin of the slices; and cond_at_d
     concludes outside the union of four events of probability eps / 4
     each.
   - condition_sat_witness: the satisfiable half for 1 < C_- < C and
     alpha < condition_alpha C_-, from the Gaussian witness in the trace-d
     slice of the cone of condition number C_- (the statement of item Q3,
     taken as a hypothesis) and the finite cover cond_cover of
     Condition/Cover.v for C_0 = C_-, C_1 = C. alpha < 1/2 follows from
     condition_alpha C_- <= 1/2 (condition_alpha_le). *)

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
From GaussianAnalysis.matrix Require Import condition_cone.
From GaussianAnalysis.probability Require Import lindeberg subgaussian mixture.
From GaussianAnalysis.probability Require Import variational.
From GaussianAnalysis.convex Require Import logdet_barrier least_squares.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import Measurability.Fit Measurability.Balanced.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality.Features Require Import Definitions Regular Mixture.
From EllipsoidUniversality.Model Require Import Rows Measurability.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Unsat Require Import FourthMomentThree.
From EllipsoidUniversality.Sat Require Import Apriori ApproximateFit Universality.
From EllipsoidUniversality.Gaussian Require Import Threshold.
From EllipsoidUniversality.Mixture Require Import Interpolation.
Require Import EllipsoidUniversality.Mixture.Theorem.
From EllipsoidUniversality.Condition Require Import Slices Cover.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).


(* 1. The deterministic step: a fit of condition number at most C from a
   point of a slice corrected by a small Delta. *)

Lemma sat_fit_cond N d (x : paper_main_sample N d) (m M e C : R)
    (R0 Delta : 'M[R]_d) (c0 : R) :
  (0 < d)%N -> 0 <= e -> e < m -> M + e <= C * (m - e) ->
  pd_slice2 d m M (mxvec R0) -> Delta \is symmetricmx -> opnorm Delta <= e ->
  (forall i, mxdot (sample_W x i) (R0 + Delta) = c0) ->
  (exists i : 'I_N, paper_main_point x i != 0) ->
  universality_conditioned_fit_event N d C x.
Proof.
move=> d0 e0 em hC hR Ds hD hc [i0 hi0].
have me : 0 < m - e by rewrite subr_gt0.
have R0s : R0 \is symmetricmx.
  move: hR; rewrite /pd_slice2 /= mxvecK => [[[h _] _]].
  apply/symmetricmxP; move/symmetricmxP: h.
  by rewrite raddfB /= tr_scalar_mx => /addIr.
have Ss : R0 + Delta \is symmetricmx.
  have R0T : R0^T = R0 by apply/symmetricmxP.
  have DT : Delta^T = Delta by apply/symmetricmxP.
  by apply/symmetricmxP; rewrite raddfD /= R0T DT.
have hq v : (m - e) * pm_sqnorm d v <= paper_main_quadratic_form (R0 + Delta) v <=
    (M + e) * pm_sqnorm d v.
  rewrite pm_qf_add.
  have /andP[a1 a2] := slice2_qf d m M R0 v hR.
  have := qf_opnorm d Delta v Ds; rewrite ler_norml => /andP[b1 b2].
  have n0 : 0 <= pm_sqnorm d v by exact: pm_sqnorm_ge0.
  have c1 : opnorm Delta * pm_sqnorm d v <= e * pm_sqnorm d v.
    exact: ler_wpM2r.
  by apply/andP; split; lra.
pose t := Num.sqrt d%:R * c0 + \tr (R0 + Delta).
have ht (i : 'I_N) :
    paper_main_quadratic_form (R0 + Delta) (paper_main_point x i) = t.
  by rewrite qf_sample_W // hc.
have t0 : 0 < t.
  rewrite -(ht i0); have /andP[h _] := hq (paper_main_point x i0).
  apply: lt_le_trans h; apply: mulr_gt0 => //.
  exact: pm_sqnorm_gt0.
have tn : t != 0 by rewrite gt_eqF.
have ti : 0 <= t^-1 by rewrite invr_ge0 ltW.
exists (t^-1 *: (R0 + Delta)), ((m - e) / t); split.
  by rewrite divr_gt0.
split.
  apply/uni_loewner_geP; split; first exact: (uni_sym_scale _ _ _ (sym_paper _ _ Ss)).
  move=> v; rewrite uni_qf_scalemx.
  have /andP[h _] := hq v.
  apply: le_trans (ler_wpM2l ti h).
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
split.
  apply/uni_loewner_leP; split; first exact: (uni_sym_scale _ _ _ (sym_paper _ _ Ss)).
  move=> v; rewrite uni_qf_scalemx.
  have /andP[_ h] := hq v.
  apply: le_trans (ler_wpM2l ti h) _.
  have -> : C * ((m - e) / t) * pm_sqnorm d v =
      t^-1 * (C * (m - e) * pm_sqnorm d v) by field.
  apply: ler_wpM2l => //; apply: ler_wpM2r => //; exact: pm_sqnorm_ge0.
by move=> i; rewrite uni_qf_scalemx ht mulVf.
Qed.

Lemma cond_at_d (m M e C Cr C1 delta : R) (N d : nat)
    (E1 : set (N.-tuple 'rV[RR]_(d * d))) (E2 G : set (paper_main_sample N d)) :
  (0 < d)%N -> 0 <= e -> e < m -> M + e <= C * (m - e) -> 0 <= C1 ->
  (forall Z, ~ E1 Z -> exists (theta : 'rV[R]_(d * d)) (b : R), [/\
      pd_slice2 d m M theta,
      \sum_(i < N) (b - mxdot (tnth Z i) theta) ^+ 2 <= delta * N%:R &
      forall i, `|b - mxdot (tnth Z i) theta| <= Cr * ln (d%:R : RR)]) ->
  (forall x, ~ E2 x -> forall (y : 'rV[R]_N) (Y : R),
      (forall i, `|y 0 i| <= Y) ->
      exists (Delta : 'M[R]_d) (b : R), [/\ Delta \is symmetricmx,
        forall i, mxdot (sample_W x i) Delta = y 0 i + b &
        opnorm Delta <=
          C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * Y + frobenius y / d%:R)]) ->
  (forall x, ~ G x -> exists i : 'I_N, paper_main_point x i != 0) ->
  C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * (Cr * ln (d%:R : RR))) <= e / 2 ->
  C1 * (Num.sqrt (delta * N%:R) / d%:R) <= e / 2 ->
  forall x, ~ (unsat_features N d @^-1` E1) x -> ~ E2 x -> ~ G x ->
    universality_conditioned_fit_event N d C x.
Proof.
move=> d0 e0 em hC C10 h1 h2 hG s1 s2 x n1 n2 n3.
have [theta [b [hth hsum hres]]] := h1 _ n1.
have hR0 : pd_slice2 d m M (mxvec (vec_mx theta)) by rewrite vec_mxK.
have hW i : mxdot (tnth (unsat_features N d x) i) theta =
    mxdot (sample_W x i) (vec_mx theta).
  by rewrite -mxvec_sample_W -[in LHS](vec_mxK theta) mxdot_mxvec.
pose y : 'rV[R]_N := \row_i (b - mxdot (sample_W x i) (vec_mx theta)).
have hy i : `|y 0 i| <= Cr * ln (d%:R : RR) by rewrite mxE -hW; exact: hres.
have [Delta [b' [Ds hD hop]]] := h2 x n2 y _ hy.
have hfy : frobenius y <= Num.sqrt (delta * N%:R).
  rewrite /frobenius; apply: ler_wsqrtr.
  apply: le_trans hsum; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  rewrite /mxdot big_ord1; apply: eq_bigr => i _.
  by rewrite !mxE -hW expr2.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have hop' : opnorm Delta <= e.
  apply: le_trans hop _.
  have h3 : C1 * (frobenius y / d%:R) <= e / 2.
    apply: le_trans s2; apply: ler_wpM2l => //.
    by apply: ler_wpM2r; [rewrite invr_ge0 ltW | exact: hfy].
  rewrite mulrDr.
  move: s1 h3; move: (C1 * _) (C1 * (frobenius y / d%:R)) => u v.
  by lra.
apply: (sat_fit_cond N d x m M e C (vec_mx theta) Delta (b + b')%R d0 e0 em hC
  hR0 Ds hop').
  by move=> i; rewrite mxdotDr hD mxE; ring.
exact: hG x n3.
Qed.

(* 2. Finitely many slices. *)

(* A common dimension threshold for finitely many eventual properties. *)
Lemma af_ev_fin (J : nat) (P : 'I_J -> nat -> Prop) :
  (forall j, af_eventually (P j)) -> af_eventually (fun d => forall j, P j d).
Proof.
move=> h.
exists (\max_(j < J) projT1 (cid (h j))) => d dD j.
apply: (projT2 (cid (h j))).
by apply: leq_trans _ dD; exact: leq_bigmax.
Qed.

(* A positive lower bound of finitely many positive reals. *)
Lemma fin_pos_min (J : nat) (f : 'I_J -> R) : (forall j, 0 < f j) ->
  exists2 e : R, 0 < e & forall j, e <= f j.
Proof.
elim: J f => [|J IH] f hf; first by exists 1 => // -[].
have [e e0 he] := IH (fun j => f (lift ord0 j)) (fun j => hf _).
exists (Num.min e (f ord0)); first by rewrite lt_min e0 hf.
move=> j; case: (unliftP ord0 j) => [k ->|->].
  by rewrite ge_min he.
by rewrite ge_min lexx orbT.
Qed.

(* The loss and barrier terms of the Gaussian value at a witness are at
   most beta / 4 for d large. *)
Lemma cond_witness_small (alpha c0 cb beta : R) (d N : nat) :
  0 < alpha -> 0 <= c0 -> 0 <= cb -> 0 < beta -> (0 < d)%N ->
  alpha / 2 * d%:R ^+ 2 <= N%:R ->
  8 * c0 / (alpha * beta) <= d%:R -> 8 * cb / beta <= Num.sqrt d%:R ->
  (N%:R *+ 2)^-1 * c0 + af_gam d * (cb * d%:R) <= beta / 4.
Proof.
move=> a0 c00 cb0 b0 d0 hN h1 h2.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have d1 : 1 <= d%:R :> RR by rewrite ler1n.
have sd : 0 < Num.sqrt (d%:R : RR) by rewrite sqrtr_gt0.
have nR : 0 < N%:R :> RR.
  apply: lt_le_trans hN; apply: mulr_gt0; [exact: divr_gt0 | exact: exprn_gt0].
have hg : af_gam d * (cb * d%:R) = cb / Num.sqrt d%:R.
  have sdn : Num.sqrt (d%:R : RR) != 0 by rewrite gt_eqF.
  have dn : d%:R != 0 :> RR by rewrite gt_eqF.
  by rewrite /af_gam; field.
have t1 : cb / Num.sqrt d%:R <= beta / 8.
  rewrite ler_pdivrMr //.
  by move: h2; rewrite ler_pdivrMr // => h; lra.
have t2 : (N%:R *+ 2)^-1 * c0 <= beta / 8.
  have n2 : 0 < N%:R *+ 2 :> RR by rewrite mulrn_wgt0.
  rewrite mulrC ler_pdivrMr //.
  have ab : 0 < alpha * beta by apply: mulr_gt0.
  move: h1; rewrite ler_pdivrMr // => h.
  have hd2 : d%:R <= d%:R ^+ 2 :> RR by rewrite expr2 ler_peMl // ltW.
  have hN2 : alpha * d%:R <= N%:R *+ 2.
    rewrite mulr2n.
    have : alpha * d%:R <= alpha * d%:R ^+ 2 by rewrite ler_pM2l.
    by move: hN; lra.
  have : beta / 8 * (alpha * d%:R) <= beta / 8 * (N%:R *+ 2).
    by rewrite ler_pM2l // divr_gt0.
  by move: h; lra.
by rewrite hg; lra.
Qed.

(* The probabilities of Theorem 2.9 for J slices sum to at most 1/2. *)
Lemma cond_prob_sum (J : nat) (p : 'I_J -> R) :
  (forall j, p j <= 1 / af_Q (J.+1%:R^-1)) -> \sum_(j < J) p j <= 1 / 2.
Proof.
move=> hp.
apply: le_trans (ler_sum _ (fun j _ => hp j)) _.
rewrite sumr_const card_ord.
have J0 : 0 < J.+1%:R :> RR by rewrite ltr0n.
have hQ : 2 * J.+1%:R <= af_Q (J.+1%:R^-1).
  by rewrite /af_Q le_max; apply/orP; right; rewrite invrK.
have Q0 : 0 < af_Q (J.+1%:R^-1) by apply: lt_le_trans hQ; rewrite mulr_gt0.
move: hQ Q0; set Q := af_Q _ => hQ Q0.
have hJ : (J%:R : RR) <= J.+1%:R by rewrite ler_nat.
rewrite -[X in X <= _]mulr_natr div1r mulrC ler_pdivrMr //.
lra.
Qed.

(* 3. The satisfiable half from a Gaussian witness on finitely many
   slices. *)

Section condition_sat_cover.
Variables (K C alpha : R) (J : nat) (a b : 'I_J -> R) (cb c0 : R).
Hypotheses (K0 : 0 < K) (Cgt1 : 1 < C) (a0 : 0 < alpha) (ah : alpha < 2^-1).
Hypotheses (a_pos : forall j, 0 < a j) (ab : forall j, a j < 1 < b j).
Hypotheses (bC : forall j, b j < C * a j) (cb0 : 0 <= cb) (c00 : 0 <= c0).
Hypothesis hwit : forall n : nat -> nat, universality_density_tends_to n alpha ->
  af_eventually (fun d =>
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law 3%:R d) (n d) E <= (1 / 4)%:E)%E &
    forall Z, ~ E Z -> exists (j : 'I_J) (S : 'M[R]_d), [/\
      pd_slice2 d (a j) (b j) (mxvec S),
      logdet_barrier2 d (a j) (b j) (mxvec S) <= cb * d%:R &
      \sum_(i < n d) mxdot (tnth Z i) (mxvec S) ^+ 2 <= c0]]).

Theorem condition_sat_cover (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : mixture_family K N w mu) :
  mixture_fourth_moment 3%:R N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  paper_main_tends_to
    (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                (universality_conditioned_fit_event (n d) d C)) 1.
Proof.
move=> h4 n hn.
have k1 : 1 < 3%:R :> RR by rewrite ltr1n.
pose Kf : RR := 2 ^+ 10 * K ^+ 2 / Num.sqrt (3%:R - 1).
pose Ls : RR := 252 * K ^+ 2.
have Ls0 : 0 < Ls by rewrite mulr_gt0 ?exprn_gt0.
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
  pose bs j := sl_beta 3%:R (b j) delta.
  pose ts j := sl_t 3%:R (b j) delta.
  pose etas j := sl_eta 3%:R Kg (b j) delta.
  pose P1s j := sl_P1 3%:R Kg (b j) delta.
  pose Cs j := sl_C 3%:R Ls (b j).
  pose epsJ : RR := J.+1%:R^-1.
  have bs0 j : 0 < bs j := sl_beta_gt0 3%:R (a j) (b j) (ab j) delta dl0.
  have ts0 j : 0 < ts j := sl_t_gt0 3%:R (a j) (b j) (ab j) delta dl0.
  have etas0 j : 0 < etas j.
    exact: (sl_eta_gt0 3%:R Kg (a j) (b j) (ab j) delta dl0).
  have Cs0 j : 0 < Cs j := sl_C_gt0 3%:R Ls (a j) (b j) Ls0 (ab j).
  have te j : 0 < (3%:R - 1) * alpha * etas j / 4.
    by rewrite divr_gt0 // mulr_gt0 // mulr_gt0 // subr_gt0.
  have [Dn hDn] := af_ev_density n alpha a0 hn.
  have [Dw hDw] := hwit n hn.
  have [D2 hD2] := hI N w mu hfam n hn (eps / 4)%R e4.
  have [N0 hN0] := sat_expr_small q (eps / 4)%R q1 e4.
  have [Dq hDq] := af_ev_ge (2 * N0%:R / alpha).
  have [D72 hD72] := af_ev_sqrt (72 / alpha).
  have [D8 hD8] := af_ev_ge (8 * alpha / (eps / 4)).
  have [Dt hDt] := af_ev_fin J
    (fun j d => taug d <= (3%:R - 1) * alpha * etas j / 4)
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
      af_value 3%:R (a j) (b j) d (n d) (bs j) (af_gam d) Z <=
        bs j * af_Mk 3%:R * b j + bs j / 4.
    move=> nZ; have [j [S [hS hB hL]]] := hEG Z nZ; exists j.
    apply: le_trans (af_value_approx 3%:R (a j) (b j) d (n d) (bs j)
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
  have hpsum : \sum_(j < J) af_prob 3%:R Kg (a j) (b j) d (n d) (bs j)
      (af_gam d) (ts j) <= 1 / 2.
    apply: cond_prob_sum => j.
    exact: (sl_prob_small 3%:R Kg alpha (a j) (b j) k1 a0 (ab j) delta epsJ
      dl0 d (n d) d0 nlo (hD7' d d7' j)).
  have [j hj] := af_center_choice 3%:R Kg d (n d) J a b bs ts (af_gam d)
    (taug d) n0 ab bs0 g0 ts0 n36 (taug0 d) (hG d d0) EG
    (fun j => bs j * af_Mk 3%:R * b j + bs j / 4) mEG PEG hpsum hval.
  (* the approximate fit on the slice j *)
  have [E1 [mE1 PE1 hE1]] := slice_at_d 3%:R Kg Ls alpha (a j) (b j) k1 Ls0
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

End condition_sat_cover.

(* 4. The satisfiable half from the Gaussian witness in the trace slice of
   the cone of condition number C_- < C, through the cover of
   Condition/Cover.v. *)

Lemma condition_alpha_le (C : R) : condition_alpha C <= 2%:R^-1.
Proof.
rewrite /condition_alpha.
have s0 (x : R) : 0 <= universality_s x.
  by rewrite universality_sE; exact: upper_moment_ge0.
set u := universality_s _; set v := universality_s _.
have h1 : 0 <= u by exact: s0.
have h2 : 0 <= v by exact: s0.
by rewrite !RminusE; lra.
Qed.

Theorem condition_sat_witness (K C Cm alpha : R) :
  0 < K -> 1 < Cm -> Cm < C -> 0 < alpha -> alpha < condition_alpha Cm ->
  (exists c0 : R, 0 <= c0 /\
   forall n : nat -> nat, universality_density_tends_to n alpha ->
   exists D : nat, forall d, (D <= d)%N ->
   exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
     (tuple_prod (fun=> gaussian_feature_law 3%:R d) (n d) E <=
       (1 / 4)%:E)%E &
     forall Z, ~ E Z -> exists S : 'M[R]_d, cond_slice Cm S /\
       \sum_(i < n d) mxdot (tnth Z i) (mxvec S) ^+ 2 <= c0]) ->
  forall (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
  mixture_family K N w mu -> mixture_fourth_moment 3%:R N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  paper_main_tends_to
    (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                (universality_conditioned_fit_event (n d) d C)) 1.
Proof.
move=> K0 Cm1 CmC a0 aC [c0 [c00 hW]] N w mu hfam h4 n hn.
have Cgt1 : 1 < C := lt_trans Cm1 CmC.
have ah : alpha < 2^-1 := lt_le_trans aC (condition_alpha_le Cm).
have [J [a [b [B [hab hcov]]]]] := cond_cover Cm C (ltW Cm1) CmC.
pose a' (j : 'I_J) := a j.
pose b' (j : 'I_J) := b j.
have a'0 j : 0 < a' j by have [] := hab j (ltn_ord j).
have a'b' j : a' j < 1 < b' j.
  by have [_ h1 h2 _] := hab j (ltn_ord j); rewrite /a' /b' h1 h2.
have b'C j : b' j < C * a' j by have [] := hab j (ltn_ord j).
have cb0 : 0 <= Num.max B 0 by rewrite le_max lexx orbT.
apply: (condition_sat_cover K C alpha J a' b' (Num.max B 0) c0 K0 Cgt1 a0 ah
  a'0 a'b' b'C cb0 c00 _ N w mu hfam h4 n hn).
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
