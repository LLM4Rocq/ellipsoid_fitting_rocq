(* The quadratic features of a point drawn from a finite mixture of product
   laws, for the mixture theorem (MixtureStatement), at Stdlib's R. For a
   family as mixture_family K N w mu asks (MixtureDefinitions), the point
   law at dimension d is the mixture, with weights w d s, s < N d, of the
   products of the component laws mu d s j, j < d, of class K
   (mixture_component_law). Its features W = (x x^T - I) / sqrt d have the
   law mix_feature_law, the mixture of the laws data_feature_law (mu d s) d
   of the features of the components (Features/Definitions); the features
   of a mixture point are distributed so by distribution_mixture
   (probability/mixture.v). Item X1 of phase 6, second half (lane A).

   Main results.
   - mix_feature_subexponential: for every A, d > 0 and L >= 252 K^2 |A|_F,
     z |-> <z, mxvec A> is subexponential with constant L / sqrt d under
     mix_feature_law, the hypothesis on the feature law of
     approximate_fit_law (Sat/ApproximateFit); and
     mix_feature_quad_subexponential: for |v| <= 1 and d > 0,
     z |-> <z, mxvec (v^T v)> is subexponential with constant
     48 K^2 / sqrt d, the hypothesis of unsat_ridge_removal (Unsat/Ridge).
     Both by subexponential_mixture from the component bounds of
     Features/Regular.
   - mix_feature_regular: under (M3), mixture_fourth_moment kappa N w mu,
     with kappa > 1 and d > 0, mix_feature_law is a regular feature
     (regular_feature of convex/least_squares.v) with covariance
     unsat_cov kappa d, K_feat = 2^10 K^2 / sqrt (kappa - 1) and
     tau = sqrt ((2^31 + 16) K^8 / d), by mixture_regular_feature
     (convex/feature_mixture.v): the features of the component s have the
     covariance coord_cov (kap s) d of the fourth moments kap s j of its
     coordinates (component_feature_cov), their average is unsat_cov
     kappa d by (M3) (coord_cov_mix), and each differs from it by at most
     16 K^8 / d in squared Frobenius norm (coord_cov_frobenius, since
     0 <= kap s j, kappa <= 4 K^4).
   - coord_cov_mix, coord_cov_frobenius, eq_coord_cov: coord_cov is affine
     in the fourth moments, |coord_cov kap d - coord_cov kap' d|_F^2 =
     sum_(j < d) ((kap j - kap' j) / d)^2, and only kap j for j < d
     matters. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From mathcomp Require Import normedtype sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import subgaussian mixture.
From GaussianAnalysis.matrix Require Import euclidean opnorm.
From GaussianAnalysis.convex Require Import least_squares feature_mixture.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Mixture Require Import Component.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Features Require Import Definitions Regular.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Stdlib's reals seen through their realType structure. *)
Local Notation RR := (R : realType).

(* 1. The covariance matrices coord_cov. *)

Lemma big_mxvec_index d (F : 'I_(d * d) -> R) :
  \sum_k F k = \sum_i \sum_j F (mxvec_index i j).
Proof.
rewrite pair_bigA /= (reindex (uncurry (@mxvec_index d d))) /=.
  exact: curry_mxvec_bij.
by apply: eq_bigr => -[i j] _.
Qed.

(* Only the fourth moments of the coordinates j < d matter. *)
Lemma eq_coord_cov (kap kap' : nat -> R) d :
  (forall j, (j < d)%N -> kap j = kap' j) -> coord_cov kap d = coord_cov kap' d.
Proof.
move=> e; apply/matrixP => p q; rewrite !mxE /coord_cov_form.
by congr (_ * (_ + _)); apply: eq_bigr => j _; rewrite e.
Qed.

(* coord_cov is affine in the fourth moments. *)
Lemma coord_cov_mix I (r : seq I) (w : I -> R) (kap : I -> nat -> R) d :
  \sum_(s <- r) w s = 1 ->
  \sum_(s <- r) w s *: coord_cov (kap s) d =
  coord_cov (fun j => \sum_(s <- r) w s * kap s j) d.
Proof.
move=> w1; apply/matrixP => p q; rewrite summxE [RHS]mxE.
under eq_bigr do rewrite !mxE.
rewrite /coord_cov_form.
move: (vec_mx (delta_mx 0 p : 'rV[R]_(d * d)))
  (vec_mx (delta_mx 0 q : 'rV[R]_(d * d))) => A B.
move: (mxdot A B + mxdot A B^T) => X.
have -> : \sum_(j < d) ((\sum_(s <- r) w s * kap s j) - 3) * (A j j * B j j) =
    \sum_(s <- r) w s * \sum_(j < d) (kap s j - 3) * (A j j * B j j).
  under [RHS]eq_bigr do rewrite mulr_sumr.
  rewrite [RHS]exchange_big /=; apply: eq_bigr => j _.
  have -> : (\sum_(s <- r) w s * kap s j) - 3 =
      \sum_(s <- r) w s * (kap s j - 3).
    transitivity (\sum_(s <- r) (w s * kap s j - 3 * w s)).
      by rewrite sumrB -mulr_sumr w1 mulr1.
    by apply: eq_bigr => s _; ring.
  by rewrite mulr_suml; apply: eq_bigr => s _; ring.
transitivity (\sum_(s <- r) (d%:R^-1 * X * w s +
    d%:R^-1 * (w s * \sum_(j < d) (kap s j - 3) * (A j j * B j j)))).
  by apply: eq_bigr => s _; ring.
by rewrite big_split /= -!mulr_sumr w1; ring.
Qed.

Lemma coord_cov_diff_entry (kap kap' : nat -> R) d (i k i' k' : 'I_d) :
  (coord_cov kap d - coord_cov kap' d) (mxvec_index i k) (mxvec_index i' k') =
  (kap i - kap' i) / d%:R * ((i == k) && (i == i') && (i == k'))%:R.
Proof.
rewrite !mxE !vec_mx_delta /coord_cov_form.
have e (X S1 S2 : R) : d%:R^-1 * (X + S1) - d%:R^-1 * (X + S2) =
    d%:R^-1 * (S1 - S2) by ring.
rewrite e -sumrB (bigD1 i) //= big1 ?addr0.
  move=> j ji; rewrite !mxE (negbTE ji) /=.
  by rewrite !mul0r !mulr0 subrr.
rewrite !mxE !eqxx /=.
by case: (i == k); case: (i == i'); case: (i == k');
  rewrite /= ?mulr0 ?mul0r ?mulr1 ?mul1r; ring.
Qed.

Lemma coord_cov_frobenius (kap kap' : nat -> R) d :
  frobenius (coord_cov kap d - coord_cov kap' d) ^+ 2 =
  \sum_(j < d) ((kap j - kap' j) / d%:R) ^+ 2.
Proof.
rewrite frobenius_sqr /mxdot big_mxvec_index; apply: eq_bigr => i _.
under eq_bigr => k _ do rewrite big_mxvec_index.
under eq_bigr => k _ do under eq_bigr => i' _ do under eq_bigr => k' _
  do rewrite coord_cov_diff_entry.
rewrite (bigD1 i) //= [X in _ + X = _]big1 ?addr0.
  move=> k ki; rewrite big1 // => i' _; rewrite big1 // => k' _.
  by rewrite [i == k]eq_sym (negbTE ki) /= !mulr0.
rewrite (bigD1 i) //= [X in _ + X = _]big1 ?addr0.
  move=> i' i'i; rewrite big1 // => k' _.
  by rewrite eqxx [i == i']eq_sym (negbTE i'i) /= !mulr0.
rewrite (bigD1 i) //= [X in _ + X = _]big1 ?addr0.
  by move=> k' k'i; rewrite !eqxx [i == k']eq_sym (negbTE k'i) /= !mulr0.
by rewrite !eqxx /= mulr1 expr2.
Qed.

(* The arithmetic of the constants, as in data_feature_regular. *)
Lemma feature_fourth_const (kappa K L : R) d : 1 < kappa -> (0 < d)%N ->
  (kappa - 1) / d%:R <= L ->
  9 * 2 ^+ 33 * K ^+ 8 / d%:R ^+ 2 <=
  (2 ^+ 10 * K ^+ 2 / Num.sqrt (kappa - 1)) ^+ 4 * L ^+ 2.
Proof.
move=> k1 d0 lam.
have kp : 0 < kappa - 1 by rewrite subr_gt0.
have dp : 0 < d%:R :> RR by rewrite ltr0n.
have lam0 : 0 < (kappa - 1) / d%:R by rewrite divr_gt0.
have K8 : 0 <= K ^+ 8 := exprn8_ge0 K.
have e : (2 ^+ 10 * K ^+ 2 / Num.sqrt (kappa - 1)) ^+ 4 =
    2 ^+ 40 * K ^+ 8 / (kappa - 1) ^+ 2.
  have s4 : Num.sqrt (kappa - 1) ^+ 4 = (kappa - 1) ^+ 2.
    by rewrite -[4%N]/(2 * 2)%N exprM sqr_sqrtr // ltW.
  by rewrite expr_div_n s4; ring.
rewrite e.
have l2 : (kappa - 1) ^+ 2 / d%:R ^+ 2 <= L ^+ 2.
  rewrite -expr_div_n ler_pXn2r // nnegrE ?(ltW lam0) //.
  exact: ltW (lt_le_trans lam0 lam).
have kn : kappa - 1 != 0 by rewrite gt_eqF.
have dn : d%:R != 0 :> RR by rewrite gt_eqF.
apply: le_trans (_ : _ <= 2 ^+ 40 * K ^+ 8 / (kappa - 1) ^+ 2 *
  ((kappa - 1) ^+ 2 / d%:R ^+ 2)) _.
  have -> : 2 ^+ 40 * K ^+ 8 / (kappa - 1) ^+ 2 *
      ((kappa - 1) ^+ 2 / d%:R ^+ 2) = 2 ^+ 40 * (K ^+ 8 / d%:R ^+ 2).
    by field.
  have k0 : 0 <= K ^+ 8 / d%:R ^+ 2 by rewrite divr_ge0 // exprn_ge0 // ltW.
  have -> : 9 * 2 ^+ 33 * K ^+ 8 / d%:R ^+ 2 =
      9 * 2 ^+ 33 * (K ^+ 8 / d%:R ^+ 2) by ring.
  by apply: ler_wpM2r => //; lra.
apply: ler_wpM2l => //.
apply: divr_ge0; first by rewrite mulr_ge0 // exprn_ge0.
by rewrite exprn_ge0 // ltW.
Qed.

Lemma sqr_div_le (x M d : R) : 0 < d -> `|x| <= M ->
  (x / d) ^+ 2 <= (M / d) ^+ 2.
Proof.
move=> d0 hx; have := normr_ge0 x.
rewrite !expr_div_n ler_pM2r ?invr_gt0 ?exprn_gt0 //.
rewrite -[x ^+ 2]real_normK ?num_real //; nra.
Qed.

Lemma abs_sub_le (x y M : R) : 0 <= x -> x <= M -> 0 <= y -> y <= M ->
  `|x - y| <= M.
Proof. by move=> *; rewrite ler_norml; apply/andP; split; lra. Qed.

Lemma count_sqr (K : R) d : (0 < d)%N ->
  d%:R * (4 * K ^+ 4 / d%:R) ^+ 2 = 16 * K ^+ 8 / d%:R.
Proof.
move=> d0; have dn : d%:R != 0 :> RR by rewrite pnatr_eq0 -lt0n.
by field.
Qed.

(* 2. The feature law of a mixture. *)

Section mix_feature.
Variables (K : R) (N : nat -> nat) (w : nat -> nat -> R).
Variable mu : nat -> nat -> nat -> probability (measurableTypeR R) R.
Hypothesis hfam : mixture_family K N w mu.

Lemma mix_weights d : mixture_weights (fun s : 'I_(N d) => w d s).
Proof. by have [w0 [w1 _]] := hfam d; split => // s; exact: w0. Qed.

Definition mix_feature_law d : probability 'rV[RR]_(d * d) RR :=
  mixture (fun s : 'I_(N d) => data_feature_law (mu d s) d) (mix_weights d).

Let hcomp d (s : 'I_(N d)) :
  forall j, (j < d)%N -> mixture_component_law K (mu d s j).
Proof. by have [_ [_ hc]] := hfam d; move=> j jd; exact: hc. Qed.

Lemma mix_feature_subexponential d (A : 'M[R]_d) (L : R) :
  (0 < d)%N -> 0 < L -> 252 * K ^+ 2 * frobenius A <= L ->
  subexponential (mix_feature_law d) (fun z => mxdot z (mxvec A) : RR)
    (L / Num.sqrt d%:R).
Proof.
move=> d0 L0 hL; apply: subexponential_mixture => s.
exact: (component_feature_subexponential K d (mu d s) (hcomp d s) A L d0 L0 hL).
Qed.

Lemma mix_feature_quad_subexponential d (v : 'rV[R]_d) :
  (0 < d)%N -> mxdot v v <= 1 ->
  subexponential (mix_feature_law d) (fun z => mxdot z (mxvec (v^T *m v)) : RR)
    (48 * K ^+ 2 / Num.sqrt d%:R).
Proof.
move=> d0 v1; apply: subexponential_mixture => s.
exact: (component_feature_quad_subexponential K d (mu d s) (hcomp d s) v d0 v1).
Qed.

(* Under (M3) the features have the covariance of the universality
   theorem, unsat_cov kappa d. *)
Variable kappa : R.
Hypothesis h4 : mixture_fourth_moment kappa N w mu.

Theorem mix_feature_regular d : 1 < kappa -> (0 < d)%N ->
  regular_feature (2 ^+ 10 * K ^+ 2 / Num.sqrt (kappa - 1))
    (Num.sqrt (2 ^+ 31 * K ^+ 8 / d%:R + 16 * K ^+ 8 / d%:R))
    (unsat_cov kappa d) (mix_feature_law d).
Proof.
move=> k1 d0.
have [w0 [w1 hc]] := hfam d.
pose kap (s : 'I_(N d)) (j : nat) : R :=
  fine (\int[mu d s j]_x ((x : R) ^+ 4)%:E)%E.
have hkap (s : 'I_(N d)) j : (j < d)%N ->
    (\int[mu d s j]_x ((x : R) ^+ 4)%:E = (kap s j)%:E)%E.
  move=> jd; rewrite /kap fineK //; apply: integrable_fin_num => //.
  exact: (component_law_integrable K (mu d s j) (hc s j (ltn_ord s) jd) 4).
have kap0 (s : 'I_(N d)) j : (j < d)%N -> 0 <= kap s j.
  move=> jd; rewrite -lee_fin -hkap //; apply: integral_ge0 => x _.
  by rewrite lee_fin exprn4_ge0.
have kapK (s : 'I_(N d)) j : (j < d)%N -> kap s j <= 4 * K ^+ 4.
  move=> jd; rewrite -lee_fin -hkap //.
  exact: (component_law_fourth_le K (mu d s j) (hc s j (ltn_ord s) jd)).
have hmix j : (j < d)%N -> \sum_(s < N d) w d s * kap s j = kappa.
  move=> jd; apply/EFin_inj; rewrite -sumEFin -(h4 d j jd).
  by apply: eq_bigr => s _; rewrite EFinM -(hkap s j jd) unlock.
have kappa0 : 0 <= kappa.
  rewrite -(hmix 0%N d0); apply: sumr_ge0 => s _.
  by apply: mulr_ge0; [exact: w0 | exact: kap0].
have kappaK : kappa <= 4 * K ^+ 4.
  rewrite -(hmix 0%N d0); apply: (@le_trans _ _ (\sum_(s < N d) w d s * (4 * K ^+ 4))).
    by apply: ler_sum => s _; apply: ler_wpM2l; [exact: w0 | exact: kapK].
  by rewrite -mulr_suml w1 mul1r.
have SigmaE : unsat_cov kappa d = \sum_(s < N d) w d s *: coord_cov (kap s) d.
  rewrite (coord_cov_mix _ _ (fun s : 'I_(N d) => w d s) kap d w1).
  rewrite -coord_cov_const; apply: eq_coord_cov => j jd.
  by rewrite hmix.
have P2 (s : 'I_(N d)) (th th' : 'rV[RR]_(d * d)) :
    ('E_(data_feature_law (mu d s) d)[fun z => (mxdot z th * mxdot z th')%R] =
     (mxdot (th *m coord_cov (kap s) d) th')%:E)%E.
  exact: (component_feature_cov K d (mu d s) (hcomp d s) (kap s) (hkap s) th th').
have P1 (s : 'I_(N d)) (th : 'rV[RR]_(d * d)) :
    ('E_(data_feature_law (mu d s) d)[fun z => mxdot z th] = 0)%E.
  exact: (component_feature_mean K d (mu d s) (hcomp d s) th).
have P4 (s : 'I_(N d)) (th : 'rV[RR]_(d * d)) :
    ('E_(data_feature_law (mu d s) d)[fun z => (mxdot z th ^+ 4)%R] <=
     ((9 * 2 ^+ 33 * K ^+ 8 / d%:R ^+ 2) * mxdot th th ^+ 2)%:E)%E.
  exact: (component_feature_fourth K d (mu d s) (hcomp d s) th).
have K8 := exprn8_ge0 K.
have t0 : 0 <= 2 ^+ 31 * K ^+ 8 / d%:R.
  apply: divr_ge0; last exact: ler0n.
  by apply: mulr_ge0 => //; exact: exprn_ge0 (ler0n _ 2).
have c0 : 0 <= 16 * K ^+ 8 / d%:R.
  apply: divr_ge0; last exact: ler0n.
  by apply: mulr_ge0 => //; exact: ler0n.
have PV (s : 'I_(N d)) (T : 'M[RR]_(d * d)) : T \is symmetricmx ->
    ('V_(data_feature_law (mu d s) d)[fun z => mxdot z (z *m T)] <=
     (Num.sqrt (2 ^+ 31 * K ^+ 8 / d%:R) ^+ 2 * frobenius T ^+ 2)%:E)%E.
  move=> _; rewrite sqr_sqrtr // frobenius_sqr.
  exact: (component_feature_variance K d (mu d s) (hcomp d s) T).
have dp : 0 < d%:R :> RR by rewrite ltr0n.
have lam := unsat_cov_opnorm_ge kappa d d0.
have lam0 : 0 < (kappa - 1) / d%:R by rewrite divr_gt0 // subr_gt0.
have S0 : 0 < opnorm (unsat_cov kappa d) := lt_le_trans lam0 lam.
have spread : \sum_(s < N d) w d s *
    frobenius (coord_cov (kap s) d - unsat_cov kappa d) ^+ 2 <=
    Num.sqrt (16 * K ^+ 8 / d%:R) ^+ 2.
  rewrite sqr_sqrtr //.
  apply: (@le_trans _ _ (\sum_(s < N d) w d s * (16 * K ^+ 8 / d%:R))).
    apply: ler_sum => s _; apply: ler_wpM2l; first exact: w0.
    rewrite -coord_cov_const coord_cov_frobenius.
    apply: (@le_trans _ _ (\sum_(j < d) (4 * K ^+ 4 / d%:R) ^+ 2)).
      apply: ler_sum => j _; apply: sqr_div_le => //; apply: abs_sub_le => //.
      - exact: (kap0 s j (ltn_ord j)).
      - exact: (kapK s j (ltn_ord j)).
    by rewrite sumr_const card_ord -[_ *+ d]mulr_natl (count_sqr K d d0).
  by rewrite -mulr_suml w1 mul1r.
have AK := feature_fourth_const kappa K (opnorm (unsat_cov kappa d)) d k1 d0 lam.
have e : Num.sqrt (2 ^+ 31 * K ^+ 8 / d%:R + 16 * K ^+ 8 / d%:R) =
    Num.sqrt (Num.sqrt (2 ^+ 31 * K ^+ 8 / d%:R) ^+ 2 +
      Num.sqrt (16 * K ^+ 8 / d%:R) ^+ 2).
  by rewrite !sqr_sqrtr.
rewrite e.
exact: (mixture_regular_feature (mix_weights d) P2 P1 P4 PV SigmaE S0 spread AK).
Qed.

End mix_feature.
