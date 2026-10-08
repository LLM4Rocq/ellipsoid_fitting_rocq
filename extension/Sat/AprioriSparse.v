(* The first display of Proposition 3.1 of Koehler and Sohn (arXiv
   2608.27372, lines 2133-2275 of arxiv_v1.tex), at Stdlib's R: the sparse a
   priori estimates. Item S3 of stage 3 of phase 5 (lane C), after
   Sat/Apriori (the second display).

   For a sample x of n points x_i of R^d from a flat family of component
   laws with constant K (Mixture/Flat, as in Sat/Apriori), an m-sparse
   u : 'rV_n (at most m nonzero coordinates, supp of
   library/random_matrix/restricted_isometry) and
   W_i = (x_i x_i^T - I) / sqrt d:
   - sample_comb x u = sum_i u_i x_i, so that |X_I| <= L for every I of
     size at most m is |sample_comb x u| <= L |u| for every m-sparse u;
   - Q_I = (<W_i, W_j> / d)_(i, j in I), so that |Q_I - I| <= delta for
     every I of size at most m is
     | |L_X^* u|_F^2 / d - |u|^2 | <= delta |u|^2 for every m-sparse u
     (L_X^* u = sample_adj x u = sum_i u_i W_i).

   Proved here, for flat families (the names ending in _flat), with the
   statements for universality_sample_law and coordinate laws as
   corollaries under the names without the suffix.
   - point_law: the law of a point as a row vector; for independent
     component laws its linear forms <x, y>, |y| = 1, are centered and
     subgaussian with constant 4 K (point_lin_mean, point_lin_subgaussian,
     from subgaussian_lincomb of library/probability/subgaussian.v).
   - sparse_points_bound_flat (the bound on X_I): for 0 < m <= n and
     s >= 0,
     outside a measurable event of probability at most 2 exp (- s), every
     m-sparse u satisfies
     |sum_i u_i x_i| <= 32 K sqrt (m (1 + ln (n / m)) + 6 (m + d) + s) |u|
     (sparse_norm_subgaussian of restricted_isometry.v).
   - sparse_gram_bound_flat (the bound on Q_I): if the linear forms of the
     feature of each point are centered and subexponential with constant
     252 K^2 / sqrt d (hypotheses hw and cen, as in adjoint_bound_flat),
     then for 0 < m <= n, 0 < beta <= 1/2 and th >= 0, outside a
     measurable event of probability at most
     2 (log_4 m + 2) exp (- sqrt m (1 + ln (n / m))) +
     2 n exp (- d min (th^2 / (576 K^4), th / (12 K^2))), every m-sparse u
     satisfies | |L_X^* u|_F^2 / d - |u|^2 | <= gram_dev |u|^2, where
     gram_dev = (256 T^2 + 32 T sqrt B + 8 beta B) / d + th (2 + th) +
     (3 + 2 th) / d, T = gram_scale is the scale of restricted_isometry
     for the features and B = gram_feature_bound bounds |W_i|_F^2 when
     | |x_i|^2 - d | <= th d (feature_dev_le). For coordinate laws the
     hypotheses hold by data_feature_hw of Sat/Apriori. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets cardinality reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From mathcomp Require Import normedtype sequences exp.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm nets nuclear.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.
From GaussianAnalysis.probability Require Import subgaussian efron_stein.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import Gaussian.Law.LibraryBridge.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Mixture Require Import Component Flat.
From EllipsoidUniversality.Sat Require Import Apriori.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. The law of a point. *)

Section point_law.
Local Open Scope ereal_scope.
Variables (K : R) (d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu : forall j, (j < d)%N -> mixture_component_law K (nu j).

(* The law of a point of the sample, as a row vector. *)
Definition point_law : probability 'rV[RR]_d RR :=
  distribution (tuple_prod nu d) (row_of_tuple d).

Lemma mxdot_row_of_tuple (y : 'rV[R]_d) (t : d.-tuple (measurableTypeR R)) :
  mxdot (row_of_tuple d t) y = (\sum_(j < d) y 0 j * tnth t j)%R.
Proof.
rewrite /mxdot big_ord1; apply: eq_bigr => j _.
by rewrite row_of_tupleE mulrC.
Qed.

Lemma point_lin_mean (y : 'rV[R]_d) :
  \int[point_law]_v (mxdot v y : R)%:E = 0.
Proof.
have mrow : measurable_fun setT (fun v : 'rV[RR]_d => (mxdot v y : R)%:E).
  apply/measurable_EFinP; rewrite /mxdot.
  apply: (eq_measurable_fun (fun v : 'rV[RR]_d =>
    \sum_(j < d) v 0 j * y 0 j)%R).
    by move=> v _; rewrite big_ord1.
  apply: measurable_sum => j.
  apply: measurable_funM; last exact: measurable_cst.
  exact: measurable_mxentry.
rewrite /point_law integral_distribution_measurable //.
have ij (j : 'I_d) : (tuple_prod nu d).-integrable setT
    (fun t : d.-tuple (measurableTypeR R) => (y 0 j * tnth t j)%:E).
  have -> : (fun t : d.-tuple (measurableTypeR R) => (y 0 j * tnth t j)%:E) =
      (fun t => (y 0 j)%:E * (tnth t j : R)%:E).
    by apply/funext => t; rewrite EFinM.
  apply: integrableZl => //.
  apply/integrableP; split.
    by apply/measurable_EFinP; exact: measurable_tnth.
  rewrite (ge0_integral_tuple_prod_coord nu j
    (f := fun x : measurableTypeR R => (`|x| : R)%:E)) //.
    by apply/measurable_EFinP; exact: normr_measurable.
  have := component_law_integrable K (nu j) (hnu j (ltn_ord j)) 1.
  by move/integrableP => [_]; under eq_integral do rewrite expr1.
rewrite (eq_integral (fun t : d.-tuple (measurableTypeR R) =>
  \sum_(j < d) (y 0 j * tnth t j)%:E)).
  by move=> t _; rewrite mxdot_row_of_tuple sumEFin.
rewrite integral_sum //; apply: big1 => j _.
rewrite (integral_tuple_prod_coord nu j
  (f := fun x : measurableTypeR R => (y 0 j * x)%:E)).
  apply/measurable_EFinP; apply: measurable_funM; first exact: measurable_cst.
  exact: measurable_id.
have hj := hnu j (ltn_ord j).
under eq_integral do rewrite EFinM.
rewrite integralZl //.
  have := component_law_integrable K (nu j) hj 1.
  by apply: eq_integrable => // x _; rewrite expr1.
have hm : (\int[nu j]_x (x : R)%:E = 0)%E :=
  component_law_mean K (nu j) hj.
by rewrite hm mule0.
Qed.

Lemma point_lin_subgaussian (y : 'rV[R]_d) : mxdot y y = 1%R ->
  subgaussian point_law (fun v => mxdot v y : RR) (4 * K)%R.
Proof.
move=> y1.
have d0 : (0 < d)%N.
  case: (pickP (fun _ : 'I_d => true)) => [j _ | h].
    exact: leq_ltn_trans (leq0n j) (ltn_ord j).
  have : mxdot y y = 0%R.
    by rewrite /mxdot big_ord1 big1 // => j _; have := h j.
  by rewrite y1 => /eqP; rewrite oner_eq0.
have K0 : (0 < K)%R := component_law_K K (nu 0) (hnu 0 d0).
have mrow : measurable_fun setT (fun v : 'rV[RR]_d => (mxdot v y : RR)).
  rewrite /mxdot.
  apply: (eq_measurable_fun (fun v : 'rV[RR]_d =>
    \sum_(j < d) v 0 j * y 0 j : RR)%R).
    by move=> v _; rewrite big_ord1.
  apply: measurable_sum => j.
  apply: measurable_funM; last exact: measurable_cst.
  exact: measurable_mxentry.
split => //; first by rewrite mulr_gt0.
have mexp : measurable_fun setT (fun v : 'rV[RR]_d =>
    (expR (mxdot v y ^+ 2 / (4 * K) ^+ 2))%:E).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM; [exact: measurable_funX | exact: measurable_cst].
rewrite /point_law integral_distribution_measurable //.
(* sum_j y_j x_j is subgaussian with constant 4 K (subgaussian_lincomb) *)
pose a (k : nat) : R := (if insub k is Some j then y 0 j else 0)%R.
have aE (j : 'I_d) : a j = (y 0 j)%R by rewrite /a valK.
have sg : forall j, (j < d)%N -> subgaussian (nu j) (fun x => x) K.
  by move=> j jd; exact: component_law_subgaussian K (nu j) (hnu j jd).
have m0 : forall j, (j < d)%N -> (\int[nu j]_x x = 0)%R.
  move=> j jd; rewrite /Rintegral.
  by rewrite (component_law_mean K (nu j) (hnu j jd)).
have h := @subgaussian_lincomb _ nu d K a sg m0.
have s1 : (\sum_(i < d) a i ^+ 2 = 1)%R.
  by rewrite -y1 /mxdot big_ord1; apply: eq_bigr => i _; rewrite aE expr2.
have e16 : ((4 * K) ^+ 2 = 16 * K ^+ 2 :> R)%R by ring.
apply: le_trans h; rewrite le_eqVlt; apply/orP; left; apply/eqP.
apply: eq_integral => x _; rewrite s1 mulr1 e16 mxdot_row_of_tuple.
by under [in RHS]eq_bigr do rewrite aE.
Qed.

End point_law.

(* 2. Sparse combinations of the points. *)

Definition sample_comb n d (x : paper_main_sample n d) (u : 'rV[R]_n) :
    'cV[R]_d :=
  \sum_i u 0 i *: paper_main_point x i.

(* The points of a sample, as the rows of their tuples. *)
Definition sample_points n d (x : paper_main_sample n d) : n.-tuple 'rV[RR]_d :=
  tuple_map (fun=> row_of_tuple d) (tuple_rows n d x).

Arguments sample_comb {n d} x u.
Arguments sample_points {n d} x.

Lemma sample_combE n d (x : paper_main_sample n d) (u : 'rV[R]_n) :
  (sample_comb x u)^T = u *m tuple_mx (sample_points x).
Proof.
rewrite tuple_mxE /sample_comb linear_sum; apply: eq_bigr => i _.
rewrite linearZ /= /sample_points /tuple_map tnth_mktuple; congr (_ *: _).
by rewrite paper_main_point_row; apply/rowP => j; rewrite !mxE.
Qed.

(* The bound on |X_I| for flat families of component laws. *)
Theorem sparse_points_bound_flat (K : R) n d
    (lam : nat -> probability (measurableTypeR R) R) (m : nat) (s : R) :
  (forall k, (k < n * d)%N -> mixture_component_law K (lam k)) ->
  (0 < d)%N -> (0 < m)%N -> (m <= n)%N -> (0 <= s)%R ->
  exists G : set (paper_main_sample n d), [/\ measurable G,
    (tuple_prod lam (n * d) (~` G) <= (2 * expR (- s))%:E)%E &
    forall x, G x -> forall u : 'rV[R]_n, (#|supp u| <= m)%N ->
      (frobenius (sample_comb x u) <=
       32 * K * Num.sqrt (m%:R * (1 + ln (n%:R / m%:R)) +
         6 * (m + d)%:R + s) * frobenius u)%R].
Proof.
move=> hlam d0 m0 mn s0.
have n0 : (0 < n)%N by apply: leq_trans m0 mn.
have hrow i : (i < n)%N -> forall j, (j < d)%N ->
    mixture_component_law K (flat_row lam d i j).
  by move=> id j jd; exact: (flat_row_hyp _ _ _ _ hlam i j id jd).
have K0 : (0 < K)%R := component_law_K _ _ (hrow 0%N n0 0%N d0).
have K40 : (0 < 4 * K)%R by rewrite mulr_gt0.
pose pl i := point_law d (flat_row lam d i).
have sub i (y : 'rV[RR]_d) : (i < n)%N -> mxdot y y = 1%R ->
    subgaussian (pl i) (fun v => mxdot v y : RR) (4 * K)%R.
  by move=> id y1; exact: point_lin_subgaussian K d _ (hrow i id) y y1.
have cen i (y : 'rV[RR]_d) : (i < n)%N -> mxdot y y = 1%R ->
    (\int[pl i]_v (mxdot v y : RR) = 0)%R.
  by move=> id _; rewrite /Rintegral (point_lin_mean K d _ (hrow i id) y).
have [Gp [mGp PGp hGp]] := @sparse_norm_subgaussian RR n d pl
  (4 * K)%R K40 sub cen m s m0 mn s0.
(* the event on the samples, by the laws of the points *)
have mP : measurable_fun setT (@sample_points n d).
  apply: measurableT_comp; last exact: measurable_tuple_rows.
  by apply: measurable_tuple_map => i; exact: measurable_row_of_tuple.
have mG : measurable (sample_points @^-1` Gp).
  by rewrite -[X in measurable X]setTI; exact: mP.
exists (sample_points @^-1` Gp); split => //.
  rewrite preimage_setC.
  have e := flat_map_law lam n d _ _ pl (row_of_tuple d) (~` Gp)
    (measurable_row_of_tuple d) (fun i B mB => erefl) (measurableC mGp).
  apply: le_trans PGp.
  exact: (eq_ind_r (fun v => (v <= _)%E) (lexx _) e).
move=> x Gx u um; rewrite -frobenius_trmx sample_combE.
apply: le_trans (hGp _ Gx u um) _.
have e84 : (8 * 4 = 32 :> R)%R by rewrite -natrM.
by rewrite /sparse_norm_bound mulrA e84.
Qed.

Theorem sparse_points_bound (kappa K : R) n d
    (nu : nat -> probability (measurableTypeR R) R) (m : nat) (s : R) :
  (forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j)) ->
  (0 < d)%N -> (0 < m)%N -> (m <= n)%N -> (0 <= s)%R ->
  exists G : set (paper_main_sample n d), [/\ measurable G,
    (universality_sample_law nu n d (~` G) <= (2 * expR (- s))%:E)%E &
    forall x, G x -> forall u : 'rV[R]_n, (#|supp u| <= m)%N ->
      (frobenius (sample_comb x u) <=
       32 * K * Num.sqrt (m%:R * (1 + ln (n%:R / m%:R)) +
         6 * (m + d)%:R + s) * frobenius u)%R].
Proof.
move=> hnu; exact: (sparse_points_bound_flat K n d (fun k => nu (k %% d)%N) m s
  (sample_law_component kappa K n d nu hnu)).
Qed.

(* 3. The Gram matrices of sparse sets of features. *)

(* |W|_F^2 - d for a point with | |x|^2 - d | <= th d: with s = |x|^2,
   |W|_F^2 = (s^2 - 2 s + d) / d (mxdot_sample_W). *)
Lemma feature_dev_le (s dR th : R) : (0 < dR)%R -> (0 <= th)%R ->
  (`|s - dR| <= th * dR)%R ->
  (`|(s ^+ 2 - 2 * s + dR) / dR - dR| <=
   dR * (th * (2 + th)) + (3 + 2 * th))%R.
Proof.
move=> d0 th0 hs.
have dn : dR != 0 by rewrite gt_eqF.
have -> : ((s ^+ 2 - 2 * s + dR) / dR - dR =
    ((s - dR) ^+ 2 + 2 * dR * (s - dR) - 2 * (s - dR) - dR) / dR)%R.
  by field.
move: hs; set e := (s - dR)%R => hs.
rewrite normrM normfV (gtr0_norm d0) ler_pdivrMr //.
have hth : (0 <= th * dR)%R by rewrite mulr_ge0 // ltW.
have e1 : (- (th * dR) <= e <= th * dR)%R by rewrite -ler_norml.
have e2 : (e ^+ 2 <= (th * dR) ^+ 2)%R.
  rewrite -[e ^+ 2]real_normK ?num_real //.
  by rewrite ler_sqr ?nnegrE ?normr_ge0.
have de : (- (th * dR * dR) <= dR * e <= th * dR * dR)%R.
  move: e1 => /andP[e1 e1']; apply/andP; split.
    by rewrite -mulNr [dR * e]mulrC ler_wpM2r // ltW.
  by rewrite [dR * e]mulrC ler_wpM2r // ltW.
move: e1 e2 de => /andP[e1 e1'] e2 /andP[de de'].
rewrite exprMn in e2.
have t2 : (0 <= th ^+ 2 * dR ^+ 2)%R by rewrite mulr_ge0 ?sqr_ge0.
have es : (0 <= e ^+ 2)%R := sqr_ge0 e.
clearbody e.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

Section sparse_gram_flat.
Variables (K : R) (n d m : nat).
Variable lam : nat -> probability (measurableTypeR R) R.
Hypothesis hlam : forall k, (k < n * d)%N -> mixture_component_law K (lam k).
(* The linear forms of the feature of each point are subexponential with
   constant 252 K^2 / sqrt d and centered. *)
Hypothesis hw : forall i (y : 'rV[R]_(d * d)), (i < n)%N -> mxdot y y = 1%R ->
  subexponential (data_feature_law (flat_row lam d i) d) (fun z => mxdot z y)
    (252 * K ^+ 2 / Num.sqrt d%:R)%R.
Hypothesis cen : forall i (y : 'rV[R]_(d * d)), (i < n)%N -> mxdot y y = 1%R ->
  (\int[data_feature_law (flat_row lam d i) d]_v mxdot v y = 0)%R.
Hypotheses (d0 : (0 < d)%N) (m0 : (0 < m)%N) (mn : (m <= n)%N).
Variables (beta th : R).
Hypotheses (beta0 : (0 < beta)%R) (beta1 : (beta <= 1 / 2)%R).
Hypothesis th0 : (0 <= th)%R.

(* The scale T of the restricted isometry theorem for the features, whose
   linear forms are subexponential with constant 252 K^2 / sqrt d
   (data_feature_hw). *)
Definition gram_scale : R :=
  rip_T n m (252 * K ^+ 2 / Num.sqrt d%:R)%R beta 1.

(* |W_i|_F^2 <= gram_feature_bound when | |x_i|^2 - d | <= th d. *)
Definition gram_feature_bound : R :=
  (d%:R * (1 + th * (2 + th)) + (3 + 2 * th))%R.

(* The isometry defect of the Gram matrices Q_I. *)
Definition gram_dev : R :=
  ((256 * gram_scale ^+ 2 + 32 * gram_scale * Num.sqrt gram_feature_bound +
    8 * beta * gram_feature_bound) / d%:R +
   th * (2 + th) + (3 + 2 * th) / d%:R)%R.

(* The bound on Q_I: outside a measurable event of the stated probability,
   | |sum_i u_i W_i|_F^2 / d - |u|^2 | <= gram_dev |u|^2 for every m-sparse
   u. *)
Theorem sparse_gram_bound_flat :
  exists G : set (paper_main_sample n d), [/\ measurable G,
    (tuple_prod lam (n * d) (~` G) <=
      (2 * (trunc_log 4 m).+2%:R *
         expR (- (Num.sqrt m%:R * (1 + ln (n%:R / m%:R)))) +
       n%:R * (2 * expR (- Num.min (th ^+ 2 * d%:R / (576 * K ^+ 4))
                                   (th * d%:R / (12 * K ^+ 2)))))%:E)%E &
    forall x, G x -> forall u : 'rV[R]_n, (#|supp u| <= m)%N ->
      (`|frobenius (sample_adj x u) ^+ 2 / d%:R - mxdot u u| <=
       gram_dev * mxdot u u)%R].
Proof.
have K0 : (0 < K)%R.
  apply: (component_law_K _ (lam 0)); apply: hlam.
  by rewrite muln_gt0 d0 andbT; apply: leq_trans m0 mn.
set psi := (252 * K ^+ 2 / Num.sqrt d%:R)%R.
have sd0 : (0 < Num.sqrt d%:R :> R)%R by rewrite sqrtr_gt0 ltr0n.
have psi0 : (0 < psi)%R by rewrite /psi !mulr_gt0 ?invr_gt0 ?exprn_gt0.
pose mu i := data_feature_law (flat_row lam d i) d.
have sub i (y : 'rV[R]_(d * d)) : (i < n)%N -> mxdot y y = 1%R ->
    subexponential (mu i) (fun v => mxdot v y) psi.
  exact: hw.
have cen' i (y : 'rV[R]_(d * d)) : (i < n)%N -> mxdot y y = 1%R ->
    (\int[mu i]_v mxdot v y = 0)%R.
  exact: cen.
(* the restricted isometry theorem for the features, with K = 1 *)
have [Gf [mGf PGf hGf]] := @restricted_isometry RR n (d * d) m
  mu psi psi0 sub cen' beta 1 m0 mn beta0 beta1 (lexx _).
have mF : measurable (unsat_features n d @^-1` Gf).
  rewrite -[X in measurable X]setTI.
  exact: (measurable_unsat_features n d) measurableT Gf mGf.
have mN := measurable_norm_good n d th.
exists (unsat_features n d @^-1` Gf `&` norm_good n d th); split.
- exact: measurableI.
- rewrite setCI; apply: le_trans (measureU2 _ _ _) _.
  + exact: measurableC.
  + exact: measurableC.
  rewrite EFinD; apply: leeD.
    have e := flat_features_law lam n d (~` Gf) (measurableC mGf).
    apply: (@le_trans _ _ (tuple_prod mu n (~` Gf))).
      rewrite preimage_setC.
      exact: (eq_ind_r (fun v => (v <= _)%E) (lexx _) e).
    by apply: le_trans PGf _; rewrite mul1r.
  exact: (norm_good_prob_flat K n d lam hlam th th0).
move=> x [/= hGx hNx] u um.
set X := unsat_features n d x.
have dR : (0 < d%:R :> R)%R by rewrite ltr0n.
(* the squared norms of the features *)
have hdev (i : 'I_n) : (`|mxdot (tnth X i) (tnth X i) - d%:R| <=
    d%:R * (th * (2 + th)) + (3 + 2 * th))%R.
  rewrite /X -mxvec_sample_W mxdot_mxvec mxdot_sample_W //.
  by apply: feature_dev_le => //; exact: ltW (hNx i).
set D0 := (d%:R * (th * (2 + th)) + (3 + 2 * th))%R in hdev.
have D00 : (0 <= D0)%R.
  have h1 : (0 <= d%:R * (th * (2 + th)))%R.
    have t2 : (0 <= 2 + th)%R := addr_ge0 (ler0n _ 2) th0.
    exact: mulr_ge0 (ler0n _ _) (mulr_ge0 th0 t2).
  have t3 : (0 <= 3 + 2 * th)%R :=
    addr_ge0 (ler0n _ 3) (mulr_ge0 (ler0n _ 2) th0).
  exact: addr_ge0 h1 t3.
have GF : gram_feature_bound = (d%:R + D0)%R.
  by rewrite /gram_feature_bound /D0; ring.
have hsq (i : 'I_n) : (mxdot (tnth X i) (tnth X i) <= gram_feature_bound)%R.
  have := hdev i; rewrite ler_norml => /andP[_ h].
  by rewrite GF addrC -lerBlDr.
have GF0 : (0 <= gram_feature_bound)%R by rewrite GF addr_ge0 // ltW.
have hmax : (maxnorm X <= Num.sqrt gram_feature_bound)%R.
  rewrite /maxnorm; apply: bigmax_le; first exact: sqrtr_ge0.
  by move=> i _; rewrite /frobenius ler_wsqrtr.
(* the restricted isometry constant *)
have T0 : (0 <= gram_scale)%R.
  rewrite /gram_scale /rip_T -/psi.
  have l1 : (0 <= ln (n%:R / m%:R : RR))%R.
    by rewrite ln_ge0 // ler_pdivlMr ?ltr0n // mul1r ler_nat.
  have b1 : (beta <= 1)%R.
    by apply: le_trans beta1 _; rewrite ler_pdivrMr //; lra.
  have l2 : (ln beta <= 0)%R by rewrite ln_le0.
  apply: mulr_ge0; last by lra.
  by rewrite !mulr_ge0 ?sqrtr_ge0 ?ler0n // ltW.
have gsE : rip_T n m psi beta 1 = gram_scale by [].
have hrip : (rip_const m X <= 256 * gram_scale ^+ 2 +
    32 * gram_scale * Num.sqrt gram_feature_bound +
    8 * beta * gram_feature_bound)%R.
  apply: le_trans (hGf X hGx) _; rewrite gsE.
  apply: lerD; first apply: lerD => //.
    by apply: ler_wpM2l => //; rewrite mulr_ge0.
  apply: ler_wpM2l; first by rewrite mulr_ge0 // ltW.
  rewrite -[X in (_ <= X)%R](sqr_sqrtr GF0).
  by rewrite ler_sqr ?nnegrE ?maxnorm_ge0 ?sqrtr_ge0.
(* | |u X|^2 - d |u|^2 | <= (rip_const + D0) |u|^2 *)
have key : (`|mxdot (u *m tuple_mx X) (u *m tuple_mx X) -
    d%:R * mxdot u u| <= (rip_const m X + D0) * mxdot u u)%R.
  have uu : mxdot u u = (\sum_i u 0 i * u 0 i)%R by rewrite /mxdot big_ord1.
  have -> : (mxdot (u *m tuple_mx X) (u *m tuple_mx X) - d%:R * mxdot u u =
      gram_off X u u +
      \sum_i u 0 i * u 0 i * (mxdot (tnth X i) (tnth X i) - d%:R))%R.
    rewrite /gram_off uu mulr_sumr.
    under [X in _ = _ + X]eq_bigr do rewrite mulrBr.
    by rewrite sumrB; under [X in _ = _ + (_ - X)]eq_bigr do rewrite mulrC;
      ring.
  rewrite mulrDl; apply: le_trans (ler_normD _ _) _; apply: lerD.
    exact: gram_off_rip.
  apply: le_trans (ler_norm_sum _ _ _) _.
  rewrite uu mulr_sumr; apply: ler_sum => i _.
  have u2 : (0 <= u 0 i * u 0 i)%R by rewrite -expr2 sqr_ge0.
  by rewrite normrM (ger0_norm u2) mulrC ler_wpM2r // hdev.
have dn : d%:R != 0 :> R by rewrite gt_eqF.
rewrite frobenius_sample_adj frobenius_sqr -/X.
have -> : (mxdot (u *m tuple_mx X) (u *m tuple_mx X) / d%:R - mxdot u u =
    (mxdot (u *m tuple_mx X) (u *m tuple_mx X) - d%:R * mxdot u u) /
    d%:R)%R by field.
rewrite normrM normfV (gtr0_norm dR) ler_pdivrMr //.
apply: le_trans key _.
rewrite [X in (_ <= X)%R]mulrAC; apply: ler_wpM2r; first exact: mxdot_ge0.
have -> : (gram_dev * d%:R = 256 * gram_scale ^+ 2 +
    32 * gram_scale * Num.sqrt gram_feature_bound +
    8 * beta * gram_feature_bound + D0)%R.
  by rewrite /gram_dev /D0; field.
by rewrite lerD2r.
Qed.

End sparse_gram_flat.

Section sparse_gram.
Variables (kappa K : R) (n d m : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu :
  forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j).
Hypotheses (d0 : (0 < d)%N) (m0 : (0 < m)%N) (mn : (m <= n)%N).
Variables (beta th : R).
Hypotheses (beta0 : (0 < beta)%R) (beta1 : (beta <= 1 / 2)%R).
Hypothesis th0 : (0 <= th)%R.

(* The bound on Q_I: outside a measurable event of the stated probability,
   | |sum_i u_i W_i|_F^2 / d - |u|^2 | <= gram_dev |u|^2 for every m-sparse
   u. *)
Theorem sparse_gram_bound :
  exists G : set (paper_main_sample n d), [/\ measurable G,
    (universality_sample_law nu n d (~` G) <=
      (2 * (trunc_log 4 m).+2%:R *
         expR (- (Num.sqrt m%:R * (1 + ln (n%:R / m%:R)))) +
       n%:R * (2 * expR (- Num.min (th ^+ 2 * d%:R / (576 * K ^+ 4))
                                   (th * d%:R / (12 * K ^+ 2)))))%:E)%E &
    forall x, G x -> forall u : 'rV[R]_n, (#|supp u| <= m)%N ->
      (`|frobenius (sample_adj x u) ^+ 2 / d%:R - mxdot u u| <=
       gram_dev K n d m beta th * mxdot u u)%R].
Proof.
exact: (sparse_gram_bound_flat K n d m _
  (sample_law_component kappa K n d nu hnu)
  (sample_law_feature_hw kappa K n d nu hnu d0)
  (sample_law_feature_mean kappa K n d nu hnu) d0 m0 mn beta th beta0 beta1 th0).
Qed.

End sparse_gram.
