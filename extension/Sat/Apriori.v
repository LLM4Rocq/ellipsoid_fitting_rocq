(* The a priori estimates: Proposition 3.1 of Koehler and Sohn (arXiv
   2608.27372, lines 2133-2300 of arxiv_v1.tex), at Stdlib's R. Item S3 of
   stage 3 of phase 5 (lane C), with
   library/random_matrix/restricted_isometry.v, for flat families since
   item X2 of phase 6.

   For a sample x of n points x_i of R^d (paper_main_point), the matrices
   W_i = (x_i x_i^T - I) / sqrt d (sample_W), the map
   L_X^* z = sum_i z_i W_i (sample_adj, the coef_adj of matrix/nuclear.v)
   and its adjoint L_X D = (<W_i, D>)_i (sample_map). The samples are flat
   families (Mixture/Flat): the n * d coordinates are independent and
   coordinate k has law lam k, a component law with constant K
   (mixture_component_law of MixtureDefinitions). The statements for
   universality_sample_law nu n d, with the coordinate laws of
   universality_coordinate_law kappa K, are corollaries
   (sample_law_component: it is the flat family k |-> nu (k mod d)).

   Proved:
   - sample_row_law: each point of a sample of universality_sample_law
     has the law tuple_prod nu d.
   - sqnorm_tail_component, norm_good_prob_flat: Bernstein's inequality
     for |x|^2 - d, P(| |x|^2 - d | >= th d) <= 2 exp (- d min (th^2 /
     (576 K^4), th / (12 K^2))) for a point of independent component laws,
     and the event norm_good n d th that every point has
     | |x_i|^2 - d | < th d, whose complement has probability at most n
     times this bound; sqnorm_tail and norm_good_prob for coordinate laws.
   - mxdot_sample_W, sqnorm_feature_le: |W_i|_F^2 = (s^2 - 2 s + d) / d
     with s = |x_i|^2, hence |W_i|_F^2 <= 5 d on norm_good n d 1.
   - adjoint_bound_flat, the second display of Proposition 3.1: let the
     linear forms of the feature of each point be centered and
     subexponential with constant Chw K^2 / sqrt d (hypotheses hw and
     cen), d > 0 and 1 <= n <= C0 d^2 with C0 >= 1. Outside a measurable
     event of probability at most
     2 (log_4 m + 2) exp (- sqrt m) +
     2 n exp (- min (d / (576 K^4), d / (12 K^2))), m = min (n, d^2),
     every point has | |x_i|^2 - d | < d and every z satisfies
     |L_X^* z|_F <= adj_const sqrt d |z|, where adj_const depends only on
     Chw, K and C0: restricted_isometry for the features at m with
     beta = 1/2 (rip_T_feature_le, rip_bound_alg), then
     tuple_mx_blocks. adjoint_bound is the case of universality_sample_law;
     for it, data_feature_hw proves hw with Chw = 252 from the
     Hanson-Wright inequality of lane A (data_feature_subexponential of
     Features/Regular), adjoint_bound_data is adjoint_bound without hw, and
     sample_law_feature_hw and sample_law_feature_mean give the hypotheses
     of adjoint_bound_flat.
   - nuclear_sample_adj_le, frobenius_sample_map_le: on that event,
     nuclear (L_X^* z) <= adj_const d |z| (Proposition 3.1 (iii), by
     nuclear_le_frobenius) and |L_X D| <= adj_const sqrt d |D|_F (by
     duality).

   - adjoint_bound_limit_features: the same with probability tending to
     one when n / d^2 tends to alpha > 0, with C = adj_const K 252
     (alpha + 1), for flat families of component laws with the hypotheses
     hw (Chw = 252) and cen; the threshold D comes before the laws. The
     failure probability is at most 12 / sqrt (min (n, d^2)) +
     12 (alpha + 1) / (c^3 d) (trunc_log_expR_le, sqr_expR_le).
     adjoint_bound_limit is the case of universality_sample_law, and
     adjoint_bound_limit_flat the case of any flat family of component
     laws: for them hw and cen hold by flat_feature_hw and
     flat_feature_mean, from the bounds of Features/Regular for component
     laws.

   The first display of Proposition 3.1, on the Gram matrices Q_I and on
   |X_I| for small sets I, is in Sat/AprioriSparse. *)

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
From GaussianAnalysis.probability Require Import subgaussian.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Mixture Require Import Component Flat.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. The maps L_X and L_X^* of a sample. *)

Section sample_maps.
Variables (n d : nat) (x : paper_main_sample n d).

(* W_i = (x_i x_i^T - I) / sqrt d. *)
Definition sample_W (i : 'I_n) : 'M[R]_d :=
  (Num.sqrt d%:R)^-1 *:
    (paper_main_point x i *m (paper_main_point x i)^T - 1%:M).

(* L_X^* z = sum_i z_i W_i and L_X D = (<W_i, D>)_i. *)
Definition sample_adj (z : 'rV[R]_n) : 'M[R]_d := coef_adj sample_W z.

Definition sample_map (D : 'M[R]_d) : 'rV[R]_n := coef_map sample_W D.

Lemma mxvec_sample_W i : mxvec (sample_W i) = tnth (unsat_features n d x) i.
Proof. by rewrite /unsat_features tnth_mktuple. Qed.

Lemma mxvec_sample_adj z :
  mxvec (sample_adj z) = z *m tuple_mx (unsat_features n d x).
Proof.
rewrite tuple_mxE /sample_adj /coef_adj linear_sum; apply: eq_bigr => i _.
by rewrite linearZ /= mxvec_sample_W.
Qed.

Lemma frobenius_sample_adj z :
  frobenius (sample_adj z) = frobenius (z *m tuple_mx (unsat_features n d x)).
Proof. by rewrite -mxvec_sample_adj /frobenius mxdot_mxvec. Qed.

End sample_maps.

Arguments sample_W {n d} x i.
Arguments sample_adj {n d} x z.
Arguments sample_map {n d} x D.

(* 2. The concentration of the norm of a point. *)

Section norm_concentration.
Local Open Scope ereal_scope.
Variables (K : R) (d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu : forall j, (j < d)%N -> mixture_component_law K (nu j).

(* Bernstein's inequality for the centered subexponential x_j^2 - 1:
   P(| |x|^2 - d | >= th d)
     <= 2 exp (- d min (th^2 / (576 K^4), th / (12 K^2))). *)
Lemma sqnorm_tail_component (th : R) : (0 <= th)%R ->
  tuple_prod nu d
    [set t | th * d%:R <= `|\sum_(j < d) tnth t j ^+ 2 - d%:R|]%R <=
  (2 * expR (- Num.min (th ^+ 2 * d%:R / (576 * K ^+ 4))
                       (th * d%:R / (12 * K ^+ 2))))%:E.
Proof.
move=> th0.
pose f (j : nat) (s : measurableTypeR R) : RR := ((s : R) ^+ 2 - 1)%R.
have sf j : (j < d)%N -> subexponential (nu j) (f j) (3 * K ^+ 2)%R.
  move=> jd; have hm := hnu j jd.
  have := subexponential_center
    (subexponential_sqr (component_law_subgaussian _ _ hm)).
  have -> : (\int[nu j]_s (id s ^+ 2) = 1 :> R)%R.
    by rewrite /Rintegral (component_law_second _ _ hm).
  by [].
have cf j : (j < d)%N -> (\int[nu j]_s f j s = 0)%R.
  move=> jd; have hm := hnu j jd.
  rewrite /f RintegralB //; first exact: (component_law_integrable _ _ hm 2).
    exact: finite_measure_integrable_cst.
  rewrite {1}/Rintegral (component_law_second _ _ hm) Rintegral_cst //=.
  by rewrite probability_setT /= mul1r subrr.
have td0 : (0 <= th * d%:R)%R by rewrite mulr_ge0.
have := bernstein_sum sf cf td0.
have -> : [set x | (th * d%:R <= `|\sum_(i < d) f i (tnth x i)|)%R] =
    [set t | (th * d%:R <= `|\sum_(j < d) tnth t j ^+ 2 - d%:R|)%R].
  apply/seteqP; split => t /=; rewrite /f sumrB sumr_const card_ord;
    by rewrite -[(1 *+ d)%R]mulr_natl mulr1.
have -> : ((th * d%:R) ^+ 2 / (64 * d%:R * (3 * K ^+ 2) ^+ 2) =
    th ^+ 2 * d%:R / (576 * K ^+ 4))%R.
  have [d0|d0] := eqVneq (d%:R : R) 0%R.
    by rewrite d0 !(mulr0, mul0r, invr0, expr0n).
  have [K0|K0] := eqVneq K 0%R.
    by rewrite K0 !(mulr0, mul0r, invr0, expr0n).
  by field; rewrite d0 K0.
by have -> : (4 * (3 * K ^+ 2) = 12 * K ^+ 2)%R by ring.
Qed.

End norm_concentration.

Section norm_concentration_coordinate.
Local Open Scope ereal_scope.
Variables (kappa K : R) (d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu :
  forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j).

Lemma sqnorm_tail (th : R) : (0 <= th)%R ->
  tuple_prod nu d
    [set t | th * d%:R <= `|\sum_(j < d) tnth t j ^+ 2 - d%:R|]%R <=
  (2 * expR (- Num.min (th ^+ 2 * d%:R / (576 * K ^+ 4))
                       (th * d%:R / (12 * K ^+ 2))))%:E.
Proof.
apply: sqnorm_tail_component => j jd.
exact: coordinate_law_component (hnu j jd).
Qed.

End norm_concentration_coordinate.

Section sample_norms.
Local Open Scope ereal_scope.
Variables (n d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.

(* The law of one row of a sample. *)
Lemma sample_row_law (B : set (d.-tuple (measurableTypeR R))) (i : 'I_n) :
  measurable B ->
  universality_sample_law nu n d [set x | B (tnth (tuple_rows n d x) i)] =
  tuple_prod nu d B.
Proof.
move=> mB.
have mA : measurable
    [set y : n.-tuple (d.-tuple (measurableTypeR R)) | B (tnth y i)].
  rewrite -[X in measurable X]setTI.
  by apply: (measurable_tnth i) => //.
have := @sample_map_law nu n d _ _ (tuple_prod nu d) idfun _
  (@measurable_id _ _ _) _ mA.
move=> /(_ (fun B0 _ => erefl)) h.
rewrite -(@tuple_prod_tnth _ _ (fun=> tuple_prod nu d) n i B mB) -h.
congr (universality_sample_law nu n d _); apply/seteqP; split => x /=.
  by move=> h1; rewrite /tuple_map tnth_mktuple.
by rewrite /tuple_map tnth_mktuple.
Qed.

Lemma mxdot_point (t : d.-tuple (measurableTypeR R)) :
  mxdot (tuple_point t) (tuple_point t) = (\sum_(j < d) tnth t j ^+ 2)%R.
Proof.
rewrite /mxdot; apply: eq_bigr => j _.
by rewrite big_ord1 !mxE expr2.
Qed.

(* Every point has | |x_i|^2 - d | < th d. *)
Definition norm_good (th : R) : set (paper_main_sample n d) :=
  [set x | forall i : 'I_n,
    `|mxdot (paper_main_point x i) (paper_main_point x i) - d%:R| <
    th * d%:R]%R.

Lemma measurable_norm_good th : measurable (norm_good th).
Proof.
have -> : norm_good th = \bigcap_(i in [set: 'I_n])
    [set x : paper_main_sample n d |
      `|\sum_(j < d) tnth (tnth (tuple_rows n d x) i) j ^+ 2 - d%:R| <
      th * d%:R]%R.
  apply/seteqP; split => x /=.
    move=> h i _ /=; rewrite -mxdot_point -paper_main_point_row; exact: h.
  by move=> h i; rewrite paper_main_point_row mxdot_point; exact: (h i).
apply: fin_bigcap_measurable => // i _.
rewrite -[X in measurable X]setTI.
apply: measurable_fun_ltr => //; apply: measurableT_comp => //.
apply: measurable_funB => //; apply: measurable_sum => j.
apply: measurable_funX; apply: measurableT_comp (measurable_tnth j) _.
apply: measurableT_comp (measurable_tnth i) _.
exact: measurable_tuple_rows.
Qed.

End sample_norms.

Section flat_norms.
Local Open Scope ereal_scope.
Variables (K : R) (n d : nat).
Variable lam : nat -> probability (measurableTypeR R) R.
Hypothesis hlam : forall k, (k < n * d)%N -> mixture_component_law K (lam k).

(* Every point has | |x_i|^2 - d | < th d, except on an event of probability
   at most n times the bound of sqnorm_tail_component. *)
Lemma norm_good_prob_flat th : (0 <= th)%R ->
  tuple_prod lam (n * d) (~` norm_good n d th) <=
  (n%:R * (2 * expR (- Num.min (th ^+ 2 * d%:R / (576 * K ^+ 4))
                                (th * d%:R / (12 * K ^+ 2)))))%:E.
Proof.
move=> th0.
pose B : set (d.-tuple (measurableTypeR R)) :=
  [set t | th * d%:R <= `|\sum_(j < d) tnth t j ^+ 2 - d%:R|]%R.
have mB : measurable B.
  rewrite -[X in measurable X]setTI /B; apply: measurable_fun_ler => //.
  apply: (measurableT_comp (@normr_measurable _ _)) => //.
  apply: measurable_funB => //; apply: measurable_sum => j.
  exact: measurable_funX (measurable_tnth j).
pose E (i : 'I_n) :=
  [set x : paper_main_sample n d | B (tnth (tuple_rows n d x) i)].
have mE i : measurable (E i).
  rewrite -[X in measurable X]setTI.
  have mf : measurable_fun [set: paper_main_sample n d]
      (fun x => tnth (tuple_rows n d x) i).
    apply: measurableT_comp (measurable_tnth i) _.
    exact: measurable_tuple_rows.
  exact: mf measurableT B mB.
have sub : ~` norm_good n d th `<=` \big[setU/set0]_(i <- enum 'I_n) E i.
  move=> x /= /existsNP [i /negP]; rewrite -leNgt => h.
  apply: (bigsetU_mem (mem_enum _ i)).
  by rewrite /E /B /= -mxdot_point -paper_main_point_row.
have mU : measurable (\big[setU/set0]_(i <- enum 'I_n) E i).
  by apply: bigsetU_measurable => i _; exact: mE.
apply: le_trans (le_measure _ _ _ sub) _.
- by rewrite inE; apply: measurableC; exact: measurable_norm_good.
- by rewrite inE.
apply: le_trans (measure_bigsetU_le _ _ mE) _.
have PE i : tuple_prod lam (n * d) (E i) = tuple_prod (flat_row lam d i) d B.
  exact: flat_row_law.
apply: le_trans (_ : \sum_(i <- enum 'I_n)
    (2 * expR (- Num.min (th ^+ 2 * d%:R / (576 * K ^+ 4))
                         (th * d%:R / (12 * K ^+ 2))))%:E <= _).
  apply: lee_sum => i _.
  have hrow j : (j < d)%N -> mixture_component_law K (flat_row lam d i j).
    exact: (flat_row_hyp _ _ _ _ hlam i j (ltn_ord i)).
  have h := sqnorm_tail_component _ _ _ hrow _ th0.
  exact: (eq_ind_r (fun v => (v <= _)%E) h (PE i)).
rewrite sumEFin lee_fin big_const_seq count_predT iter_addr addr0.
by rewrite size_enum_ord -[(_ *+ n)%R]mulr_natl.
Qed.

End flat_norms.

(* universality_sample_law nu n d is the flat family k |-> nu (k mod d); for
   coordinate laws, its coordinate laws are component laws. *)
Lemma sample_law_component (kappa K : R) (n d : nat)
    (nu : nat -> probability (measurableTypeR R) R) :
  (forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j)) ->
  forall k, (k < n * d)%N -> mixture_component_law K (nu (k %% d)%N).
Proof.
move=> hnu k kn; have d0 : (0 < d)%N.
  by rewrite lt0n; apply/eqP => d0; move: kn; rewrite d0 muln0 ltn0.
exact: coordinate_law_component (hnu _ (ltn_pmod _ d0)).
Qed.

Section sample_norms_coordinate.
Local Open Scope ereal_scope.
Variables (kappa K : R) (n d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu :
  forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j).

Lemma norm_good_prob th : (0 <= th)%R ->
  universality_sample_law nu n d (~` norm_good n d th) <=
  (n%:R * (2 * expR (- Num.min (th ^+ 2 * d%:R / (576 * K ^+ 4))
                                (th * d%:R / (12 * K ^+ 2)))))%:E.
Proof.
exact: (norm_good_prob_flat K n d _ (sample_law_component kappa K n d nu hnu)).
Qed.

End sample_norms_coordinate.

(* 3. The squared norm of a feature. *)

Lemma mxdot_sample_W n d (x : paper_main_sample n d) (i : 'I_n) :
  let s := mxdot (paper_main_point x i) (paper_main_point x i) in
  (0 < d)%N ->
  mxdot (sample_W x i) (sample_W x i) = ((s ^+ 2 - 2 * s + d%:R) / d%:R)%R.
Proof.
move=> s d0.
have sd : (Num.sqrt d%:R)^-1 ^+ 2 = (d%:R)^-1 :> R.
  by rewrite exprVn sqr_sqrtr ?ler0n.
rewrite /sample_W mxdotZl mxdotZr mulrA -expr2 sd mxdotBl !mxdotBr.
rewrite mxdot_outer2 [mxdot (_ *m _^T) 1%:M]mxdotC !mxdot_outer mulmx1.
rewrite -mxdot_colE [mxdot 1%:M 1%:M]mxdot_trace trmx1 mulmx1 mxtrace1 -/s.
by rewrite mulrC expr2; congr (_ / _); ring.
Qed.

Lemma sqnorm_feature_le n d (x : paper_main_sample n d) (i : 'I_n) :
  (0 < d)%N -> norm_good n d 1 x ->
  (mxdot (tnth (unsat_features n d x) i) (tnth (unsat_features n d x) i)
    <= 5 * d%:R)%R.
Proof.
move=> d0 /(_ i); rewrite mul1r => hs.
rewrite -mxvec_sample_W mxdot_mxvec mxdot_sample_W //.
set s := mxdot _ _ in hs *.
have dpos : (0 < d%:R :> R)%R by rewrite ltr0n.
have s0 : (0 <= s)%R by rewrite /s mxdot_ge0.
have s2 : (s <= 2 * d%:R)%R by move: hs; rewrite ltr_norml; lra.
rewrite ler_pdivrMr //.
have d1 : (1 <= d%:R :> R)%R by rewrite ler1n.
nra.
Qed.

(* 4. The operator norm of L_X^*: |L_X^* z|_F <= C sqrt d |z|. *)

(* The scale of the restricted isometry theorem for the features. *)
Lemma rip_T_feature_le (Chw K C0 : R) (n m d : nat) :
  (0 < Chw)%R -> (0 < K)%R -> (1 <= C0)%R -> (0 < d)%N -> (0 < m)%N ->
  (m <= n)%N -> (Num.sqrt m%:R <= d%:R :> R)%R -> (n%:R / m%:R <= C0)%R ->
  (0 <= rip_T n m (Chw * K ^+ 2 / Num.sqrt d%:R) (1 / 2) 1 <=
    2100 * Chw * K ^+ 2 * (2 + C0) * Num.sqrt d%:R)%R.
Proof.
move=> Chw0 K0 C01 d0 m0 mn md nmC.
have nm1 : (1 <= n%:R / m%:R :> R)%R.
  by rewrite ler_pdivlMr ?ltr0n // mul1r ler_nat.
have l2 := @ln2_le1 RR.
have lnm0 : (0 <= ln (n%:R / m%:R : RR))%R by rewrite ln_ge0.
have lnmC : (ln (n%:R / m%:R : RR) <= C0)%R.
  apply: le_trans (ln_le_sub1 _) _; first by apply: lt_le_trans nm1; lra.
  by rewrite lerBlDr; apply: le_trans nmC _; rewrite lerDl.
have lh : (ln (1 / 2 : RR) = - ln (2 : RR))%R by rewrite div1r lnV ?posrE.
have l20 : (0 <= ln (2 : RR))%R by rewrite ln_ge0 // ler1n.
have A0 : (0 <= 1 + ln (n%:R / m%:R : RR) - ln (1 / 2 : RR))%R.
  by rewrite lh opprK !addr_ge0.
have AC : (1 + ln (n%:R / m%:R : RR) - ln (1 / 2 : RR) <= 2 + C0)%R.
  rewrite lh opprK -addrA.
  have -> : (2 + C0 = 1 + (C0 + 1) :> R)%R by ring.
  by rewrite lerD2l; apply: lerD.
have sd0 : (0 < Num.sqrt d%:R :> R)%R by rewrite sqrtr_gt0 ltr0n.
have psim : (Chw * K ^+ 2 / Num.sqrt d%:R * Num.sqrt m%:R <=
    Chw * K ^+ 2 * Num.sqrt d%:R :> R)%R.
  rewrite -mulrA ler_pM2l ?mulr_gt0 ?exprn_gt0 // ler_pdivrMl //.
  by rewrite -expr2 sqr_sqrtr ?ler0n.
have p0 : (0 <= Chw * K ^+ 2 / Num.sqrt d%:R * Num.sqrt m%:R :> R)%R.
  by rewrite mulr_ge0 ?sqrtr_ge0 // divr_ge0 ?sqrtr_ge0 // mulr_ge0
    ?exprn_ge0 // ltW.
rewrite /rip_T [2100 * 1]mulr1 -[2100 * _ * _]mulrA; apply/andP; split.
  apply: mulr_ge0; last exact: A0.
  exact: (mulr_ge0 (ler0n _ _) p0).
have -> : (2100 * Chw * K ^+ 2 * (2 + C0) * Num.sqrt d%:R =
    2100 * (Chw * K ^+ 2 * Num.sqrt d%:R) * (2 + C0) :> R)%R by ring.
apply: (ler_pM (mulr_ge0 (ler0n _ _) p0) A0 _ AC).
exact: (ler_wpM2l (ler0n _ _) psim).
Qed.

(* The bound of the restricted isometry theorem in terms of T <= T0 sqrt d
   and maxnorm <= sqrt (5 d). *)
Lemma rip_bound_alg (T C T0 d : R) : (0 <= T)%R -> (0 <= T0)%R ->
  (T <= T0 * Num.sqrt d)%R -> (0 <= C)%R -> (C <= Num.sqrt (5 * d))%R ->
  (0 <= d)%R ->
  (256 * T ^+ 2 + 32 * T * C + 8 * (1 / 2) * C ^+ 2 + C ^+ 2 <=
   (256 * T0 ^+ 2 + 32 * Num.sqrt 5 * T0 + 25) * d)%R.
Proof.
move=> T0' T00 hT C0 hC d0.
have sq0 : (0 <= Num.sqrt d)%R := sqrtr_ge0 d.
have s5 : (Num.sqrt (5 * d) = Num.sqrt 5 * Num.sqrt d)%R.
  by rewrite sqrtrM // ler0n.
have dd : (Num.sqrt d ^+ 2 = d)%R by rewrite sqr_sqrtr.
have s50 : (0 <= Num.sqrt (5 : R))%R by rewrite sqrtr_ge0.
have hT2 : (T ^+ 2 <= T0 ^+ 2 * d)%R.
  rewrite -dd -exprMn; apply: lerXn2r => //; rewrite nnegrE //.
  by apply: mulr_ge0.
have hC2 : (C ^+ 2 <= 5 * d)%R.
  have h5d : (0 <= 5 * d)%R by rewrite mulr_ge0 // ler0n.
  rewrite -[X in (_ <= X)%R](@sqr_sqrtr _ (5 * d)) //.
  by apply: lerXn2r => //; rewrite nnegrE // sqrtr_ge0.
have hTC : (T * C <= T0 * Num.sqrt 5 * d)%R.
  apply: le_trans (ler_pM T0' C0 hT hC) _; rewrite s5.
  by rewrite mulrACA -expr2 dd.
lra.
Qed.

(* The constant of the bound on the operator norm of L_X^*. *)
Definition adj_const (K Chw C0 : R) : R :=
  let T0 := (2100 * Chw * K ^+ 2 * (2 + C0))%R in
  (Num.sqrt (256 * T0 ^+ 2 + 32 * Num.sqrt 5 * T0 + 25) *
   Num.sqrt (C0 + 2))%R.

Section adjoint_bound_flat.
Local Open Scope ereal_scope.
Variables (K Chw C0 : R) (n d : nat).
Variable lam : nat -> probability (measurableTypeR R) R.
Hypothesis hlam : forall k, (k < n * d)%N -> mixture_component_law K (lam k).
Hypotheses (Chw0 : (0 < Chw)%R) (C01 : (1 <= C0)%R).
(* The linear forms of the feature of each point are subexponential with
   constant Chw K^2 / sqrt d and centered. *)
Hypothesis hw : forall i (y : 'rV[R]_(d * d)), (i < n)%N -> mxdot y y = 1%R ->
  subexponential (data_feature_law (flat_row lam d i) d) (fun z => mxdot z y)
    (Chw * K ^+ 2 / Num.sqrt d%:R)%R.
Hypothesis cen : forall i (y : 'rV[R]_(d * d)), (i < n)%N -> mxdot y y = 1%R ->
  (\int[data_feature_law (flat_row lam d i) d]_v mxdot v y = 0)%R.
Hypotheses (d0 : (0 < d)%N) (n0 : (0 < n)%N).
Hypothesis nd : (n%:R <= C0 * d%:R ^+ 2)%R.

Theorem adjoint_bound_flat :
  exists G : set (paper_main_sample n d), [/\ measurable G,
    tuple_prod lam (n * d) (~` G) <=
      (2 * (trunc_log 4 (minn n (d * d))).+2%:R *
         expR (- Num.sqrt (minn n (d * d))%:R) +
       n%:R * (2 * expR (- Num.min (d%:R / (576 * K ^+ 4))
                                   (d%:R / (12 * K ^+ 2)))))%:E &
    forall x, G x -> norm_good n d 1 x /\
      forall z : 'rV[R]_n,
      (frobenius (sample_adj x z) <=
       adj_const K Chw C0 * Num.sqrt d%:R * frobenius z)%R].
Proof.
have K0 : (0 < K)%R.
  by apply: (component_law_K _ (lam 0)); apply: hlam; rewrite muln_gt0 n0 d0.
set m := minn n (d * d).
have m0 : (0 < m)%N by rewrite leq_min n0 muln_gt0 d0.
have mn : (m <= n)%N by exact: geq_minl.
have sd0 : (0 < Num.sqrt d%:R :> R)%R by rewrite sqrtr_gt0 ltr0n.
set psi := (Chw * K ^+ 2 / Num.sqrt d%:R)%R.
have psi0 : (0 < psi)%R by rewrite /psi !mulr_gt0 ?invr_gt0 ?exprn_gt0.
pose mu i := data_feature_law (flat_row lam d i) d.
have sub i (y : 'rV[R]_(d * d)) : (i < n)%N -> mxdot y y = 1%R ->
    subexponential (mu i) (fun v => mxdot v y) psi.
  exact: hw.
have cen' i (y : 'rV[R]_(d * d)) : (i < n)%N -> mxdot y y = 1%R ->
    (\int[mu i]_v mxdot v y = 0)%R.
  exact: cen.
have b0 : (0 < 1 / 2 :> R)%R by lra.
have b1 : (1 / 2 <= 1 / 2 :> R)%R by lra.
(* the restricted isometry theorem for the features of the sample *)
have [Gf [mGf PGf hGf]] := @restricted_isometry RR n (d * d) m
  mu psi psi0 sub cen' (1 / 2) 1 m0 mn b0 b1 (lexx _).
have mF : measurable (unsat_features n d @^-1` Gf).
  rewrite -[X in measurable X]setTI.
  exact: (measurable_unsat_features n d) measurableT Gf mGf.
have mN := measurable_norm_good n d 1.
exists (unsat_features n d @^-1` Gf `&` norm_good n d 1); split.
- exact: measurableI.
- rewrite setCI; apply: le_trans (measureU2 _ _ _) _.
  + exact: measurableC.
  + exact: measurableC.
  rewrite EFinD; apply: leeD.
    have e := flat_features_law lam n d (~` Gf) (measurableC mGf).
    apply: (@le_trans _ _ (tuple_prod mu n (~` Gf))).
      rewrite preimage_setC.
      exact: (eq_ind_r (fun v => (v <= _)%E) (lexx _) e).
    apply: le_trans PGf _; rewrite lee_fin ler_pM2l ?mulr_gt0 ?ltr0n //.
    rewrite ler_expR lerN2 mul1r -[X in (X <= _)%R]mulr1.
    rewrite ler_wpM2l ?sqrtr_ge0 // lerDl ln_ge0 //.
    by rewrite ler_pdivlMr ?ltr0n // mul1r ler_nat.
  apply: le_trans (norm_good_prob_flat K n d lam hlam _ ler01) _.
  by rewrite expr1n !mul1r.
- move=> x [/= hGx hNx]; split => // z.
  set X := unsat_features n d x.
  have hC : (maxnorm X <= Num.sqrt (5 * d%:R))%R.
    rewrite /maxnorm; apply: bigmax_le; first exact: sqrtr_ge0.
    move=> i _; rewrite /frobenius ler_sqrt ?mulr_ge0 ?ler0n //.
    exact: sqnorm_feature_le.
  have md : (Num.sqrt m%:R <= d%:R :> R)%R.
    apply: (@le_trans _ _ (Num.sqrt ((d%:R : R) ^+ 2))).
      rewrite ler_sqrt ?exprn_ge0 ?ler0n // -natrX ler_nat expnS expn1.
      exact: geq_minr.
    by rewrite sqrtr_sqr ger0_norm.
  have nmC : (n%:R / m%:R <= C0)%R.
    rewrite /m /minn; case: ltnP => _.
      by rewrite divff ?pnatr_eq0 -?lt0n.
    by rewrite ler_pdivrMr ?ltr0n ?muln_gt0 ?d0 // natrM -expr2.
  have /andP [T0' hT] :=
    rip_T_feature_le _ _ _ _ _ _ Chw0 K0 C01 d0 m0 mn md nmC.
  have T00 : (0 <= 2100 * Chw * K ^+ 2 * (2 + C0))%R.
    apply: mulr_ge0; last first.
      by apply: addr_ge0; [exact: ler0n|exact: le_trans ler01 C01].
    apply: mulr_ge0; last exact: exprn_ge0 (ltW K0).
    exact: mulr_ge0 (ler0n _ _) (ltW Chw0).
  have hA :=
    rip_bound_alg _ _ _ _ T0' T00 hT (maxnorm_ge0 X) hC (ler0n _ d).
  set A0 := (256 * _ ^+ 2 + 32 * Num.sqrt 5 * _ + 25)%R in hA.
  have hRC : (rip_const m X + maxnorm X ^+ 2 <= A0 * d%:R)%R.
    by apply: le_trans hA; apply: lerD => //; exact: hGf X hGx.
  (* the m-sparse vectors, then all vectors by blocks *)
  have hsp (u : 'rV[R]_n) : (#|supp u| <= m)%N ->
      (frobenius (u *m tuple_mx X) <= Num.sqrt (A0 * d%:R) * frobenius u)%R.
    move=> um; apply: le_trans (tuple_mx_rip X um) _.
    by rewrite ler_wpM2r ?frobenius_ge0 // ler_wsqrtr.
  have hb := tuple_mx_blocks m0 (sqrtr_ge0 _) hsp z.
  rewrite frobenius_sample_adj; apply: le_trans hb _.
  have A00 : (0 <= A0)%R.
    apply: addr_ge0; last exact: ler0n.
    apply: addr_ge0; first exact: mulr_ge0 (ler0n _ _) (exprn_ge0 _ T00).
    exact: mulr_ge0 (mulr_ge0 (ler0n _ _) (sqrtr_ge0 _)) T00.
  have q : ((n %/ m).+1%:R <= C0 + 2 :> R)%R.
    have q1 : ((n %/ m)%:R <= C0)%R.
      apply: le_trans nmC; rewrite ler_pdivlMr ?ltr0n // -natrM ler_nat.
      exact: leq_divM.
    rewrite -addn1 natrD; apply: (le_trans (lerD q1 (lexx (1 : R)))).
    by rewrite lerD2l ler1n.
  have e : (Num.sqrt (A0 * d%:R) * Num.sqrt (n %/ m).+1%:R =
      Num.sqrt A0 * Num.sqrt (n %/ m).+1%:R * Num.sqrt d%:R)%R.
    by rewrite sqrtrM // mulrAC.
  rewrite e; apply: ler_wpM2r; first exact: frobenius_ge0.
  apply: ler_wpM2r; first exact: sqrtr_ge0.
  rewrite /adj_const /=; apply: ler_wpM2l; first exact: sqrtr_ge0.
  exact: ler_wsqrtr q.
Qed.

End adjoint_bound_flat.

Section adjoint_bound.
Local Open Scope ereal_scope.
Variables (kappa K Chw C0 : R) (n d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu :
  forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j).
Hypotheses (Chw0 : (0 < Chw)%R) (C01 : (1 <= C0)%R).
(* The linear forms of one feature are subexponential with constant
   Chw K^2 / sqrt d: the Hanson-Wright inequality, which data_feature_hw
   below proves with Chw = 252. *)
Hypothesis hw : forall y : 'rV[R]_(d * d), mxdot y y = 1%R ->
  subexponential (data_feature_law nu d) (fun z => mxdot z y)
    (Chw * K ^+ 2 / Num.sqrt d%:R)%R.
Hypotheses (d0 : (0 < d)%N) (n0 : (0 < n)%N).
Hypothesis nd : (n%:R <= C0 * d%:R ^+ 2)%R.

Theorem adjoint_bound :
  exists G : set (paper_main_sample n d), [/\ measurable G,
    universality_sample_law nu n d (~` G) <=
      (2 * (trunc_log 4 (minn n (d * d))).+2%:R *
         expR (- Num.sqrt (minn n (d * d))%:R) +
       n%:R * (2 * expR (- Num.min (d%:R / (576 * K ^+ 4))
                                   (d%:R / (12 * K ^+ 2)))))%:E &
    forall x, G x -> norm_good n d 1 x /\
      forall z : 'rV[R]_n,
      (frobenius (sample_adj x z) <=
       adj_const K Chw C0 * Num.sqrt d%:R * frobenius z)%R].
Proof.
apply: (adjoint_bound_flat K Chw C0 n d _
  (sample_law_component kappa K n d nu hnu) Chw0 C01 _ _ d0 n0 nd).
- by move=> i y _ y1; rewrite flat_row_mod_feature; exact: hw.
- move=> i y _ _; rewrite flat_row_mod_feature.
  by have := data_feature_mean _ _ _ _ hnu y; rewrite /Rintegral unlock => ->.
Qed.

End adjoint_bound.

(* The hypothesis hw holds with Chw = 252: the Hanson-Wright inequality of
   lane A for the quadratic forms of the features
   (data_feature_subexponential of Features/Regular). *)
Lemma data_feature_hw (kappa K : R) (d : nat)
    (nu : nat -> probability (measurableTypeR R) R) :
  (forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j)) ->
  (0 < d)%N -> forall y : 'rV[R]_(d * d), mxdot y y = 1%R ->
  subexponential (data_feature_law nu d) (fun z => mxdot z y)
    (252 * K ^+ 2 / Num.sqrt d%:R)%R.
Proof.
move=> hnu d0 y y1.
have K0 : (0 < K)%R by have [] := hnu 0 d0.
have fy : frobenius (vec_mx y : 'M[R]_d) = 1%R.
  by rewrite /frobenius -mxdot_mxvec vec_mxK y1 sqrtr1.
have := data_feature_subexponential kappa K d nu hnu (vec_mx y)
  (252 * K ^+ 2)%R d0.
rewrite vec_mxK fy mulr1 lexx => h; apply: h => //.
by rewrite mulr_gt0 ?exprn_gt0 // ltr0n.
Qed.

(* adjoint_bound without the hypothesis hw. *)
Theorem adjoint_bound_data (kappa K C0 : R) (n d : nat)
    (nu : nat -> probability (measurableTypeR R) R) :
  (forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j)) ->
  (1 <= C0)%R -> (0 < d)%N -> (0 < n)%N -> (n%:R <= C0 * d%:R ^+ 2)%R ->
  exists G : set (paper_main_sample n d), [/\ measurable G,
    (universality_sample_law nu n d (~` G) <=
      (2 * (trunc_log 4 (minn n (d * d))).+2%:R *
         expR (- Num.sqrt (minn n (d * d))%:R) +
       n%:R * (2 * expR (- Num.min (d%:R / (576 * K ^+ 4))
                                   (d%:R / (12 * K ^+ 2)))))%:E)%E &
    forall x, G x -> norm_good n d 1 x /\
      forall z : 'rV[R]_n,
      (frobenius (sample_adj x z) <=
       adj_const K (252)%R C0 * Num.sqrt d%:R * frobenius z)%R].
Proof.
move=> hnu C01 d0 n0 nd.
have c0 : (0 < 252 :> R)%R by rewrite ltr0n.
exact: (adjoint_bound kappa K 252%R C0 n d nu hnu c0 C01
  (data_feature_hw kappa K d nu hnu d0) d0 n0 nd).
Qed.

(* The hypotheses on the features of adjoint_bound_flat for the sample law
   universality_sample_law nu n d, the flat family k |-> nu (k mod d), with
   coordinate laws. *)
Lemma sample_law_feature_hw (kappa K : R) (n d : nat)
    (nu : nat -> probability (measurableTypeR R) R) :
  (forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j)) ->
  (0 < d)%N -> forall i (y : 'rV[R]_(d * d)), (i < n)%N -> mxdot y y = 1%R ->
  subexponential (data_feature_law (flat_row (fun k => nu (k %% d)%N) d i) d)
    (fun z => mxdot z y) (252 * K ^+ 2 / Num.sqrt d%:R)%R.
Proof.
move=> hnu d0 i y _ y1; rewrite flat_row_mod_feature.
exact: (data_feature_hw _ _ _ _ hnu d0 y y1).
Qed.

Lemma sample_law_feature_mean (kappa K : R) (n d : nat)
    (nu : nat -> probability (measurableTypeR R) R) :
  (forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j)) ->
  forall i (y : 'rV[R]_(d * d)), (i < n)%N -> mxdot y y = 1%R ->
  (\int[data_feature_law (flat_row (fun k => nu (k %% d)%N) d i) d]_v
     mxdot v y = 0)%R.
Proof.
move=> hnu i y _ _; rewrite flat_row_mod_feature.
by have := data_feature_mean _ _ _ _ hnu y; rewrite /Rintegral unlock => ->.
Qed.

(* The hypotheses on the features of adjoint_bound_flat for flat families of
   component laws, with Chw = 252: component_feature_subexponential and
   component_feature_mean of Features/Regular. *)
Lemma flat_feature_hw (K : R) (n d : nat)
    (lam : nat -> probability (measurableTypeR R) R) :
  (forall k, (k < n * d)%N -> mixture_component_law K (lam k)) ->
  (0 < d)%N -> forall i (y : 'rV[R]_(d * d)), (i < n)%N -> mxdot y y = 1%R ->
  subexponential (data_feature_law (flat_row lam d i) d)
    (fun z => mxdot z y) (252 * K ^+ 2 / Num.sqrt d%:R)%R.
Proof.
move=> hlam d0 i y id y1.
have hrow j : (j < d)%N -> mixture_component_law K (flat_row lam d i j).
  exact: (flat_row_hyp _ _ _ _ hlam i j id).
have K0 : (0 < K)%R := component_law_K _ _ (hrow 0%N d0).
have fy : frobenius (vec_mx y : 'M[R]_d) = 1%R.
  by rewrite /frobenius -mxdot_mxvec vec_mxK y1 sqrtr1.
have := component_feature_subexponential K d _ hrow (vec_mx y)
  (252 * K ^+ 2)%R d0.
rewrite vec_mxK fy mulr1 lexx => h; apply: h => //.
by rewrite mulr_gt0 ?exprn_gt0 // ltr0n.
Qed.

Lemma flat_feature_mean (K : R) (n d : nat)
    (lam : nat -> probability (measurableTypeR R) R) :
  (forall k, (k < n * d)%N -> mixture_component_law K (lam k)) ->
  forall i (y : 'rV[R]_(d * d)), (i < n)%N -> mxdot y y = 1%R ->
  (\int[data_feature_law (flat_row lam d i) d]_v mxdot v y = 0)%R.
Proof.
move=> hlam i y id _.
have hrow j : (j < d)%N -> mixture_component_law K (flat_row lam d i j).
  exact: (flat_row_hyp _ _ _ _ hlam i j id).
by have := component_feature_mean _ _ _ hrow y; rewrite /Rintegral unlock => ->.
Qed.

(* 5. Consequences: the nuclear norm of L_X^* z and the norm of L_X. *)

Section adjoint_consequences.
Variables (n d : nat) (x : paper_main_sample n d) (C : R).
Hypothesis hC : forall z : 'rV[R]_n,
  (frobenius (sample_adj x z) <= C * Num.sqrt d%:R * frobenius z)%R.

(* Proposition 3.1 (iii): nuclear (L_X^* z) <= C d |z|. *)
Lemma nuclear_sample_adj_le (z : 'rV[R]_n) :
  (nuclear (sample_adj x z) <= C * d%:R * frobenius z)%R.
Proof.
apply: le_trans (nuclear_le_frobenius _) _.
apply: le_trans (ler_wpM2l (sqrtr_ge0 _) (hC z)) _.
have -> : (Num.sqrt d%:R * (C * Num.sqrt d%:R * frobenius z) =
    C * (Num.sqrt d%:R * Num.sqrt d%:R) * frobenius z :> R)%R by ring.
by rewrite -expr2 sqr_sqrtr ?ler0n.
Qed.

(* |L_X D| <= C sqrt d |D|_F, by duality. *)
Lemma frobenius_sample_map_le (D : 'M[R]_d) : (0 <= C)%R ->
  (frobenius (sample_map x D) <= C * Num.sqrt d%:R * frobenius D)%R.
Proof.
move=> C0; set y := sample_map x D.
have e : mxdot y y = mxdot (sample_adj x y) D.
  by rewrite /sample_adj -mxdot_coef_map.
have [y0|y0] := eqVneq (frobenius y) 0%R.
  by rewrite y0 mulr_ge0 ?frobenius_ge0 // mulr_ge0 ?sqrtr_ge0.
have yp : (0 < frobenius y)%R by rewrite lt_def y0 frobenius_ge0.
rewrite -(ler_pM2r yp) -expr2 frobenius_sqr e.
apply: le_trans (ler_norm _) _; apply: le_trans (mxdot_le _ _) _.
apply: le_trans (ler_wpM2r (frobenius_ge0 D) (hC y)) _.
by rewrite mulrAC.
Qed.

End adjoint_consequences.

(* 6. The failure probabilities tend to 0 when n / d^2 tends to alpha > 0. *)

Section adjoint_limit.

(* 2 (log_4 m + 2) exp (- sqrt m) <= 12 / sqrt m. *)
Lemma trunc_log_expR_le (m : nat) : (0 < m)%N ->
  (2 * (trunc_log 4 m).+2%:R * expR (- Num.sqrt m%:R) <=
   12 / Num.sqrt m%:R :> R)%R.
Proof.
move=> m0.
set k := trunc_log 4 m.
set s := Num.sqrt m%:R.
have s1 : (1 <= s :> R)%R.
  rewrite /s -[X in (X <= _)%R]sqrtr1 ler_sqrt //.
  by rewrite ler1n.
have s0 : (0 < s :> R)%R by apply: lt_le_trans s1; exact: ltr01.
have ss : (s ^+ 2 = m%:R :> R)%R by rewrite sqr_sqrtr // ler0n.
(* k^2 < 4^k <= m, so k <= sqrt m *)
have kk : (k * k < m)%N.
  have h4 := @trunc_logP 4 m isT m0.
  have h2 := @ltn_expl 2 k isT.
  apply: leq_trans h4; rewrite (_ : 4 = 2 * 2)%N // expnMn.
  exact: ltn_mul.
have ks : (k%:R <= s :> R)%R.
  rewrite -ler_sqr ?nnegrE ?ler0n ?(ltW s0) // ss -natrX ler_nat -mulnn.
  exact: ltnW.
(* exp (sqrt m) >= m / 2 *)
have es : (s ^+ 2 / 2 <= expR s :> R)%R.
  have h := expR_ge1Dxn 1 (ltW s0).
  rewrite (_ : 1.+1`! = 2)%N // in h.
  by apply: le_trans h; rewrite lerDr.
have em : (expR (- s) <= 2 / s ^+ 2 :> R)%R.
  rewrite expRN -[2 / s ^+ 2]invf_div lef_pV2 ?posrE ?divr_gt0 ?exprn_gt0 //.
  exact: expR_gt0.
have kR : (k.+2%:R = k%:R + 2 :> R)%R by rewrite -addn2 natrD.
apply: (@le_trans _ _ (2 * (s + 2) * (2 / s ^+ 2))).
  rewrite kR; apply: ler_pM.
  - by rewrite mulr_ge0 // addr_ge0 // ler0n.
  - exact: ltW (expR_gt0 _).
  - by rewrite ler_wpM2l // lerD2r.
  - exact: em.
have sn : s != 0 by rewrite gt_eqF.
rewrite -subr_ge0.
have -> : (12 / s - 2 * (s + 2) * (2 / s ^+ 2) = 8 * (s - 1) / s ^+ 2 :> R)%R.
  by field.
by rewrite divr_ge0 ?exprn_ge0 ?(ltW s0) // mulr_ge0 // subr_ge0.
Qed.

(* d^2 exp (- c d) <= 6 / (c^3 d). *)
Lemma sqr_expR_le (c : R) (d : nat) : (0 < c)%R -> (0 < d)%N ->
  (d%:R ^+ 2 * expR (- (c * d%:R)) <= 6 / (c ^+ 3 * d%:R) :> R)%R.
Proof.
move=> c0 d0.
have dR : (0 < d%:R :> R)%R by rewrite ltr0n.
set y := (c * d%:R)%R.
have y0 : (0 < y :> R)%R by rewrite mulr_gt0.
(* exp y >= y^3 / 6 *)
have h := expR_ge1Dxn 2 (ltW y0).
rewrite (_ : 2.+1`! = 6)%N // in h.
have ey : (y ^+ 3 / 6 <= expR y :> R)%R by apply: le_trans h; rewrite lerDr.
have em : (expR (- y) <= 6 / y ^+ 3 :> R)%R.
  rewrite expRN -[6 / y ^+ 3]invf_div lef_pV2 ?posrE ?divr_gt0 ?exprn_gt0 //.
  exact: expR_gt0.
apply: le_trans (ler_wpM2l _ em) _; first by rewrite exprn_ge0 // ler0n.
have cn : c != 0 by rewrite gt_eqF.
have dn : d%:R != 0 :> R by rewrite gt_eqF.
by rewrite /y le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

(* Proposition 3.1, second display, with probability tending to one, for
   flat families, given the hypotheses on the features of
   adjoint_bound_flat with Chw = 252: if n(d) / d^2 tends to alpha > 0,
   then for every eps > 0 there is D such that for every d >= D and every
   flat family of component laws with these hypotheses, outside a
   measurable event of probability at most eps, every point has
   | |x_i|^2 - d | < d and |L_X^* z|_F <= C sqrt d |z| for every z, with
   C = adj_const K 252 (alpha + 1). D does not depend on the laws. *)
Theorem adjoint_bound_limit_features (K alpha : R) (n : nat -> nat) :
  (0 < alpha)%R -> universality_density_tends_to n alpha ->
  forall eps : R, (0 < eps)%R -> exists D : nat, forall d, (D <= d)%N ->
  forall lam : nat -> probability (measurableTypeR R) R,
    (forall k, (k < n d * d)%N -> mixture_component_law K (lam k)) ->
    (forall i (y : 'rV[R]_(d * d)), (i < n d)%N -> mxdot y y = 1%R ->
       subexponential (data_feature_law (flat_row lam d i) d)
         (fun z => mxdot z y) (252 * K ^+ 2 / Num.sqrt d%:R)%R) ->
    (forall i (y : 'rV[R]_(d * d)), (i < n d)%N -> mxdot y y = 1%R ->
       (\int[data_feature_law (flat_row lam d i) d]_v mxdot v y = 0)%R) ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (tuple_prod lam (n d * d) E <= eps%:E)%E &
    forall x, ~ E x -> norm_good (n d) d 1 x /\
      forall z : 'rV[R]_(n d),
      (frobenius (sample_adj x z) <=
       adj_const K (252)%R (alpha + 1) * Num.sqrt d%:R * frobenius z)%R].
Proof.
move=> a0 hn eps e0.
set C0 := (alpha + 1)%R.
have C01 : (1 <= C0)%R by rewrite /C0 lerDr ltW.
set c := (Num.min (576 * K ^+ 4)^-1 (12 * K ^+ 2)^-1)%R.
set q := (Num.min (alpha / 2) 1)%R.
have q0 : (0 < q)%R by rewrite lt_min divr_gt0 // ltr01.
have [D1 h1] := hn _ q0.
pose D2 := (archimedean.Num.truncn ((24 / eps) ^+ 2 / q)).+1.
pose D3 := (archimedean.Num.truncn (24 * C0 / (c ^+ 3 * eps))).+1.
exists (maxn (maxn D1 D2) (maxn D3 1)) => d.
rewrite !geq_max => /andP[/andP[d1 d2] /andP[d3 dpos]] lam hlam hw cen.
have dR : (0 < d%:R :> R)%R by rewrite ltr0n.
have hd := h1 d d1; rewrite /paper_main_density RdivE in hd.
have d2R : (0 < d%:R ^+ 2 :> R)%R by rewrite exprn_gt0.
have qa : (q <= alpha / 2)%R by rewrite /q ge_min lexx.
have q1 : (q <= 1)%R by rewrite /q ge_min lexx orbT.
(* q d^2 <= n <= (alpha + 1) d^2 *)
move: hd; rewrite ltr_norml => /andP[hlo hhi].
have rlo : (q <= (n d)%:R / d%:R ^+ 2)%R by lra.
have rhi : ((n d)%:R / d%:R ^+ 2 <= C0)%R by rewrite /C0; lra.
have nlow : (q * d%:R ^+ 2 <= (n d)%:R)%R by rewrite -ler_pdivlMr.
have nup : ((n d)%:R <= C0 * d%:R ^+ 2)%R by rewrite -ler_pdivrMr.
have n0 : (0 < n d)%N.
  by rewrite -(ltr0n R); apply: lt_le_trans nlow; rewrite mulr_gt0.
have K0 : (0 < K)%R.
  by apply: (component_law_K _ (lam 0)); apply: hlam; rewrite muln_gt0 n0 dpos.
have c0 : (0 < c)%R by rewrite lt_min !invr_gt0 !mulr_gt0 ?exprn_gt0.
have c252 : (0 < 252 :> R)%R by rewrite ltr0n.
have [G [mG PG HG]] := adjoint_bound_flat K 252%R C0 (n d) d lam hlam c252
  C01 hw cen dpos n0 nup.
exists (~` G); split.
- exact: measurableC.
- apply: le_trans PG _; rewrite lee_fin.
  rewrite [eps]splitr; apply: lerD.
    (* the first term: m = min (n, d^2) >= q d^2 > (24 / eps)^2 *)
    set m := minn (n d) (d * d).
    have m0 : (0 < m)%N by rewrite leq_min n0 muln_gt0 dpos.
    have h12 : (2 * (trunc_log 4 m).+2%:R * expR (- Num.sqrt m%:R) <=
        12 / Num.sqrt m%:R)%R := trunc_log_expR_le m m0.
    apply: le_trans h12 _.
    have mR : (q * d%:R ^+ 2 <= m%:R)%R.
      rewrite /m /minn; case: ifP => _ //.
      by rewrite natrM -expr2 ler_piMl // ltW.
    have dd : (d%:R <= d%:R ^+ 2 :> R)%R.
      by rewrite expr2 ler_peMl ?ler0n // ler1n.
    have hX : ((24 / eps) ^+ 2 / q < d%:R)%R.
      apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
      by rewrite ler_nat.
    have mq : ((24 / eps) ^+ 2 <= m%:R)%R.
      apply: le_trans mR; apply: le_trans (ler_wpM2l (ltW q0) dd).
      by move: hX; rewrite ltr_pdivrMr // [d%:R * _]mulrC => /ltW.
    have e24 : (0 <= 24 / eps)%R by rewrite divr_ge0 // ltW.
    have sm : (24 / eps <= Num.sqrt m%:R)%R.
      by rewrite -(ger0_norm e24) -sqrtr_sqr ler_sqrt.
    have sm0 : (0 < Num.sqrt m%:R :> R)%R by rewrite sqrtr_gt0 ltr0n.
    rewrite ler_pdivrMr //.
    have e2' : (0 <= eps / 2 :> R)%R by rewrite divr_ge0 // ltW.
    apply: le_trans (ler_wpM2l e2' sm).
    have en : eps != 0 by rewrite gt_eqF.
    by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
  (* the second term: n 2 exp (- c d) <= 12 (alpha + 1) / (c^3 d) *)
  have mE : (Num.min (d%:R / (576 * K ^+ 4)) (d%:R / (12 * K ^+ 2)) =
      c * d%:R)%R.
    by rewrite /c -minr_pMr ?ler0n // mulrC.
  rewrite mE.
  have hs : (d%:R ^+ 2 * expR (- (c * d%:R)) <= 6 / (c ^+ 3 * d%:R))%R :=
    sqr_expR_le c d c0 dpos.
  apply: (@le_trans _ _ (C0 * d%:R ^+ 2 * (2 * expR (- (c * d%:R))))).
    by apply: ler_wpM2r => //; rewrite mulr_ge0 // ltW // expR_gt0.
  have -> : (C0 * d%:R ^+ 2 * (2 * expR (- (c * d%:R))) =
      2 * C0 * (d%:R ^+ 2 * expR (- (c * d%:R))))%R by ring.
  apply: le_trans (ler_wpM2l _ hs) _.
    by rewrite mulr_ge0 // (le_trans _ C01) // ler01.
  have hY : (24 * C0 / (c ^+ 3 * eps) < d%:R)%R.
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    by rewrite ler_nat.
  have cn : c != 0 by rewrite gt_eqF.
  have en : eps != 0 by rewrite gt_eqF.
  have dn : d%:R != 0 :> R by rewrite gt_eqF.
  have -> : (2 * C0 * (6 / (c ^+ 3 * d%:R)) =
      eps / 2 * (24 * C0 / (c ^+ 3 * eps) / d%:R))%R by field.
  rewrite -[X in (_ <= X)%R]mulr1 ler_wpM2l ?divr_ge0 ?ltW //.
  by rewrite ltr_pdivrMr // mul1r.
- by move=> x /contrapT Gx; exact: HG.
Qed.


(* The same for the sample law of coordinate laws: if n(d) / d^2 tends to
   alpha > 0, then for every eps > 0 and every large d, outside a
   measurable event of probability at most eps, every point has
   | |x_i|^2 - d | < d and |L_X^* z|_F <= C sqrt d |z| for every z, with
   C = adj_const K 252 (alpha + 1). *)
Theorem adjoint_bound_limit (kappa K alpha : R)
    (nu : nat -> nat -> probability (measurableTypeR R) R) (n : nat -> nat) :
  (forall d j, (j < d)%N -> universality_coordinate_law kappa K (nu d j)) ->
  (0 < alpha)%R -> universality_density_tends_to n alpha ->
  forall eps : R, (0 < eps)%R -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (universality_sample_law (nu d) (n d) d E <= eps%:E)%E &
    forall x, ~ E x -> norm_good (n d) d 1 x /\
      forall z : 'rV[R]_(n d),
      (frobenius (sample_adj x z) <=
       adj_const K (252)%R (alpha + 1) * Num.sqrt d%:R * frobenius z)%R].
Proof.
move=> hnu a0 hn eps e0.
have [D hD] := adjoint_bound_limit_features K alpha n a0 hn eps e0.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d0].
apply: (hD d dD _ (sample_law_component kappa K (n d) d (nu d) (hnu d))).
- exact: (sample_law_feature_hw _ _ _ _ _ (hnu d) d0).
- exact: (sample_law_feature_mean _ _ _ _ _ (hnu d)).
Qed.

(* Proposition 3.1, second display, with probability tending to one, for
   flat families of component laws: if n(d) / d^2 tends to alpha > 0, then
   for every eps > 0 there is D such that for every d >= D and every flat
   family of component laws with constant K, outside a measurable event of
   probability at most eps, every point has | |x_i|^2 - d | < d and
   |L_X^* z|_F <= C sqrt d |z| for every z, with
   C = adj_const K 252 (alpha + 1). *)
Theorem adjoint_bound_limit_flat (K alpha : R) (n : nat -> nat) :
  (0 < alpha)%R -> universality_density_tends_to n alpha ->
  forall eps : R, (0 < eps)%R -> exists D : nat, forall d, (D <= d)%N ->
  forall lam : nat -> probability (measurableTypeR R) R,
    (forall k, (k < n d * d)%N -> mixture_component_law K (lam k)) ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (tuple_prod lam (n d * d) E <= eps%:E)%E &
    forall x, ~ E x -> norm_good (n d) d 1 x /\
      forall z : 'rV[R]_(n d),
      (frobenius (sample_adj x z) <=
       adj_const K (252)%R (alpha + 1) * Num.sqrt d%:R * frobenius z)%R].
Proof.
move=> a0 hn eps e0.
have [D hD] := adjoint_bound_limit_features K alpha n a0 hn eps e0.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d0] lam hlam.
exact: (hD d dD lam hlam (flat_feature_hw K (n d) d lam hlam d0)
  (flat_feature_mean K (n d) d lam hlam)).
Qed.

End adjoint_limit.
