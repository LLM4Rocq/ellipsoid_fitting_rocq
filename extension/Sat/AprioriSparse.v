(* The first display of Proposition 3.1 of Koehler and Sohn (arXiv
   2608.27372, lines 2133-2275 of arxiv_v1.tex), at Stdlib's R: the sparse a
   priori estimates. Item S3 of stage 3 of phase 5 (lane C), after
   Sat/Apriori (the second display).

   For a sample x of n points x_i of R^d with coordinates of laws as
   universality_coordinate_law kappa K asks, an m-sparse u : 'rV_n (at most
   m nonzero coordinates, supp of library/random_matrix/restricted_isometry)
   and W_i = (x_i x_i^T - I) / sqrt d:
   - sample_comb x u = sum_i u_i x_i, so that |X_I| <= L for every I of
     size at most m is |sample_comb x u| <= L |u| for every m-sparse u;
   - Q_I = (<W_i, W_j> / d)_(i, j in I), so that |Q_I - I| <= delta for
     every I of size at most m is
     | |L_X^* u|_F^2 / d - |u|^2 | <= delta |u|^2 for every m-sparse u
     (L_X^* u = sample_adj x u = sum_i u_i W_i).

   Proved here.
   - point_law: the law of a point as a row vector; its linear forms
     <x, y>, |y| = 1, are centered and subgaussian with constant 4 K
     (point_lin_mean, point_lin_subgaussian, from subgaussian_lincomb of
     library/probability/subgaussian.v).
   - sparse_points_bound (the bound on X_I): for 0 < m <= n and s >= 0,
     outside a measurable event of probability at most 2 exp (- s), every
     m-sparse u satisfies
     |sum_i u_i x_i| <= 32 K sqrt (m (1 + ln (n / m)) + 6 (m + d) + s) |u|
     (sparse_norm_subgaussian of restricted_isometry.v). *)

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
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Sat Require Import Apriori.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. The law of a point. *)

Section point_law.
Local Open Scope ereal_scope.
Variables (kappa K : R) (d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu :
  forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j).

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
  have := coordinate_law_integrable kappa K (nu j) (hnu j (ltn_ord j)) 1.
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
  have := coordinate_law_integrable kappa K (nu j) hj 1.
  by apply: eq_integrable => // x _; rewrite expr1.
have hm : (\int[nu j]_x (x : R)%:E = 0)%E :=
  coordinate_law_mean kappa K (nu j) hj.
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
have K0 : (0 < K)%R := coordinate_law_K kappa K (nu 0) (hnu 0 d0).
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
  by move=> j jd; exact: coordinate_law_subgaussian kappa K (nu j) (hnu j jd).
have m0 : forall j, (j < d)%N -> (\int[nu j]_x x = 0)%R.
  move=> j jd; rewrite /Rintegral.
  by rewrite (coordinate_law_mean kappa K (nu j) (hnu j jd)).
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
move=> hnu d0 m0 mn s0.
have K0 : (0 < K)%R := coordinate_law_K kappa K (nu 0) (hnu 0 d0).
have K40 : (0 < 4 * K)%R by rewrite mulr_gt0.
pose pl := point_law d nu.
have sub i (y : 'rV[RR]_d) : (i < n)%N -> mxdot y y = 1%R ->
    subgaussian pl (fun v => mxdot v y : RR) (4 * K)%R.
  by move=> _ y1; exact: point_lin_subgaussian kappa K d nu hnu y y1.
have cen i (y : 'rV[RR]_d) : (i < n)%N -> mxdot y y = 1%R ->
    (\int[pl]_v (mxdot v y : RR) = 0)%R.
  by move=> _ _; rewrite /Rintegral (point_lin_mean kappa K d nu hnu y).
have [Gp [mGp PGp hGp]] := @sparse_norm_subgaussian RR n d (fun=> pl)
  (4 * K)%R K40 sub cen m s m0 mn s0.
(* the event on the samples, by the law of the rows *)
have mP : measurable_fun setT (@sample_points n d).
  apply: measurableT_comp; last exact: measurable_tuple_rows.
  by apply: measurable_tuple_map => i; exact: measurable_row_of_tuple.
have mG : measurable (sample_points @^-1` Gp).
  by rewrite -[X in measurable X]setTI; exact: mP.
exists (sample_points @^-1` Gp); split => //.
  rewrite preimage_setC.
  have e := sample_map_law nu n d _ _ pl (row_of_tuple d) (~` Gp)
    (measurable_row_of_tuple d) (fun B mB => erefl) (measurableC mGp).
  apply: le_trans PGp.
  exact: (eq_ind_r (fun v => (v <= _)%E) (lexx _) e).
move=> x Gx u um; rewrite -frobenius_trmx sample_combE.
apply: le_trans (hGp _ Gx u um) _.
have e84 : (8 * 4 = 32 :> R)%R by rewrite -natrM.
by rewrite /sparse_norm_bound mulrA e84.
Qed.
