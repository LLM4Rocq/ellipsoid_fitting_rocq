From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral numfun.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean opnorm.
From GaussianAnalysis.probability Require Import lindeberg subgaussian subgaussian_matrix.
From GaussianAnalysis.comparison Require Import gauss_linear.
From GaussianAnalysis.convex Require Import gauss_feature.
From GaussianAnalysis.random_matrix Require Import restricted_isometry isotropic_rows.

(**md**************************************************************************)
(* # Gaussian row matrices                                                  *)
(*                                                                           *)
(* Gaussian directional subgaussianity with constant 2 and the independent  *)
(* isotropic-row covariance bound give                                      *)
(* E ||H||op^2 <= k + 1152 (sqrt(k(d+1)) + d+1).                            *)
(* A positive-threshold Markov bound follows. These are finite-sample bounds *)
(* over any realType; both zero row count and zero column dimension are     *)
(* allowed. The constants are explicit and deliberately not optimized.      *)
(* Source: the full-sample comparison in doc/shifted-gaussian.tex.            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section gaussian_direction.
Context {R : realType} {d : nat}.

Lemma gauss_direction_subgaussian (y : 'rV[R]_d) : frobenius y <= 1 ->
  subgaussian (gauss d) (fun x => mxdot x y) 2.
Proof.
move=> y1.
have s0 : (0 <= (2 : R)^-1) by rewrite invr_ge0.
have s2 : Num.sqrt ((2 : R)^-1) ^+ 2 = (2 : R)^-1.
  exact: sqr_sqrtr.
apply: (@subgaussian_of_mgf _ _ _ _ _ (Num.sqrt ((2 : R)^-1))).
- exact: measurable_mxdot.
- by [].
- by rewrite s2; nra.
- move=> l; rewrite integral_gauss_expR_mxdot lee_fin ler_expR s2.
  have fy0 := frobenius_ge0 y.
  have fy2 : frobenius y ^+ 2 <= 1 by nra.
  by have := sqr_ge0 l; nra.
Qed.

Lemma gauss_direction_mean (y : 'rV[R]_d) :
  \int[gauss d]_x mxdot x y = 0.
Proof. by have [h _ _] := gauss_mxdot_moments y y. Qed.

Lemma gauss_direction_second (y : 'rV[R]_d) :
  \int[gauss d]_x mxdot x y ^+ 2 = frobenius y ^+ 2.
Proof.
have [_ h _] := gauss_mxdot_moments y y.
under eq_Rintegral do rewrite expr2.
by rewrite h frobenius_sqr.
Qed.

End gaussian_direction.

Section gaussian_rows.
Context {R : realType} (k d : nat).
Local Notation P := (tuple_prod (fun=> @gauss R d) k).

Definition gaussian_rows_bound : R := k%:R + isotropic_covariance_bound k d 2.

Lemma opnorm_square_gram_deviation (H : 'M[R]_(k,d)) :
  opnorm H ^+ 2 <= k%:R + opnorm (H^T *m H - k%:R *: 1%:M).
Proof.
apply: le_trans (opnorm_sqr_le H) _.
have E : H^T *m H = (H^T *m H - k%:R *: 1%:M) + k%:R *: 1%:M.
  by rewrite subrK.
rewrite {1}E; apply: le_trans (opnormD _ _) _.
have I1 : opnorm (1%:M : 'M[R]_d) <= 1.
  by apply: opnorm_le => x x1; rewrite mul1mx.
have k0 : 0 <= k%:R :> R by rewrite ler0n.
rewrite opnormZ (ger0_norm k0).
have := ler_wpM2l k0 I1.
by rewrite mulr1; lra.
Qed.

Lemma measurable_gaussian_rows_opnorm_square :
  measurable_fun setT (fun x : k.-tuple 'rV[R]_d => opnorm (tuple_mx x) ^+ 2).
Proof.
apply: measurable_funX; apply: measurable_opnorm => i j.
by apply: measurableT_comp (measurable_mxentry i j) measurable_rows_matrix.
Qed.

Theorem gaussian_rows_opnorm_majorant :
  exists M : k.-tuple 'rV[R]_d -> R,
  [/\ measurable_fun setT M,
    (forall x, opnorm (tuple_mx x) ^+ 2 <= M x) &
    (\int[P]_x (M x)%:E <= gaussian_rows_bound%:E)%E].
Proof.
have sub i (y : 'rV[R]_d) : (i < k)%N -> frobenius y <= 1 ->
    subgaussian (gauss d) (fun x => mxdot x y) 2.
  by move=> _; exact: gauss_direction_subgaussian.
have iso i (y : 'rV[R]_d) : (i < k)%N -> frobenius y <= 1 ->
    \int[gauss d]_x mxdot x y ^+ 2 = frobenius y ^+ 2.
  by move=> _ _; exact: gauss_direction_second.
have K0 : (0 < 2 :> R) by [].
have [N [mN bN eN]] := isotropic_covariance_majorant K0 sub iso.
have N0 x : 0 <= N x := le_trans (opnorm_ge0 _) (bN x).
exists (fun x => k%:R + N x); split.
- exact: measurable_funD.
- move=> x; apply: le_trans (opnorm_square_gram_deviation _) _; by rewrite lerD2l.
- under eq_integral do rewrite EFinD.
  rewrite ge0_integralD //.
  - by move=> x _; rewrite lee_fin.
  - exact/measurable_EFinP.
  - rewrite integral_cst //= probability_setT mule1 /gaussian_rows_bound EFinD.
    exact: leeD (lexx _) eN.
Qed.

Theorem gaussian_rows_opnorm_second_moment :
  (\int[P]_x (opnorm (tuple_mx x) ^+ 2)%:E <= gaussian_rows_bound%:E)%E.
Proof.
have [M [mM bM eM]] := gaussian_rows_opnorm_majorant.
apply: le_trans _ eM; apply: ge0_le_integral => //.
- by move=> x _; rewrite lee_fin sqr_ge0.
- apply/measurable_EFinP; exact: measurable_gaussian_rows_opnorm_square.
- exact/measurable_EFinP.
- by move=> x _; rewrite lee_fin.
Qed.

Theorem gaussian_rows_opnorm_integrable :
  P.-integrable setT (fun x => (opnorm (tuple_mx x) ^+ 2)%:E).
Proof.
apply/integrableP; split.
- apply/measurable_EFinP; exact: measurable_gaussian_rows_opnorm_square.
- under eq_integral do rewrite gee0_abs ?lee_fin ?sqr_ge0 //.
  exact: le_lt_trans gaussian_rows_opnorm_second_moment (ltry _).
Qed.

Theorem gaussian_rows_opnorm_tail (t : R) : 0 < t ->
  (P [set x | (t <= opnorm (tuple_mx x) ^+ 2)%R] <= (gaussian_rows_bound / t)%:E)%E.
Proof.
move=> t0.
have h := probability_markov_ge P t0 measurable_gaussian_rows_opnorm_square
  (fun x => sqr_ge0 (opnorm (tuple_mx x))).
apply: le_trans h _.
rewrite mulrC EFinM; apply: lee_wpmul2l; first by rewrite lee_fin invr_ge0 ltW.
exact: gaussian_rows_opnorm_second_moment.
Qed.

(* A nonzero one-dimensional direction has exact second moment 1. *)
Example gaussian_one_entry_second_moment :
  \int[@gauss R 1]_x mxdot x (1%:M : 'rV[R]_1) ^+ 2 = 1.
Proof.
rewrite gauss_direction_second frobenius_sqr.
by rewrite /mxdot !big_ord1 !mxE eqxx mulr1.
Qed.

End gaussian_rows.
