From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets functions interval reals ereal.
From mathcomp Require Import topology normedtype sequences derive exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral numfun.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral nets.
From GaussianAnalysis.matrix Require Import lambda_max.
From GaussianAnalysis.comparison Require Import gauss_smoothing.
From GaussianAnalysis.comparison Require Import gauss_concentration.
From GaussianAnalysis.comparison Require Import slepian gordon escape.
From GaussianAnalysis.random_matrix Require Import goe.

(**md**************************************************************************)
(* # The upper edge of the Gaussian orthogonal ensemble                       *)
(*                                                                            *)
(* Let a have law gauss (d * d) with d >= 1, and let W = goe_mx a be the GOE  *)
(* matrix of random_matrix/goe.v: its entries W_ij, i <= j, are independent   *)
(* and centered, of variance 1 / d off the diagonal and 2 / d on it. Its      *)
(* largest eigenvalue lambda_max W (matrix/lambda_max.v) has mean at most 2   *)
(* (goe_lambda_max_mean), the right edge of the semicircle law (wigner.v).    *)
(* For every t >= 0, P(lambda_max W >= 2 + t) <= exp (- d t^2 / 4)            *)
(* (goe_lambda_max_tail), and the same holds for - W (goe_lambda_maxN_tail),  *)
(* so P(opnorm W >= 2 + t) <= 2 exp (- d t^2 / 4) (goe_opnorm_edge_tail). The *)
(* file does not bound E opnorm W by 2: goe.v bounds it by 2 sqrt 2.          *)
(*                                                                            *)
(* The proof compares Gaussian processes. For a unit column x, x^T W x = sqrt *)
(* (2 / d) <a, mxvec (x x^T)> (goe_mx_form), a linear function of a. For a    *)
(* finite family x_0, ..., x_k of unit columns, the process x_j^T W x_j is    *)
(* the row a *m goe_form_mx xs. Its increments have variance (4 / d) (1 -     *)
(* <x_j, x_l>^2) <= (8 / d) (1 - <x_j, x_l>) (goe_form_incr_var), the         *)
(* increment variance of (2 / sqrt d) <g, x_j> for g of law gauss d, diagonal *)
(* entries included. The Sudakov-Fernique inequality (sudakov_fernique) and E *)
(* |g| <= sqrt d (gauss_frobenius_mean) give E max_j x_j^T W x_j <= 2         *)
(* (goe_form_max_mean). On an eps-net of the unit sphere, lambda_max A <=     *)
(* max_j x_j^T A x_j + 2 eps opnorm A (lambda_max_net_le), and E opnorm W <=  *)
(* 2 sqrt 2 (goe_opnorm_mean), so letting eps tend to 0 bounds the mean. The  *)
(* map a |-> lambda_max W is sqrt (2 / d)-Lipschitz                           *)
(* (goe_lambda_max_lipschitz, from frobenius_goe_mx), hence measurable and    *)
(* integrable, and Gaussian concentration with the sharp constant             *)
(* (gauss_concentration_upper_tail) gives the tails. The matrix - W is goe_mx *)
(* (- a) (goe_mxN), and gauss (d * d) is invariant under a |-> - a            *)
(* (integral_gauss_opp).                                                      *)
(*                                                                            *)
(* This file is a Rocq formalization of the credited argument of 'Cutoff      *)
(* throughout the high-temperature Sherrington-Kirkpatrick phase' (family 227 *)
(* of the OpenAI math collection, revision 1581d4cbd): the lemma 'Gaussian    *)
(* concentration and comparison' and the first paragraph of the proof of the  *)
(* proposition 'Good disorder', in the appendix 'Uniform spectral and entropy *)
(* estimates' (appendices/entropy.tex). The Lean modules that follow the same *)
(* argument, in lean/OAI/Probability/SKRatio of the collection:               *)
(* Lean: goe_expected_top (Matrices/DiagonalTMemLp.lean, line 93)             *)
(* Lean: goe_norm_tail (Matrices/GoeMatrixQuadCoeff.lean, line 115)           *)
(*                                                                            *)
(* The manuscript, the Lean modules and this file differ in three ways. The   *)
(* manuscript takes beta W with beta < 1/2; here beta = 1. It compares the    *)
(* suprema over the unit sphere as continuous processes on a compact set;     *)
(* here the comparison is on finite families, and a net passes to the sphere. *)
(* Its concentration inequality, from the argument of Maurey and Pisier,      *)
(* bounds the moment generating function of F - E F by exp (pi^2 D^2 s^2 / 8) *)
(* for F D-Lipschitz, which gives exp (- d t^2 / pi^2) for the upper tail of  *)
(* lambda_max W; the Lean modules use the same inequality and bound P(opnorm  *)
(* W > 2 + t) by 2 exp (- d t^2 / pi^2). Here the sharp constant of           *)
(* gauss_concentration gives exp (- d t^2 / 4) and 2 exp (- d t^2 / 4), for   *)
(* the non-strict inequalities.                                               *)
(*                                                                            *)
(* ```                                                                        *)
(*   goe_form_mx xs == the matrix of the process x_j^T W x_j, W = goe_mx a:   *)
(*                     (a *m goe_form_mx xs) 0 j = x_j^T W x_j                *)
(*    goe_lin_mx xs == (2 / sqrt d) times the matrix whose columns are the    *)
(*                     x_j, the matrix of the process (2 / sqrt d) <g, x_j>   *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section goe_form.
Context {R : realType}.

Lemma mxdot_vec_mxl m n (a : 'rV[R]_(m * n)) (M : 'M[R]_(m, n)) :
  mxdot (vec_mx a) M = mxdot a (mxvec M).
Proof.
rewrite /mxdot [in RHS]big_ord1 sum_mxvec_index.
by apply: eq_bigr => i _; apply: eq_bigr => j _; rewrite mxvecE mxE.
Qed.

Lemma mxdot_mxvec_mxvec m n (A B : 'M[R]_(m, n)) :
  mxdot (mxvec A) (mxvec B) = mxdot A B.
Proof. by rewrite -mxdot_vec_mxl mxvecK. Qed.

(* The quadratic form of the GOE matrix at x is a linear function of a. *)
Lemma goe_mx_form d (a : 'rV[R]_(d * d)) (x : 'cV[R]_d) :
  mxdot x (goe_mx a *m x) = Num.sqrt (2 / d%:R) * mxdot a (mxvec (x *m x^T)).
Proof.
have e (V : 'M[R]_d) : mxdot x (V *m x) = mxdot V (x *m x^T).
  by rewrite mxdot_outer mxdot_colE mulmxA.
rewrite /goe_mx -scalemxAl mxdotZr mulmxDl mxdotDr !e.
have -> : mxdot (vec_mx a)^T (x *m x^T) = mxdot (vec_mx a) (x *m x^T).
  by rewrite -mxdot_trmx trmxK trmx_mul trmxK.
rewrite mxdot_vec_mxl -two_div_sqrt; ring.
Qed.

Lemma goe_mxN d (a : 'rV[R]_(d * d)) : goe_mx (- a) = - goe_mx a.
Proof. by rewrite -scaleN1r goe_mxZ scaleN1r. Qed.

End goe_form.

Section goe_form_process.
Context {R : realType} (d : nat).
Local Notation gauss := (@gauss R).

Definition goe_form_mx k (xs : 'I_k -> 'cV[R]_d) : 'M[R]_(d * d, k) :=
  \matrix_(p, j) (Num.sqrt (2 / d%:R) * mxvec (xs j *m (xs j)^T) 0 p).

Lemma goe_form_mxE k (xs : 'I_k -> 'cV[R]_d) (a : 'rV[R]_(d * d)) j :
  (a *m goe_form_mx xs) 0 j = mxdot (xs j) (goe_mx a *m xs j).
Proof.
rewrite goe_mx_form [LHS]mxE /mxdot big_ord1 mulr_sumr.
by apply: eq_bigr => p _; rewrite mxE mulrCA.
Qed.

Lemma goe_form_cov k (xs : 'I_k -> 'cV[R]_d) j l :
  ((goe_form_mx xs)^T *m goe_form_mx xs) j l =
  2 / d%:R * mxdot (xs j) (xs l) ^+ 2.
Proof.
rewrite mxE.
transitivity (2 / d%:R *
    mxdot (mxvec (xs j *m (xs j)^T)) (mxvec (xs l *m (xs l)^T))).
  rewrite /mxdot big_ord1 mulr_sumr; apply: eq_bigr => p _.
  by rewrite !mxE mulrACA -expr2 sqr_sqrtr // divr_ge0 // ler0n.
by rewrite mxdot_mxvec_mxvec mxdot_outer2 expr2.
Qed.

Definition goe_lin_mx k (xs : 'I_k -> 'cV[R]_d) : 'M[R]_(d, k) :=
  (2 / Num.sqrt d%:R) *: fam_mx xs.

Lemma goe_lin_cov k (xs : 'I_k -> 'cV[R]_d) j l :
  ((goe_lin_mx xs)^T *m goe_lin_mx xs) j l = 4 / d%:R * mxdot (xs j) (xs l).
Proof.
rewrite mxE.
transitivity (2 / Num.sqrt d%:R * (2 / Num.sqrt d%:R) * mxdot (xs j) (xs l)).
  rewrite /mxdot mulr_sumr; apply: eq_bigr => i _.
  by rewrite big_ord1 /goe_lin_mx !mxE mulrACA.
congr (_ * _); rewrite -expr2 expr_div_n sqr_sqrtr ?ler0n //.
by congr (_ / _); rewrite -[4]/(2 * 2)%:R natrM.
Qed.

(* For unit x_j, the increments of x_j^T W x_j have smaller variances than
   those of (2 / sqrt d) <g, x_j>: (4 / d) (1 - r^2) <= (8 / d) (1 - r). *)
Lemma goe_form_incr_var k (xs : 'I_k -> 'cV[R]_d) j l :
  (forall j, mxdot (xs j) (xs j) = 1) ->
  incr_var (goe_form_mx xs) j l <= incr_var (goe_lin_mx xs) j l.
Proof.
move=> x1; rewrite /incr_var !goe_form_cov !goe_lin_cov !x1.
set r := mxdot (xs j) (xs l).
have t0 : 0 <= d%:R^-1 :> R by rewrite invr_ge0 ler0n.
have := mulr_ge0 t0 (sqr_ge0 (1 - r)).
set t := d%:R^-1; rewrite /GRing.exp /=; nra.
Qed.

(* The largest of the x_j^T W x_j over a finite family of unit columns has
   mean at most 2. *)
Lemma goe_form_max_mean k (xs : 'I_k.+1 -> 'cV[R]_d) : (0 < d)%N ->
  (forall j, frobenius (xs j) = 1) ->
  \int[gauss (d * d)]_a rmax (a *m goe_form_mx xs) <= 2.
Proof.
move=> d0 x1.
have x1' j : mxdot (xs j) (xs j) = 1 by rewrite -frobenius_sqr x1 expr1n.
have hSF := sudakov_fernique (fun j l => goe_form_incr_var j l x1').
have iA := integrable_gauss_rmax (goe_form_mx xs).
have iB := integrable_gauss_rmax (goe_lin_mx xs).
have h1 : \int[gauss (d * d)]_a rmax (a *m goe_form_mx xs) <=
    \int[gauss d]_g rmax (g *m goe_lin_mx xs).
  by apply: fine_le; [exact: integrable_fin_num|exact: integrable_fin_num|].
apply: (le_trans h1).
set c : R := 2 / Num.sqrt d%:R.
have c0 : 0 <= c by rewrite divr_ge0 ?sqrtr_ge0.
have iF := @gauss_smoothing.integrable_gauss_frobenius R d.
have iF' : (gauss d).-integrable [set: 'rV[R]_d]
    (EFin \o (fun g => c * frobenius g)).
  rewrite (_ : _ \o _ = (fun g => c%:E * (frobenius g)%:E)%E).
    by apply/funext => g.
  exact: integrableZl.
apply: le_trans (_ : \int[gauss d]_g (c * frobenius g) <= _).
  apply: le_Rintegral => // g _; apply: rmax_le => j.
  rewrite /goe_lin_mx -scalemxAr mxE fam_mxE ler_wpM2l //.
  by rewrite (le_trans (ler_mxdot _ _)) // frobenius_trmx x1 mulr1.
rewrite RintegralZl //.
have s0 : 0 < Num.sqrt d%:R :> R by rewrite sqrtr_gt0 ltr0n.
apply: le_trans (ler_wpM2l c0 (gauss_frobenius_mean d)) _.
by rewrite /c divfK ?gt_eqF.
Qed.

End goe_form_process.

Section lambda_max_net.
Context {R : realType}.

(* On an eps-net of the unit sphere, the largest value of the quadratic form
   is within 2 eps opnorm A of lambda_max A. *)
Lemma lambda_max_net_le n (A : 'M[R]_n) k (xs : 'I_k.+1 -> 'cV[R]_n)
    (eps : R) : (0 < n)%N -> (forall t, frobenius (xs t) = 1) ->
  (forall y, frobenius y = 1 -> exists t, frobenius (y - xs t) <= eps) ->
  lambda_max A <= rmax (\row_t mxdot (xs t) (A *m xs t)) + 2 * eps * opnorm A.
Proof.
move=> n0 xs1 net; have [v v1 <-] := lambda_max_attained A n0.
have fv : frobenius v = 1 by rewrite /frobenius v1 sqrtr1.
have [t vt] := net v fv; set y := xs t.
have -> : mxdot v (A *m v) =
    mxdot y (A *m y) + mxdot (v - y) (A *m v) + mxdot y (A *m (v - y)).
  by rewrite mulmxBr mxdotBl mxdotBr; ring.
have b1 : mxdot (v - y) (A *m v) <= eps * opnorm A.
  rewrite (le_trans (ler_norm _)) // (le_trans (mxdot_opnorm _ _ _)) //.
  rewrite fv mulr1.
  by rewrite mulrC ler_wpM2r ?opnorm_ge0.
have b2 : mxdot y (A *m (v - y)) <= eps * opnorm A.
  rewrite (le_trans (ler_norm _)) // (le_trans (mxdot_opnorm _ _ _)) // xs1.
  by rewrite mulr1 mulrC ler_wpM2r ?opnorm_ge0.
have b0 : mxdot y (A *m y) <= rmax (\row_t mxdot (xs t) (A *m xs t)).
  by have := le_rmax (\row_t mxdot (xs t) (A *m xs t)) t; rewrite mxE.
lra.
Qed.

End lambda_max_net.

Section goe_lambda_max.
Context {R : realType} (d : nat).
Local Notation gauss := (@gauss R).

Lemma goe_lambda_max_lipschitz (a b : 'rV[R]_(d * d)) :
  `|lambda_max (goe_mx a) - lambda_max (goe_mx b)| <=
  Num.sqrt (2 / d%:R) * frobenius (a - b).
Proof.
apply: le_trans (lambda_max_lipschitz _ _) _.
by rewrite -goe_mxB (le_trans (opnorm_le_frobenius _)) // frobenius_goe_mx.
Qed.

Lemma goe_lambda_maxN_lipschitz (a b : 'rV[R]_(d * d)) :
  `|lambda_max (- goe_mx a) - lambda_max (- goe_mx b)| <=
  Num.sqrt (2 / d%:R) * frobenius (a - b).
Proof.
rewrite -!goe_mxN; apply: le_trans (goe_lambda_max_lipschitz _ _) _.
by rewrite -opprD frobeniusN.
Qed.

Lemma measurable_goe_lambda_max :
  measurable_fun [set: 'rV[R]_(d * d)] (fun a => lambda_max (goe_mx a)).
Proof.
exact: continuous_measurable_mx
  (lipschitz_frobenius_continuous goe_lambda_max_lipschitz).
Qed.

Lemma measurable_goe_lambda_maxN :
  measurable_fun [set: 'rV[R]_(d * d)] (fun a => lambda_max (- goe_mx a)).
Proof.
exact: continuous_measurable_mx
  (lipschitz_frobenius_continuous goe_lambda_maxN_lipschitz).
Qed.

Lemma integrable_goe_lambda_max : (gauss (d * d)).-integrable
  [set: 'rV[R]_(d * d)] (EFin \o (fun a => lambda_max (goe_mx a))).
Proof. exact: integrable_gauss_lipschitz goe_lambda_max_lipschitz. Qed.

Lemma integrable_goe_lambda_maxN : (gauss (d * d)).-integrable
  [set: 'rV[R]_(d * d)] (EFin \o (fun a => lambda_max (- goe_mx a))).
Proof. exact: integrable_gauss_lipschitz goe_lambda_maxN_lipschitz. Qed.

(* E lambda_max W <= 2. *)
Theorem goe_lambda_max_mean : (0 < d)%N ->
  \int[gauss (d * d)]_a lambda_max (goe_mx a) <= 2.
Proof.
move=> d0; apply/ler_addgt0Pr => e e0.
set eps := e / 8.
have eps0 : 0 < eps by rewrite divr_gt0.
have [k [xs [xs1 _ xsnet]]] := @sym_sphere_net R d eps eps0 d0.
have hp a : lambda_max (goe_mx a) <=
    rmax (a *m goe_form_mx xs) + 2 * eps * opnorm (goe_mx a).
  have -> : a *m goe_form_mx xs = \row_t mxdot (xs t) (goe_mx a *m xs t).
    by apply/rowP => t; rewrite goe_form_mxE mxE.
  exact: lambda_max_net_le.
have iL := integrable_goe_lambda_max.
have iM := integrable_gauss_rmax (goe_form_mx xs).
have iO := integrable_goe_opnorm d.
have iO' : (gauss (d * d)).-integrable [set: 'rV[R]_(d * d)]
    (EFin \o (fun a => 2 * eps * opnorm (goe_mx a))).
  rewrite (_ : _ \o _ = (fun a => (2 * eps)%:E * (opnorm (goe_mx a))%:E)%E).
    by apply/funext => a.
  exact: integrableZl.
have iS : (gauss (d * d)).-integrable [set: 'rV[R]_(d * d)]
    (EFin \o (fun a =>
      rmax (a *m goe_form_mx xs) + 2 * eps * opnorm (goe_mx a))).
  rewrite (_ : _ \o _ = (EFin \o (fun a => rmax (a *m goe_form_mx xs))) \+
    (EFin \o (fun a => 2 * eps * opnorm (goe_mx a)))) //.
  exact: integrableD.
apply: le_trans (_ : \int[gauss (d * d)]_a
    (rmax (a *m goe_form_mx xs) + 2 * eps * opnorm (goe_mx a)) <= _).
  by apply: le_Rintegral => // a _; exact: hp.
rewrite RintegralD // RintegralZl //.
have hm := goe_form_max_mean d0 xs1.
have ho := goe_opnorm_mean d0.
have s2 : Num.sqrt 2 <= 2 :> R.
  have s0 := @sqrtr_ge0 R 2; have := @sqr_sqrtr R 2 (ler0n _ 2).
  rewrite /GRing.exp /=; nra.
have : 2 * eps * \int[gauss (d * d)]_a opnorm (goe_mx a) <= e.
  apply: le_trans (_ : 2 * eps * (2 * Num.sqrt 2) <= _).
    by apply: ler_wpM2l; [rewrite mulr_ge0 // ltW | exact: ho].
  by rewrite /eps; nra.
lra.
Qed.

(* E lambda_max (- W) <= 2: - W = goe_mx (- a) has the law of W. *)
Theorem goe_lambda_maxN_mean : (0 < d)%N ->
  \int[gauss (d * d)]_a lambda_max (- goe_mx a) <= 2.
Proof.
move=> d0; rewrite /Rintegral.
have -> : (\int[gauss (d * d)]_a (lambda_max (- goe_mx a))%:E =
    \int[gauss (d * d)]_a (lambda_max (goe_mx a))%:E)%E.
  rewrite -(integral_gauss_opp integrable_goe_lambda_max).
  by apply: eq_integral => a _; rewrite /= goe_mxN.
exact: goe_lambda_max_mean.
Qed.

Lemma goe_edge_exponent (t : R) : (0 < d)%N ->
  - t ^+ 2 / (2 * Num.sqrt (2 / d%:R) ^+ 2) = - (d%:R * t ^+ 2 / 4).
Proof.
move=> d0; rewrite sqr_sqrtr ?divr_ge0 ?ler0n //.
have dn : d%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
by field.
Qed.

(* P(lambda_max W >= 2 + t) <= exp (- d t^2 / 4). *)
Theorem goe_lambda_max_tail (t : R) : (0 < d)%N -> 0 <= t ->
  (gauss (d * d) [set a | 2 + t <= lambda_max (goe_mx a)]%R <=
   (expR (- (d%:R * t ^+ 2 / 4)))%:E)%E.
Proof.
move=> d0 t0.
have mI (A : set R) : measurable A ->
    measurable ((fun a : 'rV[R]_(d * d) => lambda_max (goe_mx a)) @^-1` A).
  move=> mA; rewrite -[X in measurable X]setTI.
  exact: measurable_goe_lambda_max.
have := gauss_concentration_upper_tail goe_lambda_max_lipschitz t0.
rewrite goe_edge_exponent //; apply: le_trans; apply: le_measure; rewrite ?inE.
- by rewrite -preimage_itvcy; apply: mI; exact: measurable_itv.
- by rewrite -preimage_itvcy; apply: mI; exact: measurable_itv.
- by move=> a /=; have := goe_lambda_max_mean d0; lra.
Qed.

(* P(lambda_max (- W) >= 2 + t) <= exp (- d t^2 / 4). *)
Theorem goe_lambda_maxN_tail (t : R) : (0 < d)%N -> 0 <= t ->
  (gauss (d * d) [set a | 2 + t <= lambda_max (- goe_mx a)]%R <=
   (expR (- (d%:R * t ^+ 2 / 4)))%:E)%E.
Proof.
move=> d0 t0.
have mI (A : set R) : measurable A ->
    measurable ((fun a : 'rV[R]_(d * d) => lambda_max (- goe_mx a)) @^-1` A).
  move=> mA; rewrite -[X in measurable X]setTI.
  exact: measurable_goe_lambda_maxN.
have := gauss_concentration_upper_tail goe_lambda_maxN_lipschitz t0.
rewrite goe_edge_exponent //; apply: le_trans; apply: le_measure; rewrite ?inE.
- by rewrite -preimage_itvcy; apply: mI; exact: measurable_itv.
- by rewrite -preimage_itvcy; apply: mI; exact: measurable_itv.
- by move=> a /=; have := goe_lambda_maxN_mean d0; lra.
Qed.

(* P(opnorm W >= 2 + t) <= 2 exp (- d t^2 / 4). *)
Theorem goe_opnorm_edge_tail (t : R) : (0 < d)%N -> 0 <= t ->
  (gauss (d * d) [set a | 2 + t <= opnorm (goe_mx a)]%R <=
   (2 * expR (- (d%:R * t ^+ 2 / 4)))%:E)%E.
Proof.
move=> d0 t0.
have -> : [set a : 'rV[R]_(d * d) | 2 + t <= opnorm (goe_mx a)]%R =
    [set a : 'rV[R]_(d * d) | 2 + t <= lambda_max (goe_mx a)]%R `|`
    [set a : 'rV[R]_(d * d) | 2 + t <= lambda_max (- goe_mx a)]%R.
  apply/seteqP; split => a /=.
    rewrite opnorm_lambda_max ?goe_mx_symmetric // le_max.
    by move=> /orP[]; [left|right].
  rewrite opnorm_lambda_max ?goe_mx_symmetric // le_max.
  by move=> -[] ->; rewrite ?orbT.
have mI (F : 'rV[R]_(d * d) -> R) (A : set R) : measurable_fun setT F ->
    measurable A -> measurable (F @^-1` A).
  by move=> mF mA; rewrite -[X in measurable X]setTI; exact: mF.
apply: le_trans (measureU2 _ _ _) _.
- rewrite -preimage_itvcy; apply: mI; last exact: measurable_itv.
  exact: measurable_goe_lambda_max.
- rewrite -preimage_itvcy; apply: mI; last exact: measurable_itv.
  exact: measurable_goe_lambda_maxN.
rewrite mulr_natl mulr2n EFinD.
by apply: leeD; [exact: goe_lambda_max_tail|exact: goe_lambda_maxN_tail].
Qed.

End goe_lambda_max.
