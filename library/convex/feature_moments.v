From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis Require Import measurable_matrix euclidean opnorm.
From GaussianAnalysis Require Import least_squares lindeberg efron_stein.

(**md**************************************************************************)
(* # Moments of regular features                                              *)
(*                                                                            *)
(* The moment calculus behind Propositions 2.14 and 2.16 of Koehler and Sohn  *)
(* (arXiv 2608.27372): for a (K, tau)-regular feature mu on 'rV[R]_N with     *)
(* covariance Sigma (regular_feature of least_squares.v) and                  *)
(* lambda = opnorm Sigma, the polynomials of degree at most 4 in the          *)
(* coordinates are integrable, and the first two moments of the linear forms  *)
(* and of the quadratic forms z |-> z T z^T depend only on Sigma. Integrals   *)
(* are Rintegral, with values in R.                                           *)
(*                                                                            *)
(* - reg_integrable: a measurable g with |g z| <= a + b |z|^4 is integrable.  *)
(* - reg_mean, reg_cov: E <z, theta> = 0 and                                  *)
(*   E <z, theta> <z, theta'> = theta Sigma theta'^T.                         *)
(* - reg_quad_mean: E z T z^T = sum_b (e_b Sigma) . T_(., b), a function of   *)
(*   Sigma and T only; reg_quad_var: for T symmetric,                         *)
(*   E (z T z^T - E z T z^T)^2 <= tau^2 |T|_F^2.                              *)
(* - reg_resid2: E (b - <z, theta>)^2 = b^2 + theta Sigma theta^T;            *)
(*   reg_resid4: E (b - <z, theta>)^4 <= 8 (1 + K^4) S^2 with                 *)
(*   S = lambda |theta|^2 + b^2.                                              *)
(* - reg_ell_mean, reg_ell_var: for l z = c - 2 <v, z> + z T z^T with T       *)
(*   symmetric, E l z = c + E z T z^T and                                     *)
(*   E (l z - E l)^2 <= 2 tau^2 |T|_F^2 + 8 lambda |v|^2.                     *)
(* - form_le_opnorm: v Sigma v^T <= opnorm Sigma |v|^2.                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Rintegral_helpers.
Context d (U : measurableType d) (R : realType) (P : probability U R).

Lemma Rintegral_EFin (f : U -> R) :
  P.-integrable setT (EFin \o f) -> (\int[P]_x f x)%:E = (\int[P]_x (f x)%:E)%E.
Proof. by move=> fi; rewrite fineK // integrable_fin_num. Qed.

Lemma integrable_cst_prob (c : R) : P.-integrable setT (EFin \o cst c).
Proof. exact: (bounded_integrable P (measurable_cst c) (fun=> lexx `|c|)). Qed.

Lemma Rintegral_cst_prob (c : R) : \int[P]_x c = c.
Proof. by rewrite Rintegral_cst // [X in c * fine X]probability_setT mulr1. Qed.

Lemma integrableR_sum I (s : seq I) (h : I -> U -> R) :
  (forall i, P.-integrable setT (EFin \o h i)) ->
  P.-integrable setT (EFin \o (fun x => \sum_(i <- s) h i x)).
Proof.
move=> hi.
have iS : P.-integrable setT (fun x => (\sum_(j <- s) (h j x)%:E)%E).
  by apply: (integrable_sum measurableT) => j _; exact: hi.
by apply: (eq_integrable measurableT _ _ _ iS) => x _; rewrite /= sumEFin.
Qed.

Lemma Rintegral_sumr I (s : seq I) (h : I -> U -> R) :
  (forall i, P.-integrable setT (EFin \o h i)) ->
  \int[P]_x (\sum_(i <- s) h i x) = \sum_(i <- s) \int[P]_x h i x.
Proof.
move=> hi; elim: s => [|i s IH].
  rewrite big_nil; under eq_Rintegral do rewrite big_nil.
  exact: Rintegral_cst_prob.
under eq_Rintegral do rewrite big_cons.
by rewrite (RintegralD measurableT (hi i) (integrableR_sum s hi)) IH big_cons.
Qed.

Lemma integrableRD (f g : U -> R) :
  P.-integrable setT (EFin \o f) -> P.-integrable setT (EFin \o g) ->
  P.-integrable setT (EFin \o (fun x => f x + g x)).
Proof.
move=> fi gi.
by apply: (eq_integrable measurableT _ _ _ (integrableD measurableT fi gi)).
Qed.

Lemma integrableRB (f g : U -> R) :
  P.-integrable setT (EFin \o f) -> P.-integrable setT (EFin \o g) ->
  P.-integrable setT (EFin \o (fun x => f x - g x)).
Proof.
move=> fi gi.
by apply: (eq_integrable measurableT _ _ _ (integrableB measurableT fi gi)).
Qed.

Lemma integrableRZl (c : R) (f : U -> R) :
  P.-integrable setT (EFin \o f) ->
  P.-integrable setT (EFin \o (fun x => c * f x)).
Proof.
move=> fi.
apply: (eq_integrable measurableT _ _ _ (integrableZl measurableT c fi)).
by move=> x _; rewrite /= EFinM.
Qed.

Lemma integrableRZr (c : R) (f : U -> R) :
  P.-integrable setT (EFin \o f) ->
  P.-integrable setT (EFin \o (fun x => f x * c)).
Proof.
move=> fi; apply: (eq_integrable measurableT _ _ _ (integrableRZl c fi)).
by move=> x _; rewrite /= mulrC.
Qed.

End Rintegral_helpers.

Section linear_forms.
Context {R : realType} {N : nat}.

Lemma continuous_mxdotl (th : 'rV[R]_N) :
  continuous (fun z : 'rV[R]_N => mxdot z th).
Proof.
have -> : (fun z : 'rV[R]_N => mxdot z th) = (fun z => (z *m th^T) 0 0).
  by apply/funext => z; rewrite mxdot_rowE.
move=> z; apply: (@continuous_comp _ _ _ (fun w : 'rV[R]_N => w *m th^T)
  (fun M : 'M[R]_1 => M 0 0)).
  exact: continuous_mulmxr.
exact: coord_continuous.
Qed.

Lemma measurable_mxdotl (th : 'rV[R]_N) :
  measurable_fun setT (fun z : 'rV[R]_N => mxdot z th).
Proof. by apply: continuous_measurable_mx; exact: continuous_mxdotl. Qed.

(* A quadratic form is a sum of products of two linear forms. *)
Lemma mxdot_quadE (T : 'M[R]_N) (z : 'rV[R]_N) :
  mxdot z (z *m T) = \sum_b mxdot z (delta_mx 0 b) * mxdot z (col b T)^T.
Proof.
rewrite [LHS]/mxdot big_ord1; apply: eq_bigr => b _.
rewrite mxdot_delta; congr (_ * _).
by rewrite /mxdot big_ord1 mxE; apply: eq_bigr => j _; rewrite !mxE.
Qed.

Lemma measurable_quad (T : 'M[R]_N) :
  measurable_fun setT (fun z : 'rV[R]_N => mxdot z (z *m T)).
Proof.
have -> : (fun z : 'rV[R]_N => mxdot z (z *m T)) = (fun z : 'rV[R]_N =>
    \sum_b mxdot z (delta_mx 0 b) * mxdot z (col b T)^T).
  by apply/funext => z; exact: mxdot_quadE.
by apply: measurable_sum => b; apply: measurable_funM; exact: measurable_mxdotl.
Qed.

Lemma measurable_norm2 : measurable_fun setT (fun z : 'rV[R]_N => mxdot z z).
Proof.
have -> : (fun z : 'rV[R]_N => mxdot z z) =
    (fun z : 'rV[R]_N => mxdot z (z *m 1%:M)).
  by apply/funext => z; rewrite mulmx1.
exact: measurable_quad.
Qed.

Lemma mxdot_sqr_sum (z : 'rV[R]_N) :
  mxdot z z ^+ 2 <= N%:R * \sum_a mxdot z (delta_mx 0 a) ^+ 4.
Proof.
have -> : mxdot z z = \sum_a mxdot z (delta_mx 0 a) ^+ 2 * 1.
  rewrite /mxdot big_ord1; apply: eq_bigr => a _.
  by rewrite mulr1 -/(mxdot z (delta_mx 0 a)) mxdot_delta expr2.
apply: le_trans (sum_cauchy_schwarz _ _) _.
have -> : \sum_(i < N) (1 * 1 : R) = N%:R.
  by under eq_bigr do rewrite mulr1; rewrite sumr_const card_ord.
rewrite mulrC; apply: ler_wpM2l; first exact: ler0n.
by apply: ler_sum => a _; rewrite -exprD.
Qed.

Lemma quad_le_frobenius (T : 'M[R]_N) (z : 'rV[R]_N) :
  `|mxdot z (z *m T)| <= frobenius T * mxdot z z.
Proof.
apply: le_trans (mxdot_le _ _) _.
apply: le_trans (ler_wpM2l (frobenius_ge0 _) (frobenius_mulmx _ _)) _.
by rewrite mulrA -expr2 frobenius_sqr mulrC.
Qed.

Lemma form_le_opnorm (Sigma : 'M[R]_N) (v : 'rV[R]_N) :
  mxdot (v *m Sigma) v <= opnorm Sigma * mxdot v v.
Proof.
have h := mxdot_opnorm Sigma^T v^T v^T.
rewrite opnorm_trmx !frobenius_trmx in h.
have -> : mxdot (v *m Sigma) v = mxdot v^T (Sigma^T *m v^T).
  by rewrite mxdotC -mxdot_trmx trmx_mul.
apply: le_trans (ler_norm _) _; apply: le_trans h _.
by rewrite -mulrA -expr2 frobenius_sqr.
Qed.

End linear_forms.

Section regular_moments.
Context {R : realType} {N : nat}.
Variables (K tau : R) (Sigma : 'M[R]_N) (mu : probability 'rV[R]_N R).
Hypothesis reg : regular_feature K tau Sigma mu.
Local Notation lambda := (opnorm Sigma).

Lemma reg_lambda_gt0 : 0 < lambda.
Proof. by case: reg. Qed.

Lemma reg_int4 (th : 'rV[R]_N) :
  mu.-integrable setT (EFin \o (fun z => mxdot z th ^+ 4)).
Proof.
have [_ F1 _ _ _] := reg.
apply/integrableP; split.
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_mxdotl.
have := F1 th; rewrite unlock /= => h.
apply: (le_lt_trans _ (ltry (K ^+ 4 * lambda ^+ 2 * mxdot th th ^+ 2))).
apply: le_trans h; rewrite le_eqVlt; apply/orP; left; apply/eqP.
by apply: eq_integral => z _; rewrite ger0_norm ?exprn_even_ge0.
Qed.

Lemma reg_moment4 (th : 'rV[R]_N) :
  \int[mu]_z (mxdot z th ^+ 4) <= K ^+ 4 * lambda ^+ 2 * mxdot th th ^+ 2.
Proof.
have [_ F1 _ _ _] := reg.
rewrite -lee_fin (Rintegral_EFin (reg_int4 th)).
by have := F1 th; rewrite unlock.
Qed.

Lemma reg_int_norm4 : mu.-integrable setT (EFin \o (fun z => mxdot z z ^+ 2)).
Proof.
have i4 : mu.-integrable setT
    (fun z => (\sum_a (mxdot z (delta_mx 0 a) ^+ 4)%:E)%E).
  by apply: (integrable_sum measurableT) => a _; exact: reg_int4.
have iN := integrableZl measurableT N%:R i4.
apply: (le_integrable measurableT _ _ iN).
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_norm2.
move=> z _; rewrite /= sumEFin -EFinM /= lee_fin.
rewrite [`|mxdot z z ^+ 2|]ger0_norm ?sqr_ge0 //.
exact: le_trans (mxdot_sqr_sum z) (ler_norm _).
Qed.

(* Domination by a + b |z|^4. *)
Lemma reg_integrable (g : 'rV[R]_N -> R) (a b : R) :
  measurable_fun setT g -> (forall z, `|g z| <= a + b * mxdot z z ^+ 2) ->
  mu.-integrable setT (EFin \o g).
Proof.
move=> mg gb.
have ia := integrable_cst_prob mu a.
have ib := integrableZl measurableT b reg_int_norm4.
have iab := integrableD measurableT ia ib.
apply: (le_integrable measurableT _ _ iab); first exact/measurable_EFinP.
move=> z _ /=; rewrite lee_fin.
exact: le_trans (gb z) (ler_norm _).
Qed.

Lemma le1_sqr (x : R) : 0 <= x -> x <= 1 + x ^+ 2.
Proof. by move=> x0; have := sqr_ge0 (x - 1); nra. Qed.

Lemma reg_int_sqr (th : 'rV[R]_N) :
  mu.-integrable setT (EFin \o (fun z => mxdot z th ^+ 2)).
Proof.
apply: (@reg_integrable _ (mxdot th th) (mxdot th th)).
  by apply: measurable_funX; exact: measurable_mxdotl.
move=> z; rewrite ger0_norm ?sqr_ge0 //.
have cs := mxdot_cauchy_schwarz z th.
have t0 := mxdot_ge0 th.
have := le1_sqr (mxdot_ge0 z); by nra.
Qed.

Lemma reg_int_lin (th : 'rV[R]_N) :
  mu.-integrable setT (EFin \o (fun z => mxdot z th)).
Proof.
apply: (@reg_integrable _ (1 + mxdot th th) (mxdot th th)).
  exact: measurable_mxdotl.
move=> z; have cs := mxdot_cauchy_schwarz z th.
have t0 := mxdot_ge0 th.
have h1 : `|mxdot z th| <= 1 + mxdot z th ^+ 2.
  by rewrite -real_normK ?num_real //; exact: le1_sqr.
have := le1_sqr (mxdot_ge0 z); by nra.
Qed.

Lemma reg_int_lin2 (th th' : 'rV[R]_N) :
  mu.-integrable setT (EFin \o (fun z => mxdot z th * mxdot z th')).
Proof.
apply: (@reg_integrable _ ((mxdot th th + mxdot th' th') / 2)
  ((mxdot th th + mxdot th' th') / 2)).
  by apply: measurable_funM; exact: measurable_mxdotl.
move=> z; have cs := mxdot_cauchy_schwarz z th.
have cs' := mxdot_cauchy_schwarz z th'.
have t0 := mxdot_ge0 th; have t0' := mxdot_ge0 th'.
have h1 : `|mxdot z th * mxdot z th'| <=
    (mxdot z th ^+ 2 + mxdot z th' ^+ 2) / 2.
  rewrite normrM -(real_normK (num_real (mxdot z th))).
  rewrite -(real_normK (num_real (mxdot z th'))).
  have := sqr_ge0 (`|mxdot z th| - `|mxdot z th'|); by nra.
have := le1_sqr (mxdot_ge0 z); by nra.
Qed.

Lemma reg_int_quad (T : 'M[R]_N) :
  mu.-integrable setT (EFin \o (fun z => mxdot z (z *m T))).
Proof.
apply: (@reg_integrable _ (frobenius T) (frobenius T)).
  exact: measurable_quad.
move=> z; apply: le_trans (quad_le_frobenius T z) _.
have f0 := frobenius_ge0 T.
have := le1_sqr (mxdot_ge0 z); by nra.
Qed.

Lemma quad_sqr_le (T : 'M[R]_N) (z : 'rV[R]_N) :
  mxdot z (z *m T) ^+ 2 <= frobenius T ^+ 2 * mxdot z z ^+ 2.
Proof.
rewrite -exprMn -real_normK ?num_real //.
rewrite ler_sqr ?nnegrE ?normr_ge0 ?mulr_ge0 ?frobenius_ge0 ?mxdot_ge0 //.
exact: quad_le_frobenius.
Qed.

Lemma reg_int_quad2 (T : 'M[R]_N) (c : R) :
  mu.-integrable setT (EFin \o (fun z => (mxdot z (z *m T) - c) ^+ 2)).
Proof.
apply: (@reg_integrable _ (2 * c ^+ 2) (2 * frobenius T ^+ 2)).
  apply: measurable_funX; apply: measurable_funB; last exact: measurable_cst.
  exact: measurable_quad.
move=> z; rewrite ger0_norm ?sqr_ge0 //.
have q2 := quad_sqr_le T z.
have := sqr_ge0 (mxdot z (z *m T) + c); by nra.
Qed.

Lemma reg_int_resid2 (th : 'rV[R]_N) (b : R) :
  mu.-integrable setT (EFin \o (fun z => (b - mxdot z th) ^+ 2)).
Proof.
apply: (@reg_integrable _ (2 * b ^+ 2 + 2 * mxdot th th) (2 * mxdot th th)).
  apply: measurable_funX; apply: measurable_funB; first exact: measurable_cst.
  exact: measurable_mxdotl.
move=> z; rewrite ger0_norm ?sqr_ge0 //.
have cs := mxdot_cauchy_schwarz z th.
have t0 := mxdot_ge0 th.
have zz := le1_sqr (mxdot_ge0 z).
have := sqr_ge0 (b + mxdot z th); by nra.
Qed.

Lemma reg_int_ell2 (c : R) (v : 'rV[R]_N) (T : 'M[R]_N) (d : R) :
  mu.-integrable setT
    (EFin \o (fun z => (c - 2 * mxdot z v + mxdot z (z *m T) - d) ^+ 2)).
Proof.
apply: (@reg_integrable _ (4 * (d - c) ^+ 2 + 8 * mxdot v v)
  (4 * frobenius T ^+ 2 + 8 * mxdot v v)).
  apply: measurable_funX; apply: measurable_funB; last exact: measurable_cst.
  apply: measurable_funD; last exact: measurable_quad.
  apply: measurable_funB; first exact: measurable_cst.
  by apply: measurable_funM; [exact: measurable_cst | exact: measurable_mxdotl].
move=> z; rewrite ger0_norm ?sqr_ge0 //.
have q2 := quad_sqr_le T z.
have cs := mxdot_cauchy_schwarz z v.
have v0 := mxdot_ge0 v.
have zz := le1_sqr (mxdot_ge0 z).
set a := mxdot z (z *m T) in q2 *; set y := mxdot z v in cs *.
have e1 : (c - 2 * y + a - d) ^+ 2 <= 2 * (a - (d - c)) ^+ 2 + 8 * y ^+ 2.
  have := sqr_ge0 (a - (d - c) + 2 * y); by nra.
have e2 : (a - (d - c)) ^+ 2 <= 2 * a ^+ 2 + 2 * (d - c) ^+ 2.
  have := sqr_ge0 (a + (d - c)); by nra.
have e3 : y ^+ 2 <= mxdot v v * (1 + mxdot z z ^+ 2).
  have := mxdot_ge0 z; by nra.
by nra.
Qed.

Lemma reg_mean (th : 'rV[R]_N) : \int[mu]_z mxdot z th = 0.
Proof.
have [_ _ F2 _ _] := reg.
by have := F2 th; rewrite unlock /= => h; rewrite /Rintegral h.
Qed.

Lemma reg_cov (th th' : 'rV[R]_N) :
  \int[mu]_z (mxdot z th * mxdot z th') = mxdot (th *m Sigma) th'.
Proof.
have [_ _ _ F3 _] := reg.
by have := F3 th th'; rewrite unlock /= => h; rewrite /Rintegral h.
Qed.

Lemma reg_quad_mean (T : 'M[R]_N) :
  \int[mu]_z mxdot z (z *m T) =
  \sum_b mxdot (delta_mx 0 b *m Sigma) (col b T)^T.
Proof.
under eq_Rintegral do rewrite mxdot_quadE.
rewrite (Rintegral_sumr _ (fun b => reg_int_lin2 (delta_mx 0 b) (col b T)^T)).
by apply: eq_bigr => b _; exact: reg_cov.
Qed.

Lemma reg_quad_var (T : 'M[R]_N) : T \is symmetricmx ->
  \int[mu]_z ((mxdot z (z *m T) - \int[mu]_y mxdot y (y *m T)) ^+ 2) <=
  tau ^+ 2 * frobenius T ^+ 2.
Proof.
move=> Ts; have [_ _ _ _ F4] := reg.
rewrite -lee_fin (Rintegral_EFin (reg_int_quad2 T _)).
by have := F4 T Ts; rewrite varianceT.
Qed.

Lemma reg_resid2 (th : 'rV[R]_N) (b : R) :
  \int[mu]_z ((b - mxdot z th) ^+ 2) = b ^+ 2 + mxdot (th *m Sigma) th.
Proof.
have -> : (fun z => (b - mxdot z th) ^+ 2) =
    (fun z => (b ^+ 2 - 2 * b * mxdot z th) + mxdot z th * mxdot z th).
  by apply/funext => z; ring.
have ic := integrable_cst_prob mu (b ^+ 2).
have il := integrableZl measurableT (2 * b) (reg_int_lin th).
have il' : mu.-integrable setT (EFin \o (fun z => 2 * b * mxdot z th)).
  by apply: (eq_integrable measurableT _ _ _ il) => z _; rewrite /= EFinM.
have icl : mu.-integrable setT
    (EFin \o (fun z => b ^+ 2 - 2 * b * mxdot z th)).
  apply: (eq_integrable measurableT _ _ _ (integrableB measurableT ic il')).
  move=> z _.
  by rewrite /= EFinB.
rewrite (RintegralD measurableT icl (reg_int_lin2 th th)).
rewrite (RintegralB measurableT ic il') Rintegral_cst_prob.
rewrite (RintegralZl _ measurableT (reg_int_lin th)).
by rewrite reg_mean reg_cov mulr0 subr0.
Qed.

Lemma resid4_le (b y : R) : (b - y) ^+ 4 <= 8 * b ^+ 4 + 8 * y ^+ 4.
Proof.
have h1 : (b - y) ^+ 2 <= 2 * (b ^+ 2 + y ^+ 2).
  have := sqr_ge0 (b + y); by nra.
have h2 : (b - y) ^+ 4 <= 4 * (b ^+ 2 + y ^+ 2) ^+ 2.
  have -> : (b - y) ^+ 4 = ((b - y) ^+ 2) ^+ 2 by rewrite -exprM.
  have -> : 4 * (b ^+ 2 + y ^+ 2) ^+ 2 = (2 * (b ^+ 2 + y ^+ 2)) ^+ 2.
    by rewrite exprMn; congr (_ * _); rewrite expr2 -natrM.
  by rewrite ler_sqr ?nnegrE ?sqr_ge0 ?mulr_ge0 ?addr_ge0 ?sqr_ge0.
have h3 : (b ^+ 2 + y ^+ 2) ^+ 2 <= 2 * (b ^+ 4 + y ^+ 4).
  have := sqr_ge0 (b ^+ 2 - y ^+ 2).
  have -> : b ^+ 4 = (b ^+ 2) ^+ 2 by rewrite -exprM.
  have -> : y ^+ 4 = (y ^+ 2) ^+ 2 by rewrite -exprM.
  by nra.
by lra.
Qed.

Lemma reg_int_resid4 (th : 'rV[R]_N) (b : R) :
  mu.-integrable setT (EFin \o (fun z => (b - mxdot z th) ^+ 4)).
Proof.
apply: (@reg_integrable _ (8 * b ^+ 4) (8 * mxdot th th ^+ 2)).
  apply: measurable_funX; apply: measurable_funB; first exact: measurable_cst.
  exact: measurable_mxdotl.
move=> z; rewrite ger0_norm ?exprn_even_ge0 //.
have cs := mxdot_cauchy_schwarz z th.
have y2 : mxdot z th ^+ 4 <= mxdot th th ^+ 2 * mxdot z z ^+ 2.
  have -> : mxdot z th ^+ 4 = (mxdot z th ^+ 2) ^+ 2 by rewrite -exprM.
  rewrite -exprMn ler_sqr ?nnegrE ?sqr_ge0 ?mulr_ge0 ?mxdot_ge0 //.
  by rewrite mulrC.
have := resid4_le b (mxdot z th); by lra.
Qed.

Lemma reg_resid4 (th : 'rV[R]_N) (b : R) :
  \int[mu]_z ((b - mxdot z th) ^+ 4) <=
  8 * (1 + K ^+ 4) * (lambda * mxdot th th + b ^+ 2) ^+ 2.
Proof.
have i4 := reg_int4 th.
have ib := integrable_cst_prob mu (8 * b ^+ 4).
have i8 := integrableZl measurableT 8 i4.
have i8' : mu.-integrable setT (EFin \o (fun z => 8 * mxdot z th ^+ 4)).
  by apply: (eq_integrable measurableT _ _ _ i8) => z _; rewrite /= EFinM.
have i48 : mu.-integrable setT
    (EFin \o (fun z => 8 * b ^+ 4 + 8 * mxdot z th ^+ 4)).
  apply: (eq_integrable measurableT _ _ _ (integrableD measurableT ib i8')).
  by move=> z _; rewrite /= EFinD.
apply: le_trans (_ : \int[mu]_z (8 * b ^+ 4 + 8 * mxdot z th ^+ 4) <= _).
  apply: (le_Rintegral measurableT (reg_int_resid4 th b) i48) => z _.
  exact: resid4_le.
rewrite (RintegralD measurableT ib i8') Rintegral_cst_prob.
rewrite (RintegralZl _ measurableT i4).
have m4 := reg_moment4 th.
have K4 : 0 <= K ^+ 4 by rewrite exprn_even_ge0.
have l0 := ltW reg_lambda_gt0; have t0 := mxdot_ge0 th.
have L0 : 0 <= lambda * mxdot th th by rewrite mulr_ge0.
have e : K ^+ 4 * lambda ^+ 2 * mxdot th th ^+ 2 =
    K ^+ 4 * (lambda * mxdot th th) ^+ 2 by ring.
rewrite e in m4.
move: L0 m4; set L := lambda * mxdot th th => L0 m4.
have -> : b ^+ 4 = (b ^+ 2) ^+ 2 by rewrite -exprM.
have b2 := sqr_ge0 b.
move: m4 K4 b2; set I := \int[mu]_x _; set k := K ^+ 4; set B := b ^+ 2.
move=> m4 K4 b2.
have h2 : 0 <= L * B := mulr_ge0 L0 b2.
have h1 : 0 <= k * (L * B) := mulr_ge0 K4 h2.
have h3 : 0 <= k * B ^+ 2 := mulr_ge0 K4 (sqr_ge0 B).
have h4 : 0 <= L ^+ 2 := sqr_ge0 L.
by nra.
Qed.

Lemma reg_ell_int (c : R) (v : 'rV[R]_N) (T : 'M[R]_N) :
  mu.-integrable setT
    (EFin \o (fun z => c - 2 * mxdot z v + mxdot z (z *m T))).
Proof.
have ic := integrable_cst_prob mu c.
have il := integrableZl measurableT 2 (reg_int_lin v).
have iq := reg_int_quad T.
apply: (eq_integrable measurableT _ _ _
  (integrableD measurableT (integrableB measurableT ic il) iq)).
by move=> z _ /=; rewrite -!EFinD.
Qed.

Lemma reg_ell_mean (c : R) (v : 'rV[R]_N) (T : 'M[R]_N) :
  \int[mu]_z (c - 2 * mxdot z v + mxdot z (z *m T)) =
  c + \sum_b mxdot (delta_mx 0 b *m Sigma) (col b T)^T.
Proof.
have ic := integrable_cst_prob mu c.
have il := integrableZl measurableT 2 (reg_int_lin v).
have il' : mu.-integrable setT (EFin \o (fun z => 2 * mxdot z v)).
  by apply: (eq_integrable measurableT _ _ _ il) => z _; rewrite /= EFinM.
have icl : mu.-integrable setT (EFin \o (fun z => c - 2 * mxdot z v)).
  apply: (eq_integrable measurableT _ _ _ (integrableB measurableT ic il')).
  move=> z _.
  by rewrite /= EFinB.
rewrite (RintegralD measurableT icl (reg_int_quad T)) reg_quad_mean.
rewrite (RintegralB measurableT ic il') Rintegral_cst_prob.
by rewrite (RintegralZl _ measurableT (reg_int_lin v)) reg_mean mulr0 subr0.
Qed.

Lemma reg_ell_var (c : R) (v : 'rV[R]_N) (T : 'M[R]_N) : T \is symmetricmx ->
  \int[mu]_z ((c - 2 * mxdot z v + mxdot z (z *m T) -
     \int[mu]_y (c - 2 * mxdot y v + mxdot y (y *m T))) ^+ 2) <=
  2 * tau ^+ 2 * frobenius T ^+ 2 + 8 * lambda * mxdot v v.
Proof.
move=> Ts; rewrite reg_ell_mean -reg_quad_mean.
set Qb := \int[mu]_y mxdot y (y *m T).
have iQ := reg_int_quad2 T Qb.
have iv := reg_int_sqr v.
have iQ2 : mu.-integrable setT
    (EFin \o (fun z => 2 * (mxdot z (z *m T) - Qb) ^+ 2)).
  apply: (eq_integrable measurableT _ _ _ (integrableZl measurableT 2 iQ)).
  by move=> z _; rewrite /= EFinM.
have iv8 : mu.-integrable setT (EFin \o (fun z => 8 * mxdot z v ^+ 2)).
  apply: (eq_integrable measurableT _ _ _ (integrableZl measurableT 8 iv)).
  by move=> z _; rewrite /= EFinM.
have i2 : mu.-integrable setT
    (EFin \o (fun z => 2 * (mxdot z (z *m T) - Qb) ^+ 2 + 8 * mxdot z v ^+ 2)).
  apply: (eq_integrable measurableT _ _ _ (integrableD measurableT iQ2 iv8)).
  by move=> z _; rewrite /= EFinD.
have il := reg_int_ell2 c v T (c + Qb).
apply: le_trans (_ : \int[mu]_z (2 * (mxdot z (z *m T) - Qb) ^+ 2 +
    8 * mxdot z v ^+ 2) <= _).
  apply: (le_Rintegral measurableT il i2) => z _.
  have := sqr_ge0 (mxdot z (z *m T) - Qb + 2 * mxdot z v); by nra.
rewrite (RintegralD measurableT iQ2 iv8).
rewrite (RintegralZl _ measurableT iQ) (RintegralZl _ measurableT iv).
have h1 := reg_quad_var Ts; rewrite -/Qb in h1.
have h2 : \int[mu]_z (mxdot z v ^+ 2) <= lambda * mxdot v v.
  under eq_Rintegral do rewrite expr2.
  by rewrite reg_cov; exact: form_le_opnorm.
by nra.
Qed.

End regular_moments.
