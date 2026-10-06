From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import interval topology normedtype.
From mathcomp Require Import derive realfun measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From GaussianAnalysis Require Import measurable_matrix normal_integral gauss.
From GaussianAnalysis Require Import gauss_ibp.

(**md**************************************************************************)
(* # Moments of the standard Gaussian measures                                *)
(*                                                                            *)
(* The moments of the standard normal law follow from Stein's identity:       *)
(* E[X^(k+2)] = (k + 1) E[X^k] (normal_momentS), so the odd moments vanish    *)
(* and E[X^(2k)] = 1 * 3 * ... * (2k - 1) (normal_moment_odd,                 *)
(* normal_moment_even). A vector x of law gauss n has mean 0 and covariance   *)
(* the identity (gauss_mean, gauss_cov), and x *m A has covariance            *)
(* A^T *m A (gauss_mulmx_cov).                                                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section normal_moments.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Let integrable_normal_exprnr k : N.-integrable [set: R] (fun x => (x ^+ k)%:E).
Proof.
apply: (integrable_normal_poly (C := 1) (k := k)) => [|x].
  by apply: measurable_funX; exact: measurable_id.
by rewrite normrX mul1r lerDr.
Qed.

Lemma normal_momentS k :
  (\int[N]_x (x ^+ k.+2)%:E = k.+1%:R%:E * \int[N]_x (x ^+ k)%:E)%E.
Proof.
have dX (x : R) : is_derive x 1 (fun y : R => y ^+ k.+1) (k.+1%:R * x ^+ k).
  apply: DeriveDef; first exact: exprn_derivable.
  by rewrite exp_derive /GRing.scale /= mulr1.
have cX : continuous (fun x : R => k.+1%:R * x ^+ k).
  by move=> x; apply: (cvgM (cvg_cst _)); exact: exprn_continuous.
have k1 : 1 <= k.+1%:R :> R by rewrite ler1n.
have b1 (x : R) : `|x ^+ k.+1| <= k.+1%:R * (1 + `|x| ^+ k.+1).
  by rewrite normrX; have := exprn_ge0 k.+1 (normr_ge0 x); nra.
have b2 (x : R) : `|k.+1%:R * x ^+ k| <= k.+1%:R * (1 + `|x| ^+ k.+1).
  rewrite normrM normrX ger0_norm ?ler0n //; apply: ler_wpM2l => //.
  case: (leP `|x| 1) => x1.
    by rewrite (le_trans (exprn_ile1 _ (normr_ge0 x) x1)) // lerDl exprn_ge0.
  have h : `|x| ^+ k <= `|x| ^+ k.+1.
    by rewrite exprS ler_peMl // ?exprn_ge0 // ltW.
  by apply: (le_trans h); rewrite lerDr.
have := normal_ibp dX cX b1 b2.
under eq_integral do rewrite -exprS.
move=> ->; under eq_integral do rewrite EFinM.
by rewrite integralZl.
Qed.

Lemma normal_mean : (\int[N]_x x%:E = 0)%E.
Proof.
have d1 (x : R) : is_derive x 1 (fun _ : R => 1 : R) 0 by exact: is_derive_cst.
have c0 : continuous (fun _ : R => 0 : R) by move=> x; exact: cvg_cst.
have b (x : R) : `|(fun _ : R => 1 : R) x| <= 1 * (1 + `|x| ^+ 0).
  by rewrite /= normr1 expr0 mul1r lerDr ler01.
have b' (x : R) : `|(fun _ : R => 0 : R) x| <= 1 * (1 + `|x| ^+ 0).
  by rewrite /= normr0 expr0 mul1r addr_ge0.
have := normal_ibp d1 c0 b b'; under eq_integral do rewrite mulr1.
by move=> ->; rewrite integral0.
Qed.

Lemma normal_moment_odd k : (\int[N]_x (x ^+ k.*2.+1)%:E = 0)%E.
Proof.
elim: k => [|k IH].
  by under eq_integral do rewrite expr1; exact: normal_mean.
have -> : k.+1.*2.+1 = (k.*2.+1).+2 by rewrite doubleS.
by rewrite normal_momentS IH mule0.
Qed.

Lemma normal_moment_even k :
  (\int[N]_x (x ^+ k.*2)%:E = (\prod_(i < k) i.*2.+1%:R)%:E)%E.
Proof.
elim: k => [|k IH].
  under eq_integral do rewrite expr0.
  by rewrite big_ord0 integral_cst //= probability_setT mule1.
have -> : k.+1.*2 = (k.*2).+2 by rewrite doubleS.
by rewrite normal_momentS IH big_ord_recr /= -EFinM mulrC.
Qed.

End normal_moments.

Section gauss_moments.
Context {R : realType}.

Lemma gauss_mean n (i : 'I_n) : (\int[gauss n]_x (x 0 i)%:E = 0 :> \bar R)%E.
Proof.
have iN : (@normal_prob R 0 1).-integrable [set: R] (fun t => t%:E).
  apply: (integrable_normal_poly (C := 1) (k := 1)) => [|x].
    exact: measurable_id.
  by rewrite expr1 mul1r lerDr.
by rewrite (integral_gauss_coord i iN); exact: normal_mean.
Qed.

Lemma gauss_cov n (i j : 'I_n) :
  (\int[gauss n]_x (x 0 i * x 0 j)%:E = (i == j)%:R%:E :> \bar R)%E.
Proof.
have dc (x : 'rV[R]_n) :
    is_derive x (delta_mx 0 i) (fun y : 'rV[R]_n => y 0 j) ((i == j)%:R).
  apply: (is_derive_transfer (G := fun t : R => t * (i == j)%:R + x 0 j)
    (b := 0) (w := 1)).
    by move=> h; rewrite !mxE /= addr0 [h%:A]mulr1 eq_sym.
  apply: is_derive_eq; rewrite ?mul1r ?addr0 ?mulr1 //.
  by rewrite scale0r add0r [_%:A]mulr1.
have cc : continuous (fun y : 'rV[R]_n => y 0 j).
  by move=> y; exact: coord_continuous.
have c1 : continuous (fun _ : 'rV[R]_n => (i == j)%:R : R).
  exact: cst_continuous.
have b1 (y : 'rV[R]_n) : `|y 0 j| <= 1 * (1 + `|y| ^+ 1).
  by rewrite mul1r expr1 (le_trans (mx_norm_entry_le y 0 j)) // lerDr.
have b2 (y : 'rV[R]_n) : `|(i == j)%:R : R| <= 1 * (1 + `|y| ^+ 1).
  by rewrite mul1r expr1; case: (i == j);
    rewrite ?normr1 ?normr0 ?lerDl ?addr_ge0.
rewrite (gauss_ibp dc cc c1 b1 b2).
by rewrite integral_cst //= probability_setT mule1.
Qed.

Lemma gauss_mulmx_cov n k (A : 'M[R]_(n, k)) (j l : 'I_k) :
  (\int[gauss n]_x ((x *m A) 0 j * (x *m A) 0 l)%:E = ((A^T *m A) j l)%:E)%E.
Proof.
have ixx (ii : 'I_n * 'I_n) : (gauss n).-integrable [set: 'rV[R]_n]
    (fun x : 'rV[R]_n => (x 0 ii.1 * x 0 ii.2)%:E).
  apply: (integrable_gauss_poly (C := 1) (k := 2)) => [|x].
    by apply: measurable_funM; exact: measurable_mxentry.
  rewrite mul1r normrM expr2.
  have h : `|x 0 ii.1| * `|x 0 ii.2| <= `|x| * `|x|.
    by rewrite ler_pM // mx_norm_entry_le.
  by apply: (le_trans h); rewrite lerDr.
have E (x : 'rV[R]_n) : ((x *m A) 0 j * (x *m A) 0 l)%:E =
    (\sum_(ii : 'I_n * 'I_n)
      (A ii.1 j * A ii.2 l)%:E * (x 0 ii.1 * x 0 ii.2)%:E)%E.
  rewrite sumEFin; congr (_%:E).
  rewrite -(pair_bigA _ (fun i i' => A i j * A i' l * (x 0 i * x 0 i'))) /=.
  rewrite !mxE mulr_suml; apply: eq_bigr => i _.
  by rewrite mulr_sumr; apply: eq_bigr => i' _; rewrite mulrACA mulrC.
under eq_integral do rewrite E.
rewrite integral_sum //.
  by move=> ii; exact: (integrableZl measurableT _ (ixx ii)).
under eq_bigr do rewrite integralZl // gauss_cov.
rewrite sumEFin; congr (_%:E).
rewrite -(pair_bigA _ (fun i i' => A i j * A i' l * (i == i')%:R)) /= mxE.
apply: eq_bigr => i _; rewrite (bigD1 i) //= eqxx mulr1 big1 ?addr0 ?mxE //.
by move=> i' /negbTE; rewrite eq_sym => ->; rewrite mulr0.
Qed.

End gauss_moments.
