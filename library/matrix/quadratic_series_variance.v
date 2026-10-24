From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear reals arithmetic_tactic ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm nuclear.
From GaussianAnalysis.matrix Require Import psd_part psd_splitting.

(**md**************************************************************************)
(* # Variance of a quadratic matrix series                                   *)
(*                                                                            *)
(* A Frobenius bound on the coefficient adjoint of B_j = u_j u_j^T - I      *)
(* controls fourth moments of all linear forms of the finite column family  *)
(* u. The bounds are homogeneous, so they include zero vectors and zero     *)
(* coordinate dimension. No random variables or independence are involved.   *)
(*                                                                            *)
(* ```                                                                        *)
(* quadratic_series_feature u j == u j (u j)^T - I                           *)
(* quadratic_fourth_constant k L == 2 L^2 + 2 k                              *)
(* quadratic_series_variance u b == sum_j <u j,b>^2 B_j^2                    *)
(* ```                                                                        *)
(*                                                                            *)
(* The variance bound has constant M F + sqrt(k F), with F = 2 L^2 + 2 k,   *)
(* when every ||u j||^2 <= M and ||coef_adj B t||_F <= L ||t||.              *)
(* Source: the reserve-correction proof of doc/shifted-gaussian.tex. The     *)
(* moment inequalities here are homogeneous, including zero directions.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section dual_bound.
Variables (R : realType) (k d : nat) (B : 'I_k -> 'M[R]_d).

Lemma coef_map_bound (L : R) : 0 <= L ->
  (forall t, frobenius (coef_adj B t) <= L * frobenius t) ->
  forall D, frobenius (coef_map B D) <= L * frobenius D.
Proof.
move=> L0 adj D.
have h : frobenius (coef_map B D) ^+ 2 <=
    L * frobenius (coef_map B D) * frobenius D.
  rewrite frobenius_sqr mxdot_coef_map.
  apply: le_trans (ler_mxdot _ _) _.
  by rewrite ler_wpM2r ?frobenius_ge0.
have [->|map0] := eqVneq (frobenius (coef_map B D)) 0.
  by rewrite mulr_ge0 ?frobenius_ge0.
have mapp : 0 < frobenius (coef_map B D).
  by rewrite lt_def map0 frobenius_ge0.
by move: h; rewrite expr2 [L * _]mulrC -mulrA ler_pM2l.
Qed.

Lemma coef_map_sqr_bound (L : R) : 0 <= L ->
  (forall t, frobenius (coef_adj B t) <= L * frobenius t) ->
  forall D, mxdot (coef_map B D) (coef_map B D) <= L ^+ 2 * mxdot D D.
Proof.
move=> L0 adj D.
have h := coef_map_bound L0 adj D.
rewrite -!frobenius_sqr -exprMn.
by rewrite lerXn2r ?nnegrE ?frobenius_ge0 ?mulr_ge0 ?frobenius_ge0.
Qed.

End dual_bound.

Section definitions.
Variable R : realType.

Definition quadratic_series_feature k d (u : 'I_k -> 'cV[R]_d) j :=
  u j *m (u j)^T - 1%:M.

Definition quadratic_fourth_constant k (L : R) := 2 * L ^+ 2 + 2 * k%:R.

Definition quadratic_series_variance k d (u : 'I_k -> 'cV[R]_d)
    (b : 'cV[R]_d) :=
  \sum_j (mxdot (u j) b) ^+ 2 *:
    (quadratic_series_feature u j *m quadratic_series_feature u j).

End definitions.

Section fourth_moments.
Variables (R : realType) (k d : nat) (u : 'I_k -> 'cV[R]_d).
Variable L : R.
Hypothesis L0 : 0 <= L.
Hypothesis adj : forall t,
  frobenius (coef_adj (quadratic_series_feature u) t) <= L * frobenius t.

Lemma quadratic_fourth_constant_ge0 : 0 <= quadratic_fourth_constant k L.
Proof.
have two0 : 0 <= (2 : R) by rewrite ler0n.
have k0 : 0 <= (k%:R : R) by rewrite ler0n.
exact: addr_ge0 (mulr_ge0 two0 (sqr_ge0 L)) (mulr_ge0 two0 k0).
Qed.

Lemma quadratic_series_pairing j (z : 'cV[R]_d) :
  mxdot (quadratic_series_feature u j) (z *m z^T) =
    (mxdot (u j) z) ^+ 2 - mxdot z z.
Proof.
by rewrite /quadratic_series_feature mxdotBl mxdot_outer2 -expr2
  mxdot_outer mulmx1 -mxdot_colE.
Qed.

Lemma quadratic_deviations_bound (z : 'cV[R]_d) :
  \sum_j ((mxdot (u j) z) ^+ 2 - mxdot z z) ^+ 2 <=
    L ^+ 2 * (mxdot z z) ^+ 2.
Proof.
have h := coef_map_sqr_bound L0 adj (z *m z^T).
rewrite mxdot_outer2 -expr2 in h.
have e : mxdot (coef_map (quadratic_series_feature u) (z *m z^T))
    (coef_map (quadratic_series_feature u) (z *m z^T)) =
    \sum_j ((mxdot (u j) z) ^+ 2 - mxdot z z) ^+ 2.
  rewrite /mxdot big_ord1; apply: eq_bigr => j _.
  by rewrite /coef_map !mxE quadratic_series_pairing expr2.
by rewrite -e.
Qed.

Theorem quadratic_fourth_moment_bound (z : 'cV[R]_d) :
  \sum_j (mxdot (u j) z) ^+ 4 <=
    quadratic_fourth_constant k L * frobenius z ^+ 4.
Proof.
have h := quadratic_deviations_bound z.
have point j : (mxdot (u j) z) ^+ 4 <=
    2 * ((mxdot (u j) z) ^+ 2 - mxdot z z) ^+ 2 +
    2 * (mxdot z z) ^+ 2.
  have := sqr_ge0 ((mxdot (u j) z) ^+ 2 - 2 * mxdot z z).
  by nra.
have summed : (\sum_j (mxdot (u j) z) ^+ 4) <=
    \sum_j (2 * ((mxdot (u j) z) ^+ 2 - mxdot z z) ^+ 2 +
      2 * (mxdot z z) ^+ 2).
  by apply: ler_sum => j _; exact: point.
apply: le_trans summed _.
rewrite big_split /= -mulr_sumr sumr_const card_ord -mulr_natl.
have e4 : frobenius z ^+ 4 = (mxdot z z) ^+ 2.
  by rewrite -frobenius_sqr -exprM.
rewrite /quadratic_fourth_constant e4 mulrDl.
have two0 : 0 <= (2 : R) by rewrite ler0n.
have h2 := ler_wpM2l two0 h.
by nra.
Qed.

Corollary quadratic_fourth_unit_bound (z : 'cV[R]_d) :
  frobenius z = 1 -> \sum_j (mxdot (u j) z) ^+ 4 <=
    quadratic_fourth_constant k L.
Proof. by move=> z1; have := quadratic_fourth_moment_bound z; rewrite z1 expr1n mulr1. Qed.

Theorem quadratic_mixed_fourth_bound (b z : 'cV[R]_d) :
  \sum_j (mxdot (u j) b) ^+ 2 * (mxdot (u j) z) ^+ 2 <=
    quadratic_fourth_constant k L * frobenius b ^+ 2 * frobenius z ^+ 2.
Proof.
have sum0 (x : 'cV[R]_d) : 0 <= \sum_j (mxdot (u j) x) ^+ 4.
  by apply: sumr_ge0 => j _; rewrite exprn_even_ge0.
have mixed0 : 0 <= \sum_j (mxdot (u j) b) ^+ 2 * (mxdot (u j) z) ^+ 2.
  by apply: sumr_ge0 => j _; rewrite mulr_ge0 ?sqr_ge0.
have F0 := quadratic_fourth_constant_ge0.
have rhs0 : 0 <= quadratic_fourth_constant k L * frobenius b ^+ 2 * frobenius z ^+ 2.
  exact: mulr_ge0 (mulr_ge0 F0 (sqr_ge0 _)) (sqr_ge0 _).
rewrite -ler_sqr ?nnegrE //.
have cs := sum_cauchy_schwarz
  (fun j => (mxdot (u j) b) ^+ 2) (fun j => (mxdot (u j) z) ^+ 2).
have squares (f : 'I_k -> R) : \sum_j f j ^+ 2 * f j ^+ 2 = \sum_j f j ^+ 4.
  by apply: eq_bigr => j _; rewrite -expr2 -exprM.
rewrite !squares in cs.
apply: le_trans cs _.
have prod := ler_pM (sum0 b) (sum0 z)
  (quadratic_fourth_moment_bound b) (quadratic_fourth_moment_bound z).
have e : (quadratic_fourth_constant k L * frobenius b ^+ 4) *
    (quadratic_fourth_constant k L * frobenius z ^+ 4) =
    (quadratic_fourth_constant k L * frobenius b ^+ 2 * frobenius z ^+ 2) ^+ 2.
  by ring.
by rewrite -e.
Qed.

Theorem quadratic_second_moment_bound (b : 'cV[R]_d) :
  \sum_j (mxdot (u j) b) ^+ 2 <=
    Num.sqrt (k%:R * quadratic_fourth_constant k L) * frobenius b ^+ 2.
Proof.
have cs := sum_cauchy_schwarz
  (fun j : 'I_k => (mxdot (u j) b) ^+ 2) (fun _ => (1 : R)).
have squares (f : 'I_k -> R) : \sum_j f j ^+ 2 * f j ^+ 2 = \sum_j f j ^+ 4.
  by apply: eq_bigr => j _; rewrite -expr2 -exprM.
have e1 : (\sum_j (mxdot (u j) b) ^+ 2 * 1) =
    \sum_j (mxdot (u j) b) ^+ 2.
  by apply: eq_bigr => j _; rewrite mulr1.
have c1 : (\sum_(j < k) (1 : R) * 1) = k%:R.
  by rewrite mulr1 sumr_const card_ord.
rewrite e1 squares c1 in cs.
have F0 := quadratic_fourth_constant_ge0.
have k0 : (0 : R) <= k%:R by rewrite ler0n.
have kF0 : 0 <= k%:R * quadratic_fourth_constant k L by rewrite mulr_ge0.
have sum0 : 0 <= \sum_j (mxdot (u j) b) ^+ 2.
  by apply: sumr_ge0 => j _; exact: sqr_ge0.
rewrite -ler_sqr ?nnegrE ?mulr_ge0 ?sqr_ge0 ?sqrtr_ge0 //.
rewrite exprMn sqr_sqrtr // -exprM.
apply: le_trans cs _.
have h := ler_wpM2r k0 (quadratic_fourth_moment_bound b).
by rewrite -mulrA [k%:R * _]mulrC.
Qed.

End fourth_moments.

Section matrix_variance.
Variables (R : realType) (k d : nat) (u : 'I_k -> 'cV[R]_d).

Lemma quadratic_feature_symmetric j :
  quadratic_series_feature u j \is symmetricmx.
Proof.
apply/symmetricmxP.
by rewrite /quadratic_series_feature linearB /= trmx_mul trmxK trmx1.
Qed.

Lemma quadratic_feature_action j (z : 'cV[R]_d) :
  quadratic_series_feature u j *m z = mxdot (u j) z *: u j - z.
Proof.
by rewrite /quadratic_series_feature mulmxBl mul1mx -mulmxA
  [(u j)^T *m z]mx11_scalar -mxdot_colE mul_mx_scalar.
Qed.

Lemma quadratic_feature_square_form j (z : 'cV[R]_d) :
  mxdot z (quadratic_series_feature u j *m quadratic_series_feature u j *m z) =
    mxdot (quadratic_series_feature u j *m z) (quadratic_series_feature u j *m z).
Proof.
by rewrite mxdot_mulmxl (symmetricmxP _ (quadratic_feature_symmetric j)) mulmxA.
Qed.

Lemma quadratic_feature_square_psd j :
  psdmx (quadratic_series_feature u j *m quadratic_series_feature u j).
Proof.
split.
  apply/symmetricmxP.
  by rewrite trmx_mul (symmetricmxP _ (quadratic_feature_symmetric j)).
by move=> z; rewrite quadratic_feature_square_form mxdot_ge0.
Qed.

Lemma quadratic_feature_square_expansion j (z : 'cV[R]_d) :
  mxdot z (quadratic_series_feature u j *m quadratic_series_feature u j *m z) =
    (frobenius (u j) ^+ 2 - 2) * (mxdot (u j) z) ^+ 2 + frobenius z ^+ 2.
Proof.
rewrite quadratic_feature_square_form quadratic_feature_action.
rewrite mxdotBl !mxdotBr !mxdotZl !mxdotZr (mxdotC z (u j)) !frobenius_sqr.
by ring.
Qed.

Lemma quadratic_series_variance_psd (b : 'cV[R]_d) :
  psdmx (quadratic_series_variance u b).
Proof.
apply: psdmx_sum => j _; apply: psdmxZ; first exact: sqr_ge0.
exact: quadratic_feature_square_psd.
Qed.

Theorem quadratic_series_variance_bound (L M : R) :
  0 <= L -> 0 <= M ->
  (forall t, frobenius (coef_adj (quadratic_series_feature u) t) <=
    L * frobenius t) ->
  (forall j, frobenius (u j) ^+ 2 <= M) ->
  forall b : 'cV[R]_d,
    opnorm (quadratic_series_variance u b) <=
      (M * quadratic_fourth_constant k L +
        Num.sqrt (k%:R * quadratic_fourth_constant k L)) * frobenius b ^+ 2.
Proof.
move=> L0 M0 adj row_bound b.
have F0 := @quadratic_fourth_constant_ge0 R k L.
have C0 : 0 <= (M * quadratic_fourth_constant k L +
    Num.sqrt (k%:R * quadratic_fourth_constant k L)) * frobenius b ^+ 2.
  exact: mulr_ge0 (addr_ge0 (mulr_ge0 M0 F0) (sqrtr_ge0 _)) (sqr_ge0 _).
have Vp := quadratic_series_variance_psd b.
apply/(opnorm_symP Vp.1 C0) => z.
rewrite (ger0_norm (Vp.2 z)) /quadratic_series_variance mulmx_suml mxdot_sumr.
have point j : (mxdot (u j) b) ^+ 2 *
    mxdot z (quadratic_series_feature u j *m quadratic_series_feature u j *m z) <=
    M * ((mxdot (u j) b) ^+ 2 * (mxdot (u j) z) ^+ 2) +
    frobenius z ^+ 2 * (mxdot (u j) b) ^+ 2.
  rewrite quadratic_feature_square_expansion.
  have h := row_bound j.
  have b0 := sqr_ge0 (mxdot (u j) b).
  have z0 := sqr_ge0 (mxdot (u j) z).
  have hmul := ler_wpM2r z0 h.
  have hmul2 := ler_wpM2r b0 hmul.
  by nra.
have step : (\sum_j mxdot z
    (((mxdot (u j) b) ^+ 2 *:
      (quadratic_series_feature u j *m quadratic_series_feature u j)) *m z)) <=
    \sum_j (M * ((mxdot (u j) b) ^+ 2 * (mxdot (u j) z) ^+ 2) +
      frobenius z ^+ 2 * (mxdot (u j) b) ^+ 2).
  apply: ler_sum => j _.
  by rewrite -scalemxAl mxdotZr; exact: point.
apply: le_trans step _.
rewrite big_split /= -!mulr_sumr -frobenius_sqr.
have mixed := quadratic_mixed_fourth_bound L0 adj b z.
have second := quadratic_second_moment_bound L0 adj b.
have h1 := ler_wpM2l M0 mixed.
have h2 := ler_wpM2l (sqr_ge0 (frobenius z)) second.
apply: le_trans (lerD h1 h2) _.
by nra.
Qed.

End matrix_variance.

Section example.
Variable R : realType.

(* One scalar observation u=2 has feature B=3, hence variance 36 b^2. *)
Example scalar_quadratic_variance (b : R) :
  quadratic_series_variance
    (fun _ : 'I_1 => (const_mx 2 : 'cV[R]_1)) (const_mx b) =
    (36 * b ^+ 2)%:M.
Proof.
rewrite /quadratic_series_variance big_ord1.
apply/matrixP => i j; rewrite !ord1 /quadratic_series_feature /mxdot.
by rewrite !big_ord1 !mxE !big_ord1 !mxE eqxx /= !big_ord1 !mxE /=; ring.
Qed.

End example.
