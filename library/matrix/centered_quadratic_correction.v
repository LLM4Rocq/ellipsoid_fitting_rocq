From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import reals ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean opnorm nuclear.
From GaussianAnalysis.matrix Require Import centered_correction.

(**md**************************************************************************)
(* # The quadratic contribution of a centered linear correction              *)
(*                                                                            *)
(* The columns and sample rows follow centered_correction.v. The coefficient *)
(* adjoint is the existing coef_adj of nuclear.v; column coefficients t are  *)
(* passed to it as t^T. No second adjoint definition is introduced.           *)
(*                                                                            *)
(* ```                                                                        *)
(* reserve_feature H i == (row i H)^T (row i H) - I                           *)
(* reserve_mean H == (1/k) H^T 1                                             *)
(* reserve_quadratic H b == sum_i r_i (row i H)^T (row i H),                  *)
(*                         where r = centered_correction H b                 *)
(* reserve_linearized_quadratic H b == (1/k) sum_i (H b)_i B_i,              *)
(*                                   where B_i = reserve_feature H i         *)
(* ```                                                                        *)
(*                                                                            *)
(* The exact decomposition needs k > 0 only. Its norm bound assumes an       *)
(* explicit Frobenius bound on coef_adj; probabilistic estimates of this     *)
(* bound, or independence of the rows, are outside this module.              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section adjoint_algebra.
Variables (R : realType) (k d : nat) (B : 'I_k -> 'M[R]_d).

Lemma coef_adjD (u v : 'rV[R]_k) :
  coef_adj B (u + v) = coef_adj B u + coef_adj B v.
Proof.
rewrite /coef_adj -big_split /=; apply: eq_bigr => i _.
by rewrite mxE scalerDl.
Qed.

Lemma coef_adjB (u v : 'rV[R]_k) :
  coef_adj B (u - v) = coef_adj B u - coef_adj B v.
Proof.
rewrite /coef_adj -sumrB; apply: eq_bigr => i _.
by rewrite !mxE scalerBl.
Qed.

Lemma coef_adjZ (a : R) (u : 'rV[R]_k) :
  coef_adj B (a *: u) = a *: coef_adj B u.
Proof.
rewrite /coef_adj scaler_sumr; apply: eq_bigr => i _.
by rewrite mxE scalerA.
Qed.

Lemma coef_adj_ones :
  coef_adj B (centering_ones k)^T = \sum_i B i.
Proof.
by apply: eq_bigr => i _; rewrite /centering_ones !mxE scale1r.
Qed.

Lemma coef_adj_shift (E : 'M[R]_d) (u : 'rV[R]_k) :
  coef_adj (fun i => B i - E) u =
    coef_adj B u - (\sum_i u 0 i) *: E.
Proof.
rewrite /coef_adj.
under eq_bigr do rewrite scalerBr.
by rewrite sumrB -scaler_suml.
Qed.

End adjoint_algebra.

Section definitions.
Variable R : realType.

Definition reserve_feature k d (H : 'M[R]_(k, d)) (i : 'I_k) :=
  (row i H)^T *m row i H - 1%:M.

Definition reserve_mean k d (H : 'M[R]_(k, d)) : 'cV[R]_d :=
  k%:R^-1 *: (H^T *m centering_ones k).

Definition reserve_quadratic k d (H : 'M[R]_(k, d)) (b : 'cV[R]_d) :=
  coef_adj (fun i => (row i H)^T *m row i H)
    (centered_correction H b)^T.

Definition reserve_linearized_quadratic k d (H : 'M[R]_(k, d))
    (b : 'cV[R]_d) :=
  k%:R^-1 *: coef_adj (reserve_feature H) (H *m b)^T.

End definitions.

Section decomposition.
Variables (R : realType) (k d : nat) (H : 'M[R]_(k, d)).

Lemma centered_correction_mean (b : 'cV[R]_d) :
  centered_correction H b = H *m centered_potential H b -
    mxdot (reserve_mean H) (centered_potential H b) *: centering_ones k.
Proof.
rewrite /centered_correction /centering_mx mulmxBl mul1mx mulmxBl
  -!scalemxAl -!mulmxA.
rewrite [((centering_ones k)^T *m _)]mx11_scalar
  -mxdot_colE mul_mx_scalar scalerA.
rewrite /reserve_mean mxdotZl mxdot_mulmxl trmxK.
by rewrite mulrC.
Qed.

Lemma reserve_quadratic_centered (b : 'cV[R]_d) : (0 < k)%N ->
  reserve_quadratic H b =
    coef_adj (reserve_feature H) (centered_correction H b)^T.
Proof.
move=> k0; rewrite /reserve_feature coef_adj_shift /reserve_quadratic.
have sum0 : \sum_i (centered_correction H b)^T 0 i = 0.
  have e : (\sum_i (centered_correction H b)^T 0 i) =
      \sum_i centered_correction H b i 0.
    by apply: eq_bigr => i _; rewrite mxE.
  by rewrite e centered_correction_sum.
by rewrite sum0 scale0r subr0.
Qed.

Theorem reserve_quadratic_decomposition (b : 'cV[R]_d) : (0 < k)%N ->
  reserve_quadratic H b = reserve_linearized_quadratic H b +
    coef_adj (reserve_feature H)
      (H *m (centered_potential H b - k%:R^-1 *: b))^T -
    mxdot (reserve_mean H) (centered_potential H b) *:
      (\sum_i reserve_feature H i).
Proof.
move=> k0; rewrite reserve_quadratic_centered // centered_correction_mean.
rewrite linearB /= linearZ /= coef_adjB coef_adjZ coef_adj_ones.
congr (_ - _).
rewrite /reserve_linearized_quadratic mulmxBr -scalemxAr linearB /=
  linearZ /= coef_adjB coef_adjZ.
by rewrite addrCA subrr addr0.
Qed.

Theorem reserve_quadratic_error_bound (b : 'cV[R]_d) (L : R) :
  (0 < k)%N -> 0 <= L ->
  (forall t : 'rV[R]_k,
    frobenius (coef_adj (reserve_feature H) t) <= L * frobenius t) ->
  opnorm (reserve_quadratic H b - reserve_linearized_quadratic H b) <=
    L * opnorm H * frobenius (centered_potential H b - k%:R^-1 *: b) +
    frobenius (reserve_mean H) * frobenius (centered_potential H b) *
      opnorm (\sum_i reserve_feature H i).
Proof.
move=> k0 L0 adj.
rewrite reserve_quadratic_decomposition //.
have cancel (X Y Z : 'M[R]_d) : X + Y - Z - X = Y - Z.
  by rewrite addrAC [X + Y - X]addrAC subrr add0r.
rewrite cancel.
apply: le_trans (opnormD _ _) _; rewrite opnormN opnormZ.
apply: lerD.
- apply: le_trans (opnorm_le_frobenius _) _.
  apply: le_trans (adj _) _; rewrite frobenius_trmx.
  rewrite -mulrA ler_wpM2l //.
  exact: frobenius_mulmx_opnorm.
- by rewrite ler_wpM2r ?opnorm_ge0 //; exact: mxdot_le.
Qed.

End decomposition.

Section example.
Variable R : realType.

(* For two opposite observations in dimension one, the correction changes
   the linear moment but its entire quadratic contribution vanishes. *)
Example two_rows_quadratic_correction_zero (b : 'cV[R]_1) :
  let H : 'M[R]_(2, 1) := \col_i (if i == 0 then 1 else -1) in
  reserve_quadratic H b = 0.
Proof.
move=> H.
have feature0 (i : 'I_2) : reserve_feature H i = 0.
  apply/matrixP => j l; rewrite !ord1 /reserve_feature /H.
  rewrite !mxE big_ord1 !mxE eqxx /=.
  by case: ifP => _; ring.
rewrite reserve_quadratic_centered // /coef_adj.
by apply: big1 => i _; rewrite feature0 scaler0.
Qed.

End example.
