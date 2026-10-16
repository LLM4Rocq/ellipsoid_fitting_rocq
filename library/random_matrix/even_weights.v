From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral measurable_realfun probability.
From mathcomp Require Import ring_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.convex Require Import image_projection.
From GaussianAnalysis.probability Require Import symmetrization.
From GaussianAnalysis.random_matrix Require Import symmetric_reserve.

(* The weighted first moment of a row-sign invariant sample. The weights
   may depend on every row, but must be unchanged by each independent row
   sign. Sign averaging removes the cross terms without imposing moments
   on the sample law. Source: the main-sample certificate argument in
   doc/shifted-gaussian.tex. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section finite_signs.
Context {R : realType} {k m n : nat}.

Lemma rademacher_mean_frobenius_sum (A : 'I_k -> 'M[R]_(m,n)) :
  rademacher_mean (fun s : k.-tuple bool =>
    frobenius (\sum_i rademacher (tnth s i) *: A i)^+2) =
  \sum_i frobenius (A i)^+2.
Proof.
have e s : frobenius (\sum_i rademacher (tnth s i) *: A i)^+2 =
    \sum_(a < m) \sum_(b < n)
      (\sum_(i < k) A i a b * rademacher (tnth s i))^+2.
  rewrite frobenius_sqr /mxdot.
  apply: eq_bigr => a _; apply: eq_bigr => b _.
  rewrite -expr2 summxE; congr (_ ^+ 2).
  by apply: eq_bigr => i _; rewrite mxE mulrC.
under eq_fun do rewrite e.
rewrite rademacher_mean_sum.
under eq_bigr do rewrite rademacher_mean_sum.
under eq_bigr do under eq_bigr do rewrite rademacher_mean_sqr_sum.
under eq_bigr do rewrite exchange_big.
rewrite exchange_big; apply: eq_bigr => i _.
rewrite frobenius_sqr /mxdot.
by apply: eq_bigr => a _; apply: eq_bigr => b _; rewrite expr2.
Qed.
End finite_signs.

Section weighted_moment.
Context {R : realType} {k d : nat}.

Definition weighted_row_moment (H : 'M[R]_(k,d)) (w : 'rV[R]_k) := H^T *m w^T.

Lemma weighted_row_moment_sign (H : 'M[R]_(k,d)) (w : 'rV[R]_k)
    (s : k.-tuple bool) :
  weighted_row_moment (reserve_row_sign s H) w =
    \sum_i rademacher (tnth s i) *: (w 0 i *: (row i H)^T).
Proof.
apply/matrixP => a b; rewrite ord1 /weighted_row_moment mxE summxE.
apply: eq_bigr => i _.
by rewrite /reserve_row_sign !mxE; ring.
Qed.

Lemma weighted_row_moment_sign_second (H : 'M[R]_(k,d)) (w : 'rV[R]_k) :
  rademacher_mean (fun s : k.-tuple bool =>
    frobenius (weighted_row_moment (reserve_row_sign s H) w)^+2) =
  \sum_i (w 0 i)^+2 * frobenius (row i H)^+2.
Proof.
under eq_fun do rewrite weighted_row_moment_sign.
rewrite rademacher_mean_frobenius_sum; apply: eq_bigr => i _.
by rewrite frobeniusZ frobenius_trmx exprMn -normrX ger0_norm ?sqr_ge0.
Qed.

Lemma weighted_row_moment_sign_bound (H : 'M[R]_(k,d)) (w : 'rV[R]_k) (M : R) :
  0 <= M -> frobenius w <= 1 ->
  (forall i, frobenius (row i H)^+2 <= M) ->
  rademacher_mean (fun s : k.-tuple bool =>
    frobenius (weighted_row_moment (reserve_row_sign s H) w)^+2) <= M.
Proof.
move=> M0 w1 rows; rewrite weighted_row_moment_sign_second.
apply: le_trans (_ : M * frobenius w ^+ 2 <= M).
  rewrite frobenius_sqr /mxdot big_ord1 mulr_sumr.
  apply: ler_sum => i _; rewrite -expr2 mulrC.
  by apply: ler_wpM2r; [exact: sqr_ge0 | exact: rows].
rewrite -[leRHS]mulr1; apply: ler_wpM2l => //.
by rewrite -[leRHS](@expr1n R 2) lerXn2r ?nnegrE ?frobenius_ge0.
Qed.
End weighted_moment.

Section random_weights.
Context {R : realType} {k d : nat}.
Variable Q : probability 'M[R]_(k,d) R.
Variable w : 'M[R]_(k,d) -> 'rV[R]_k.
Hypothesis mw : measurable_fun setT w.
Hypothesis evenw : forall s H, w (reserve_row_sign s H) = w H.
Hypothesis w1 : forall H, frobenius (w H) <= 1.

Lemma measurable_weighted_row_moment :
  measurable_fun setT (fun H => weighted_row_moment H (w H)).
Proof.
apply: measurable_mulmx.
- exact: measurable_trmx.
- apply/measurable_fun_mxP => i j.
  under eq_fun do rewrite mxE.
  have /measurable_fun_mxP mw' := mw.
  exact: mw'.
Qed.

Theorem even_weights_moment_tail (E : set 'M[R]_(k,d)) (M t : R) :
  reserve_sign_invariant Q -> measurable E -> 0 <= M -> 0 < t ->
  (forall H, E H -> forall i, frobenius (row i H)^+2 <= M) ->
  (Q [set H | (t < frobenius (weighted_row_moment H (w H))^+2)%R] <=
    Q (~` E) + (M/t)%:E)%E.
Proof.
move=> symQ mE M0 t0 rows.
apply: reserve_sign_average_tail => //.
- apply: measurable_funX; apply: measurable_frobenius_fun.
  exact: measurable_weighted_row_moment.
- by move=> H; exact: sqr_ge0.
- move=> H EH.
  under eq_fun do rewrite evenw.
  exact: weighted_row_moment_sign_bound M0 (w1 H) (rows H EH).
Qed.
End random_weights.

Section example.
Variable R : realType.

(* The cross terms vanish even for two identical observations. *)
Example two_equal_rows_sign_second (v : 'rV[R]_1) :
  rademacher_mean (fun s : 2.-tuple bool =>
    frobenius (\sum_(i < 2) rademacher (tnth s i) *: v)^+2) =
  2 * frobenius v^+2.
Proof.
rewrite rademacher_mean_frobenius_sum big_ord_recr big_ord1 /=.
ring.
Qed.
End example.
