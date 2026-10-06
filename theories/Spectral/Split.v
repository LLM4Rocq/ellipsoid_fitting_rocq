(* The fixed spectral cutoff as commuting positive head and bulk matrices. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.HeadFrobenius Spectral.SymmetricDiagonalization
  Spectral.Cutoff Spectral.OrthogonalBounds Cone.ConditionOperator.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Definition paper_main_spectral_matrix {d} (O : 'M[R]_d) (a : 'rV[R]_d) :=
  O^T *m diag_mx a *m O.
Definition paper_main_spectral_head {d} (O : 'M[R]_d) (a : 'rV[R]_d) eps :=
  paper_main_spectral_matrix O (paper_main_spectral_head_coeff a eps).
Definition paper_main_spectral_bulk {d} (O : 'M[R]_d) (a : 'rV[R]_d) eps :=
  paper_main_spectral_matrix O (paper_main_spectral_bulk_coeff a eps).
Definition paper_main_spectral_projection {d} (O : 'M[R]_d) (a : 'rV[R]_d) eps :=
  paper_main_spectral_matrix O (paper_main_spectral_mask a eps).

Section Split.
Variable d : nat.
Implicit Types (O : 'M[R]_d) (a b : 'rV[R]_d).

Lemma paper_main_diagonal_add a b : diag_mx (a+b) = diag_mx a+diag_mx b.
Proof. by apply/matrixP=> i j; rewrite !mxE mulrnDl. Qed.

Lemma paper_main_diagonal_mul a b :
  diag_mx a *m diag_mx b = diag_mx (\row_i (a 0 i*b 0 i)).
Proof.
apply/matrixP=>i j; rewrite mxE (bigD1 i) //= big1.
- by move=> k Hk; rewrite [diag_mx a i k]mxE eq_sym (negbTE Hk) mulr0n mul0r.
- rewrite !mxE eqxx mulr1n addr0; case: (i==j); by rewrite ?mulr1n ?mulr0n ?mulr0.
Qed.

Lemma paper_main_spectral_matrix_add O a b :
  paper_main_spectral_matrix O (a+b) = paper_main_spectral_matrix O a+paper_main_spectral_matrix O b.
Proof. by rewrite /paper_main_spectral_matrix paper_main_diagonal_add mulmxDr mulmxDl. Qed.

Lemma paper_main_spectral_matrix_mul O a b : O^T *m O = 1%:M ->
  paper_main_spectral_matrix O a *m paper_main_spectral_matrix O b =
  paper_main_spectral_matrix O (\row_i (a 0 i*b 0 i)).
Proof.
move=> HO; have HT := paper_main_symmetric_orthogonal_tr d O HO.
by rewrite /paper_main_spectral_matrix -!mulmxA (mulmxA O) HT mul1mx !mulmxA -(mulmxA O^T (diag_mx a) (diag_mx b)) paper_main_diagonal_mul.
Qed.

Lemma paper_main_spectral_matrix_symmetric O a : (paper_main_spectral_matrix O a)^T = paper_main_spectral_matrix O a.
Proof. by rewrite /paper_main_spectral_matrix !trmx_mul trmxK tr_diag_mx mulmxA. Qed.

Theorem paper_main_spectral_split O a eps :
  paper_main_spectral_head O a eps+paper_main_spectral_bulk O a eps = paper_main_spectral_matrix O a.
Proof.
by rewrite /paper_main_spectral_head /paper_main_spectral_bulk -paper_main_spectral_matrix_add paper_main_spectral_coeff_split.
Qed.

Theorem paper_main_spectral_projection_square O a eps : O^T *m O = 1%:M ->
  paper_main_spectral_projection O a eps *m paper_main_spectral_projection O a eps = paper_main_spectral_projection O a eps.
Proof.
move=> HO; rewrite /paper_main_spectral_projection paper_main_spectral_matrix_mul //.
congr (paper_main_spectral_matrix O _); apply/matrixP=>i j; have -> : i = 0 by apply: ord1.
by rewrite /paper_main_spectral_mask !mxE; case: ifP=>_; rewrite ?mulr1 ?mulr0.
Qed.

Theorem paper_main_spectral_projection_commutes O a eps : O^T *m O = 1%:M ->
  paper_main_spectral_projection O a eps *m paper_main_spectral_matrix O a =
  paper_main_spectral_matrix O a *m paper_main_spectral_projection O a eps.
Proof.
move=> HO; rewrite /paper_main_spectral_projection !paper_main_spectral_matrix_mul //.
congr (paper_main_spectral_matrix O _); apply/matrixP=>i j; by rewrite !mxE mulrC.
Qed.

Theorem paper_main_spectral_head_supported O a eps : O^T *m O = 1%:M ->
  paper_main_spectral_projection O a eps *m paper_main_spectral_head O a eps *m paper_main_spectral_projection O a eps =
  paper_main_spectral_head O a eps.
Proof.
move=> HO; rewrite /paper_main_spectral_projection /paper_main_spectral_head !paper_main_spectral_matrix_mul //.
congr (paper_main_spectral_matrix O _); apply/matrixP=>i j; have -> : i = 0 by apply: ord1.
by rewrite /paper_main_spectral_mask /paper_main_spectral_head_coeff !mxE; case: ifP=>_; rewrite ?mul1r ?mulr1 ?mul0r ?mulr0.
Qed.

Theorem paper_main_spectral_positive_bounds O a eps : O^T *m O = 1%:M ->
  (forall i, 0<=a 0 i) -> 0<=eps ->
  paper_main_psd (paper_main_spectral_head O a eps) /\
  paper_main_psd (paper_main_spectral_bulk O a eps) /\
  paper_main_cone_opnorm_le (paper_main_spectral_bulk O a eps) eps.
Proof.
move=> HO Ha He; have HB := paper_main_spectral_bulk_bounds d a eps Ha He.
split.
- apply: paper_main_psd_congruence; apply: paper_main_diagonal_psd=>i; exact: (HB i).1.
split.
- apply: paper_main_psd_congruence; apply: paper_main_diagonal_psd=>i; exact: (andP (HB i).2).1.
- apply: paper_main_orthogonal_congruence_opnorm=> //.
  apply: paper_main_diagonal_opnorm=> // i.
  have /andP [H0 H1] := (HB i).2; by rewrite ger0_norm.
Qed.

Theorem paper_main_spectral_head_frobenius O a eps : O^T *m O = 1%:M ->
  paper_main_frobenius (paper_main_spectral_head O a eps)<=paper_main_frobenius (paper_main_spectral_matrix O a).
Proof.
move=> HO.
have H : paper_main_frobenius (paper_main_spectral_head O a eps)^+2<=paper_main_frobenius (paper_main_spectral_matrix O a)^+2.
  rewrite !pmh_frobenius_sqr.
  rewrite (paper_main_symmetric_frobenius_diagonal d _ O _ HO erefl).
  rewrite (paper_main_symmetric_frobenius_diagonal d _ O _ HO erefl).
  apply: ler_sum=>i _; rewrite /paper_main_spectral_head_coeff mxE.
  by case: ifP=>_; rewrite ?expr0n //; exact: sqr_ge0.
by move: H; rewrite ler_sqr ?nnegrE ?pmh_frobenius_ge0.
Qed.
End Split.
