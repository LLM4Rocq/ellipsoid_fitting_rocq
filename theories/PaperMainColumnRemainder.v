(* Exact column-power splitting for the non-backtracking recurrence error. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainSquarefreeEdgeLower.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Definition pmcr_rankone N (C : finType) (X : 'I_N -> C -> R) c : 'M[R]_N :=
  \matrix_(i,j) (X i c * X j c).
Definition pmcr_diagonal N (C : finType) (X : 'I_N -> C -> R) c : 'M[R]_N :=
  diag_mx (\row_i (X i c)^+2).
Definition pmcr_column_norm N (C : finType) (X : 'I_N -> C -> R) c : R :=
  \sum_(i<N) (X i c)^+2.

Lemma pmcr_column_split N (C : finType) (X : 'I_N -> C -> R) kap c :
  pmlo_P N C X kap c = kap *: (pmcr_rankone N C X c-pmcr_diagonal N C X c).
Proof.
apply/matrixP=>i j; rewrite /pmlo_P /pmcr_rankone /pmcr_diagonal !mxE.
case: eqP=> [->|Hij]; first by rewrite mulr1n expr2 subrr mulr0.
by rewrite mulr0n subr0.
Qed.

Lemma pmcr_rankone_square N (C : finType) (X : 'I_N -> C -> R) c :
  pmcr_rankone N C X c *m pmcr_rankone N C X c =
  pmcr_column_norm N C X c *: pmcr_rankone N C X c.
Proof.
apply/matrixP=>i j; rewrite /pmcr_rankone /pmcr_column_norm !mxE mulr_suml.
apply: eq_bigr=>k _; rewrite !mxE; ring.
Qed.

Lemma pmcr_rankone_power N (C : finType) (X : 'I_N -> C -> R) c k :
  (pmcr_rankone N C X c)^+k.+1 = (pmcr_column_norm N C X c)^+k *: pmcr_rankone N C X c.
Proof.
elim: k=>[|k IH]; first by rewrite expr1 expr0 scale1r.
rewrite exprS -mulmxE IH -scalemxAr pmcr_rankone_square scalerA exprS.
by rewrite mulrC.
Qed.

Lemma pmcr_scaled_power n (A : 'M[R]_n) a k :
  (a *: A)^+k = a^+k *: A^+k.
Proof.
elim: k=>[|k IH]; first by rewrite !expr0 scale1r.
rewrite !exprS -!mulmxE IH -scalemxAl -scalemxAr scalerA.
by [].
Qed.

Lemma pmcr_first_sum N (C : finType) (X : 'I_N -> C -> R) kap :
  pmlo_T N C X kap 1 = kap *: (\sum_c pmcr_rankone N C X c)-kap *: (\sum_c pmcr_diagonal N C X c).
Proof.
rewrite pmlo_T1.
under eq_bigr do rewrite pmcr_column_split.
by rewrite -scaler_sumr sumrB scalerBr.
Qed.

Lemma pmcr_power_sum N (C : finType) (X : 'I_N -> C -> R) kap k :
  pmlo_S N C X kap k = kap^+k *: (\sum_c (pmcr_rankone N C X c-pmcr_diagonal N C X c)^+k).
Proof.
rewrite /pmlo_S.
under eq_bigr do rewrite pmcr_column_split pmcr_scaled_power.
by rewrite scaler_sumr.
Qed.

Theorem paper_main_column_remainder_split N (C : finType) (X : 'I_N -> C -> R) kap s k :
  s = kap*N%:R ->
  pmlo_E N C X kap s k =
    kap^+k.+2 *: (\sum_c ((pmcr_rankone N C X c-pmcr_diagonal N C X c)^+k.+2-
      (pmcr_rankone N C X c)^+k.+2)) +
    kap^+k.+2 *: (\sum_c (((pmcr_column_norm N C X c)^+k.+1-N%:R^+k.+1) *: pmcr_rankone N C X c)) +
    s^+k *: ((kap^+2*N%:R) *: (\sum_c pmcr_diagonal N C X c)-1%:M).
Proof.
move=> Hs.
have EP : (\sum_c ((pmcr_rankone N C X c-pmcr_diagonal N C X c)^+k.+2-
    (pmcr_rankone N C X c)^+k.+2)) =
  (\sum_c (pmcr_rankone N C X c-pmcr_diagonal N C X c)^+k.+2)-
  (\sum_c (pmcr_column_norm N C X c)^+k.+1 *: pmcr_rankone N C X c).
{ rewrite sumrB; congr (_-_); apply: eq_bigr=>c _; exact: pmcr_rankone_power. }
have EC : (\sum_c (((pmcr_column_norm N C X c)^+k.+1-N%:R^+k.+1) *: pmcr_rankone N C X c)) =
  (\sum_c (pmcr_column_norm N C X c)^+k.+1 *: pmcr_rankone N C X c)-
  N%:R^+k.+1 *: (\sum_c pmcr_rankone N C X c).
{ under eq_bigr do rewrite scalerBl.
  by rewrite sumrB scaler_sumr. }
rewrite /pmlo_E pmcr_power_sum pmcr_first_sum EP EC !scalerBr !scalerA.
have Hcoef : kap^+k.+2*N%:R^+k.+1 = s^+k.+1*kap.
{ rewrite Hs exprMn !exprS; ring. }
have Hcoef2 : s^+k*(kap^+2*N%:R) = s^+k.+1*kap.
{ rewrite Hs !exprS; ring. }
rewrite Hcoef Hcoef2.
apply/matrixP=>i j; rewrite !mxE; ring.
Qed.
