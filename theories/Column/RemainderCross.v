(* Operator norm bounds for the column powers in the error of the
   non-backtracking recurrence. Deterministic.

   For a family X : 'I_N -> C -> R with columns X_c, write R_c = X_c X_c^T
   (pmcr_rankone), D_c = diag(X_ic^2) (pmcr_diagonal) and
   Q_c = sum_i X_ic^2 (pmcr_column_norm).
   - pmcr_cross_opbound: if every Q_c <= U, every X_ic^2 <= m, every row sum
     sum_c X_ic^2 is at most U, sum_c R_c <= U I as quadratic forms,
     0 <= m <= b <= U and m U <= b^2, then for p >= 2 the operator norm of
     sum_c ((R_c - D_c)^p - R_c^p) is at most p (2 U)^(p - 1) b.
   - pmcr_cross_scaled: the same bound after scaling by kap^p.
   - pmcr_diagonal_sum and pmcr_diagonal_error: sum_c D_c is the diagonal
     matrix of the row sums, so if |a sum_c X_ic^2 - 1| <= delta for every
     row i, then a sum_c D_c - I has operator norm at most delta. *)
From Stdlib Require Import Reals List FunctionalExtensionality Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions
  Geometry.HeadCoefficients Geometry.HeadFrobenius Cone.ConditionOperator
  SquareFree.EdgeLower Spectral.OrthogonalBounds Column.Remainder
  Column.RemainderBounds SquareFree.MatrixFamilyCauchy
  SquareFree.MatrixFamilyCauchyPowers Column.RemainderPowers.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Theorem pmcr_cross_opbound N (C : finType) (X : 'I_N -> C -> R) U m b :
  0 <= U -> 0 <= m -> 0 <= b -> m <= b -> m <= U -> b <= U -> m*U <= b^+2 ->
  (forall c, pmcr_column_norm N C X c <= U) ->
  (forall i c, (X i c)^+2 <= m) ->
  (forall i, \sum_c (X i c)^+2 <= U) ->
  (forall u : 'cV[R]_N, (u^T *m (\sum_c pmcr_rankone N C X c) *m u) 0 0 <= U*(u^T *m u) 0 0) ->
  forall p, (2 <= p)%N ->
  pmlo_opb N (\sum_c ((pmcr_rankone N C X c-pmcr_diagonal N C X c)^+p-
    (pmcr_rankone N C X c)^+p)) (p%:R*(2*U)^+p.-1*b).
Proof.
move=>HU Hm Hb Hmb HmU HbU HmUb HQ HX HD HG p Hp.
have [Hc [ER [ED EA]]] := pmcr_column_base_bounds N C X U m b HU Hm Hb HmU HbU HmUb HQ HX HD HG.
have HU2 : U <= 2*U.
{ apply/RleP; move/RleP: HU=>HU.
  change (Rle R0 U) in HU.
  change (Rle U (Rmult (IZR 2) U)); Stdlib.micromega.Lra.lra. }
apply: (pmcr_power_sum_error C N (pmcr_rankone N C X) (pmcr_diagonal N C X) (2*U) m b)=>//.
- exact: pmcr_rankone_symmetric.
- exact: pmcr_diagonal_symmetric.
- by move=>c; have [_ [_ H]] := Hc c.
- move=>c; apply: (pmlo_opb_le N _ U _ (proj1 (Hc c))); exact: HU2.
- by move=>c; have [_ [H _]] := Hc c.
- exact: (pmcr_energy_bound_le C N _ U _ ER HU2).
Qed.

Theorem pmcr_cross_scaled N (C : finType) (X : 'I_N -> C -> R) U b kap p :
  0 <= kap ->
  pmlo_opb N (\sum_c ((pmcr_rankone N C X c-pmcr_diagonal N C X c)^+p-
    (pmcr_rankone N C X c)^+p)) (p%:R*(2*U)^+p.-1*b) ->
  pmlo_opb N (kap^+p *: (\sum_c ((pmcr_rankone N C X c-pmcr_diagonal N C X c)^+p-
    (pmcr_rankone N C X c)^+p))) (kap^+p*(p%:R*(2*U)^+p.-1*b)).
Proof.
move=>Hkap H; have HS := pmlo_opb_scale N _ _ (kap^+p) H.
by rewrite ger0_norm ?exprn_ge0 in HS.
Qed.

Lemma pmcr_diagonal_sum N (C : finType) (X : 'I_N -> C -> R) :
  (\sum_c pmcr_diagonal N C X c) = diag_mx (\row_i \sum_c (X i c)^+2).
Proof.
apply/matrixP=>i j; rewrite summxE !mxE.
under eq_bigr do rewrite /pmcr_diagonal !mxE.
by rewrite -sumrMnl.
Qed.

Theorem pmcr_diagonal_error N (C : finType) (X : 'I_N -> C -> R) a delta :
  0 <= delta -> (forall i, `|a*(\sum_c (X i c)^+2)-1| <= delta) ->
  pmlo_opb N (a *: (\sum_c pmcr_diagonal N C X c)-1%:M) delta.
Proof.
move=>Hdelta HD.
have E : a *: (\sum_c pmcr_diagonal N C X c)-1%:M =
  diag_mx (\row_i (a*(\sum_c (X i c)^+2)-1)).
{ rewrite pmcr_diagonal_sum; apply/matrixP=>i j; rewrite !mxE.
  case: (i == j); rewrite /= ?mulr0n ?mulr1n ?mulr0 ?subr0 //.
  }
rewrite E; apply: paper_main_opnorm_to_action=>//.
apply: paper_main_diagonal_opnorm=>// i; rewrite mxE; exact: HD.
Qed.
