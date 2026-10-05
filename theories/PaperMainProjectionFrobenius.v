(* Dimension-free Frobenius estimates for products and orthogonal projections. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCoefficients PaperMainConeConditionOperator
  PaperMainDiagonalBlockTrace.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section Frobenius.
Variable d : nat.
Implicit Types (A B P : 'M[R]_d) (u v : 'cV[R]_d).

Lemma paper_main_frobenius_transpose A : paper_main_frobenius A^T=paper_main_frobenius A.
Proof.
rewrite /paper_main_frobenius; congr (Num.sqrt _); rewrite /paper_main_pairing exchange_big.
by apply: eq_bigr => i _; apply: eq_bigr => j _; rewrite !mxE.
Qed.

Lemma paper_main_frobenius_trace A : paper_main_frobenius A ^+ 2=\tr(A^T *m A).
Proof.
rewrite pmh_frobenius_sqr /paper_main_pairing /mxtrace exchange_big.
by apply: eq_bigr => i _; rewrite mxE; apply: eq_bigr => j _; rewrite mxE.
Qed.

Lemma paper_main_frobenius_columns A : paper_main_frobenius A ^+ 2=
  \sum_(i<d) (((col i A)^T *m col i A) 0 0).
Proof.
rewrite pmh_frobenius_sqr /paper_main_pairing exchange_big.
by apply: eq_bigr => i _; rewrite pmh_vec_dot; apply: eq_bigr => j _; rewrite !mxE.
Qed.

Lemma paper_main_product_column A B (j : 'I_d) : col j (A *m B)=A *m col j B.
Proof.
apply/matrixP=> i k; rewrite !mxE.
by apply: eq_bigr => a _; rewrite mxE.
Qed.

Lemma paper_main_opnorm_action A c : paper_main_cone_opnorm_le A c ->
  forall v, ((A *m v)^T *m (A *m v)) 0 0<=c ^+ 2*(v^T *m v) 0 0.
Proof.
move=> HA v.
have H := HA (A *m v) v; rewrite -mulmxA in H.
have Hx := pmh_vec_sqr_ge0 _ (A *m v).
have Hy := pmh_vec_sqr_ge0 _ v.
have Hc := sqr_ge0 c.
set x := ((A *m v)^T *m (A *m v)) 0 0 in H Hx *.
have [Hx0|Hx0] := eqVneq x 0; first by rewrite Hx0 mulr_ge0.
have Hxp : 0<x by rewrite lt0r Hx0.
nra.
Qed.

Lemma paper_main_action_frobenius A B c :
  (forall v, ((A *m v)^T *m (A *m v)) 0 0<=c ^+ 2*(v^T *m v) 0 0) ->
  paper_main_frobenius (A *m B) ^+ 2<=c ^+ 2*paper_main_frobenius B ^+ 2.
Proof.
move=> HA; rewrite !paper_main_frobenius_columns mulr_sumr.
by apply: ler_sum => j _; rewrite paper_main_product_column; exact: HA.
Qed.

Theorem paper_main_opnorm_frobenius_left A B c : 0<=c -> paper_main_cone_opnorm_le A c ->
  paper_main_frobenius (A *m B)<=c*paper_main_frobenius B.
Proof.
move=> Hc HA.
have H := paper_main_action_frobenius A B c (paper_main_opnorm_action A c HA).
have H1 := pmh_frobenius_ge0 _ (A *m B).
have H2 := pmh_frobenius_ge0 _ B.
have H3 : 0<=c*paper_main_frobenius B by exact: mulr_ge0.
nra.
Qed.

Theorem paper_main_frobenius_product A B :
  paper_main_frobenius (A *m B)<=paper_main_frobenius A*paper_main_frobenius B.
Proof.
have H := paper_main_action_frobenius A B (paper_main_frobenius A).
have HA : forall v, ((A *m v)^T *m (A *m v)) 0 0<=
  paper_main_frobenius A ^+ 2*(v^T *m v) 0 0.
  move=> v; rewrite paper_main_frobenius_trace; exact: pmdb_form_frobenius.
have HH := H HA.
have H1 := pmh_frobenius_ge0 _ (A *m B).
have H2 := pmh_frobenius_ge0 _ B.
have H3 := pmh_frobenius_ge0 _ A.
have H4 : 0<=paper_main_frobenius A*paper_main_frobenius B by exact: mulr_ge0.
nra.
Qed.

Lemma paper_main_projection_action P : P^T= P -> P *m P= P ->
  forall v, ((P *m v)^T *m (P *m v)) 0 0<=(v^T *m v) 0 0.
Proof.
move=> HP HI v.
have E : ((P *m v)^T *m (P *m v)) 0 0=(v^T *m P *m v) 0 0.
  by rewrite trmx_mul HP !mulmxA -(mulmxA v^T P P) HI.
have H := pmco_vec_cauchy_schwarz _ v (P *m v).
rewrite mulmxA -E in H.
have Hx := pmh_vec_sqr_ge0 _ (P *m v).
have Hy := pmh_vec_sqr_ge0 _ v.
nra.
Qed.

Theorem paper_main_projection_frobenius_left P A : P^T= P -> P *m P= P ->
  paper_main_frobenius (P *m A)<=paper_main_frobenius A.
Proof.
move=> HP HI.
have H := paper_main_action_frobenius P A 1.
have HH : forall v, ((P *m v)^T *m (P *m v)) 0 0<=1 ^+ 2*(v^T *m v) 0 0.
  move=> v; rewrite expr1n mul1r; exact: paper_main_projection_action.
have HB := H HH; rewrite expr1n mul1r in HB.
have H1 := pmh_frobenius_ge0 _ (P *m A).
have H2 := pmh_frobenius_ge0 _ A.
nra.
Qed.

Theorem paper_main_projection_frobenius_right P A : P^T= P -> P *m P= P ->
  paper_main_frobenius (A *m P)<=paper_main_frobenius A.
Proof.
move=> HP HI.
rewrite -[paper_main_frobenius (A *m P)]paper_main_frobenius_transpose trmx_mul HP.
apply: le_trans (paper_main_projection_frobenius_left P A^T HP HI) _.
by rewrite paper_main_frobenius_transpose.
Qed.
End Frobenius.
