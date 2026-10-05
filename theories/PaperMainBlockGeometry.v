(* Public quadratic, trace and Frobenius identities for orthogonal head/bulk blocks. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCoefficients PaperMainProjectionFrobenius
  PaperMainOrthogonalMatrixBounds PaperMainSymmetricDiagonalization PaperMainConeConditionOperator.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Lemma paper_main_orthogonal_frobenius_square d (O A : 'M[R]_d) : O^T *m O = 1%:M ->
  paper_main_frobenius (O^T *m A *m O)^+2 = paper_main_frobenius A^+2.
Proof.
move=> HO; have HT := paper_main_symmetric_orthogonal_tr d O HO.
rewrite !paper_main_frobenius_trace !trmx_mul trmxK.
have E : (O^T *m (A^T *m O)) *m (O^T *m A *m O) = O^T *m (A^T *m A) *m O.
  by rewrite -!mulmxA (mulmxA O) HT mul1mx.
rewrite E mxtrace_mulC (mulmxA O) HT mul1mx.
reflexivity.
Qed.

Lemma paper_main_orthogonal_frobenius d (O A : 'M[R]_d) : O^T *m O = 1%:M ->
  paper_main_frobenius (O^T *m A *m O) = paper_main_frobenius A.
Proof.
move=> HO; have H := paper_main_orthogonal_frobenius_square d O A HO.
have H1 := pmh_frobenius_ge0 d (O^T *m A *m O); have H2 := pmh_frobenius_ge0 d A.
nra.
Qed.

Lemma paper_main_orthogonal_trace d (O A : 'M[R]_d) : O^T *m O = 1%:M ->
  paper_main_trace (O^T *m A *m O) = paper_main_trace A.
Proof.
move=> HO; have HT := paper_main_symmetric_orthogonal_tr d O HO.
change (\tr(O^T *m A *m O) = \tr A).
by rewrite mxtrace_mulC mulmxA HT mul1mx.
Qed.

Section Blocks.
Variables r m : nat.
Implicit Types (H : 'M[R]_r) (B : 'M[R]_m) (M : 'M[R]_(r+m)) (g : 'cV[R]_r) (y : 'cV[R]_m).

Lemma paper_main_block_form H B g y :
  paper_main_quadratic_form (block_mx H 0 0 B) (col_mx g y) =
  paper_main_quadratic_form H g+paper_main_quadratic_form B y.
Proof.
rewrite !paper_main_quadratic_formE tr_col_mx -mulmxA mul_block_col !mul0mx !addr0 !add0r.
by rewrite mul_row_col !mulmxA mxE.
Qed.

Lemma paper_main_block_trace H B : paper_main_trace (block_mx H 0 0 B) = paper_main_trace H+paper_main_trace B.
Proof. exact: mxtrace_block. Qed.

Lemma paper_main_block_frobenius H B :
  paper_main_frobenius (block_mx H 0 0 B)^+2 = paper_main_frobenius H^+2+paper_main_frobenius B^+2.
Proof.
by rewrite !paper_main_frobenius_trace tr_block_mx !trmx0 mulmx_block
  !mulmx0 !mul0mx !addr0 !add0r mxtrace_block.
Qed.

Lemma paper_main_block_symmetric H B : paper_main_symmetric H -> paper_main_symmetric B ->
  paper_main_symmetric (block_mx H 0 0 B).
Proof.
move=> /paper_main_symmetricP HH /paper_main_symmetricP HB; apply/paper_main_symmetricP.
by rewrite tr_block_mx !trmx0 HH HB.
Qed.

Theorem paper_main_block_psd H B : paper_main_psd H -> paper_main_psd B -> paper_main_psd (block_mx H 0 0 B).
Proof.
move=> [HH HP] [HB BP]; split; first exact: paper_main_block_symmetric.
move=> v; rewrite -[v]vsubmxK paper_main_block_form; exact: addr_ge0 (HP _) (BP _).
Qed.

Theorem paper_main_block_head_psd M : paper_main_psd M -> paper_main_psd (ulsubmx M).
Proof.
move=> [HM HP]; split.
- apply/paper_main_symmetricP.
  have HMT : M^T = M by exact/paper_main_symmetricP.
  have H := congr1 (@ulsubmx R r m r m) HMT.
  by rewrite -{1}[M]submxK tr_block_mx block_mxKul in H.
- move=> g; have H := HP (col_mx g (0 : 'cV[R]_m)).
  rewrite !paper_main_quadratic_formE -{1}[M]submxK tr_col_mx -mulmxA mul_block_col
    !mulmx0 !addr0 mul_row_col trmx0 mul0mx addr0 mulmxA in H.
  by rewrite paper_main_quadratic_formE.
Qed.

Theorem paper_main_block_bulk_psd M : paper_main_psd M -> paper_main_psd (drsubmx M).
Proof.
move=> [HM HP]; split.
- apply/paper_main_symmetricP.
  have HMT : M^T = M by exact/paper_main_symmetricP.
  have H := congr1 (@drsubmx R r m r m) HMT.
  by rewrite -{1}[M]submxK tr_block_mx block_mxKdr in H.
- move=> y; have H := HP (col_mx (0 : 'cV[R]_r) y).
  rewrite !paper_main_quadratic_formE -{1}[M]submxK tr_col_mx -mulmxA mul_block_col
    !mulmx0 !add0r mul_row_col trmx0 mul0mx add0r mulmxA in H.
  by rewrite paper_main_quadratic_formE.
Qed.

Theorem paper_main_block_bulk_opnorm H B b : paper_main_cone_opnorm_le (block_mx H 0 0 B) b ->
  paper_main_cone_opnorm_le B b.
Proof.
move=> HB u v; have Hop := HB (col_mx (0 : 'cV[R]_r) u) (col_mx (0 : 'cV[R]_r) v).
by rewrite !tr_col_mx -mulmxA mul_block_col !mulmx0 !mul0mx !addr0 !add0r
  !mul_row_col !trmx0 !mul0mx !add0r mulmxA in Hop.
Qed.
End Blocks.
