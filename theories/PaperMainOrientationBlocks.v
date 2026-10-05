(* Pinched coordinate blocks in the first-r-rows orientation.

   Dimension d = r + m. For O with O^T O = 1 and any S, let
     P = P_r(O) = O^T diag(1_{i<r}) O,  M = O S O^T,
     H = ulsubmx M (r x r),  B = drsubmx M (m x m).
   1. diag(1_{i<r}) = block_mx 1 0 0 0 and
      1 - diag(1_{i<r}) = block_mx 0 0 0 1.
   2. P S P = O^T (block_mx H 0 0 0) O and
      (1 - P) S (1 - P) = O^T (block_mx 0 0 0 B) O.
   3. paper_main_pinching P S = O^T (block_mx H 0 0 B) O
      (paper_main_orientation_pinching_block). For PSD S the blocks H and B
      are PSD (paper_main_orientation_blocks_psd). For every S,
      ||paper_main_pinching P S||_F^2 = ||H||_F^2 + ||B||_F^2
      (paper_main_orientation_pinching_frobenius), and an operator bound on
      the compressed bulk (1 - P) S (1 - P) is an operator bound on B
      (paper_main_orientation_bulk_opnorm). r = 0 is included. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainConeConditionOperator PaperMainSymmetricDiagonalization
  PaperMainOrthogonalMatrixBounds PaperMainProjectionFrobenius PaperMainProjectionPinching
  PaperMainBlockGeometry PaperMainOrientationNet.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. The mask as a block matrix. *)

Lemma paper_main_orientation_mask_block (r m : nat) :
  diag_mx (paper_main_orientation_mask (d := r + m) r) = block_mx 1%:M 0 0 0.
Proof.
have -> : paper_main_orientation_mask (d := r + m) r =
    row_mx (const_mx 1 : 'rV[R]_r) (const_mx 0 : 'rV[R]_m).
  apply/matrixP => i j; rewrite !mxE.
  case: splitP => k Hk.
    by rewrite mxE.
  by rewrite mxE.
rewrite diag_mx_row !diag_const_mx.
by congr block_mx; apply/matrixP => i j; rewrite !mxE mul0rn.
Qed.

Lemma paper_main_orientation_mask_block_complement (r m : nat) :
  1%:M - diag_mx (paper_main_orientation_mask (d := r + m) r) = block_mx 0 0 0 1%:M.
Proof.
rewrite paper_main_orientation_mask_block (scalar_mx_block r m 1) opp_block_mx add_block_mx.
by rewrite !subrr subr0.
Qed.

(* 2. The compressions as conjugated blocks of M = O S O^T. *)

Lemma paper_main_orientation_head_compression {r m : nat} (O S : 'M[R]_(r + m)) :
  paper_main_orientation_projector r O *m S *m paper_main_orientation_projector r O =
  O^T *m block_mx (ulsubmx (O *m S *m O^T)) 0 0 0 *m O.
Proof.
rewrite /paper_main_orientation_projector.
set D := diag_mx (paper_main_orientation_mask (d := r + m) r).
set M := O *m S *m O^T.
have -> : O^T *m D *m O *m S *m (O^T *m D *m O) = O^T *m (D *m M *m D) *m O.
  by rewrite /M !mulmxA.
rewrite /D paper_main_orientation_mask_block -[in LHS](submxK M).
rewrite !mulmx_block !mul1mx !mul0mx !mulmx1 !mulmx0 ?addr0 ?add0r.
by [].
Qed.

Lemma paper_main_orientation_bulk_compression {r m : nat} (O S : 'M[R]_(r + m)) :
  O^T *m O = 1%:M ->
  (1%:M - paper_main_orientation_projector r O) *m S *m
    (1%:M - paper_main_orientation_projector r O) =
  O^T *m block_mx 0 0 0 (drsubmx (O *m S *m O^T)) *m O.
Proof.
move=> HO.
set D' := 1%:M - diag_mx (paper_main_orientation_mask (d := r + m) r).
have HC : 1%:M - paper_main_orientation_projector r O = O^T *m D' *m O.
  by rewrite /D' /paper_main_orientation_projector mulmxBr mulmxBl mulmx1 HO.
rewrite HC.
set M := O *m S *m O^T.
have -> : O^T *m D' *m O *m S *m (O^T *m D' *m O) = O^T *m (D' *m M *m D') *m O.
  by rewrite /M !mulmxA.
rewrite /D' paper_main_orientation_mask_block_complement -[in LHS](submxK M).
rewrite !mulmx_block !mul1mx !mul0mx !mulmx1 !mulmx0 ?addr0 ?add0r.
by [].
Qed.

(* 3. The pinching, its blocks and their norms. *)

Theorem paper_main_orientation_pinching_block {r m : nat} (O S : 'M[R]_(r + m)) :
  O^T *m O = 1%:M ->
  paper_main_pinching (paper_main_orientation_projector r O) S =
  O^T *m block_mx (ulsubmx (O *m S *m O^T)) 0 0 (drsubmx (O *m S *m O^T)) *m O.
Proof.
move=> HO.
rewrite /paper_main_pinching paper_main_orientation_head_compression
  (paper_main_orientation_bulk_compression O S HO).
by rewrite -mulmxDl -mulmxDr add_block_mx !addr0 !add0r.
Qed.

Theorem paper_main_orientation_blocks_psd {r m : nat} (O S : 'M[R]_(r + m)) :
  paper_main_psd S ->
  paper_main_psd (ulsubmx (O *m S *m O^T)) /\ paper_main_psd (drsubmx (O *m S *m O^T)).
Proof.
move=> HS.
have HM : paper_main_psd (O *m S *m O^T).
  by have := paper_main_psd_congruence (r + m) S O^T HS; rewrite trmxK.
split; [exact: paper_main_block_head_psd | exact: paper_main_block_bulk_psd].
Qed.

Theorem paper_main_orientation_pinching_frobenius {r m : nat} (O S : 'M[R]_(r + m)) :
  O^T *m O = 1%:M ->
  paper_main_frobenius (paper_main_pinching (paper_main_orientation_projector r O) S) ^+ 2 =
  paper_main_frobenius (ulsubmx (O *m S *m O^T)) ^+ 2 +
  paper_main_frobenius (drsubmx (O *m S *m O^T)) ^+ 2.
Proof.
move=> HO.
rewrite (paper_main_orientation_pinching_block O S HO) paper_main_orthogonal_frobenius_square //.
exact: paper_main_block_frobenius.
Qed.

Theorem paper_main_orientation_bulk_opnorm {r m : nat} (O S : 'M[R]_(r + m)) (b : R) :
  O^T *m O = 1%:M ->
  paper_main_cone_opnorm_le ((1%:M - paper_main_orientation_projector r O) *m S *m
    (1%:M - paper_main_orientation_projector r O)) b ->
  paper_main_cone_opnorm_le (drsubmx (O *m S *m O^T)) b.
Proof.
move=> HO Hb.
rewrite (paper_main_orientation_bulk_compression O S HO) in Hb.
have HO' : O *m O^T = 1%:M by apply: mulmx1C.
have HT : (O^T)^T *m O^T = 1%:M by rewrite trmxK.
have H := paper_main_orthogonal_congruence_opnorm (r + m) _ O^T b HT Hb.
rewrite trmxK !mulmxA HO' mul1mx -mulmxA HO' mulmx1 in H.
exact: (paper_main_block_bulk_opnorm r m 0 _ b H).
Qed.
