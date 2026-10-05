(* Pinching into a nearby head subspace: PSD, trace and Frobenius control. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometrySeparation PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCoefficients
  PaperMainProjectionFrobenius.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Definition paper_main_pinching {d} (P S : 'M[R]_d) :=
  P *m S *m P+(1%:M-P) *m S *m (1%:M-P).

Section Pinching.
Variable d : nat.
Implicit Types (P U S : 'M[R]_d).

Lemma paper_main_projection_complement_transpose P : P^T  =  P -> (1%:M-P)^T = 1%:M-P.
Proof. by move=> HP; rewrite linearB /= trmx1 HP. Qed.

Lemma paper_main_projection_complement_square P : P *m P  =  P ->
  (1%:M-P) *m (1%:M-P) = 1%:M-P.
Proof.
by move=> HP; rewrite mulmxBl !mulmxBr !mulmx1 !mul1mx HP subrr subr0.
Qed.

Lemma paper_main_compression_psd P S : P^T  =  P -> paper_main_psd S -> paper_main_psd (P *m S *m P).
Proof.
move=> HP [HS HV]; split.
- apply/paper_main_symmetricP.
  have HST : S^T  =  S by exact/paper_main_symmetricP.
  by rewrite !trmx_mul HP HST mulmxA.
- move=> v; have H := HV (P *m v).
  rewrite !paper_main_quadratic_formE trmx_mul HP !mulmxA in H *.
  exact H.
Qed.

Theorem paper_main_pinching_psd P S : P^T  =  P -> paper_main_psd S -> paper_main_psd (paper_main_pinching P S).
Proof.
move=> HP HS; apply: pms_psd_add; apply: paper_main_compression_psd => //.
exact: paper_main_projection_complement_transpose.
Qed.

Theorem paper_main_pinching_frobenius P S : P^T  =  P -> P *m P  =  P ->
  paper_main_frobenius (paper_main_pinching P S)<=2*paper_main_frobenius S.
Proof.
move=> HP HI.
have HQ := paper_main_projection_complement_transpose P HP.
have HJ := paper_main_projection_complement_square P HI.
have H1 := paper_main_projection_frobenius_right d P (P *m S) HP HI.
have H2 := paper_main_projection_frobenius_left d P S HP HI.
have H3 := paper_main_projection_frobenius_right d (1%:M-P) ((1%:M-P) *m S) HQ HJ.
have H4 := paper_main_projection_frobenius_left d (1%:M-P) S HQ HJ.
have H5 := pmh_frobenius_triangle d (P *m S *m P) ((1%:M-P) *m S *m (1%:M-P)).
rewrite /paper_main_pinching; lra.
Qed.

Lemma paper_main_pinching_error P S : S-paper_main_pinching P S =
  P *m S *m (1%:M-P)+(1%:M-P) *m S *m P.
Proof.
rewrite /paper_main_pinching !mulmxBl !mulmxBr !mul1mx !mulmx1.
by apply/matrixP=> i j; rewrite !mxE; ring.
Qed.

Lemma paper_main_pinching_cross_error P U S : P *m P  =  P -> P *m S = S *m P ->
  U *m S *m (1%:M-U) = (U-P) *m S *m (1%:M-U)+P *m S *m (P-U).
Proof.
move=> HP HC.
have HPS : P *m S *m P = P *m S by rewrite HC -mulmxA HP -HC.
rewrite !mulmxBl !mulmxBr !mulmx1 HPS.
by apply/matrixP=> i j; rewrite !mxE; ring.
Qed.

Theorem paper_main_pinching_cross_frobenius P U S :
  P^T  =  P -> P *m P  =  P -> U^T  =  U -> U *m U  =  U -> P *m S = S *m P ->
  paper_main_frobenius (U *m S *m (1%:M-U))<=
    2*paper_main_frobenius (U-P)*paper_main_frobenius S.
Proof.
move=> HP HI HU HJ HC.
have HQ := paper_main_projection_complement_transpose U HU.
have HK := paper_main_projection_complement_square U HJ.
rewrite (paper_main_pinching_cross_error P U S HI HC).
have H1 := paper_main_projection_frobenius_right d (1%:M-U) ((U-P) *m S) HQ HK.
have H2 := paper_main_frobenius_product d (U-P) S.
have H3 := paper_main_projection_frobenius_left d P (S *m (P-U)) HP HI.
rewrite mulmxA in H3.
have H4 := paper_main_frobenius_product d S (P-U).
rewrite (pmh_frobeniusB d P U) in H4.
have H5 := pmh_frobenius_triangle d ((U-P) *m S *m (1%:M-U)) (P *m S *m (P-U)).
nra.
Qed.

Theorem paper_main_pinching_perturbation P U S :
  P^T  =  P -> P *m P  =  P -> U^T  =  U -> U *m U  =  U -> S^T  =  S -> P *m S = S *m P ->
  paper_main_frobenius (S-paper_main_pinching U S)<=
    4*paper_main_frobenius (U-P)*paper_main_frobenius S.
Proof.
move=> HP HI HU HJ HS HC.
have H1 := paper_main_pinching_cross_frobenius P U S HP HI HU HJ HC.
have HQ := paper_main_projection_complement_transpose U HU.
have ET : (U *m S *m (1%:M-U))^T = (1%:M-U) *m S *m U
  by rewrite !trmx_mul HU HS HQ mulmxA.
have H2 : paper_main_frobenius ((1%:M-U) *m S *m U) = paper_main_frobenius (U *m S *m (1%:M-U))
  by rewrite -ET paper_main_frobenius_transpose.
rewrite paper_main_pinching_error.
have H3 := pmh_frobenius_triangle d (U *m S *m (1%:M-U)) ((1%:M-U) *m S *m U).
rewrite H2 in H3; nra.
Qed.
End Pinching.
