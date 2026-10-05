(* The orthogonal head/bulk blocks of a nearby pinching retain a nonzero norm. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainProjectionFrobenius PaperMainProjectionPinching.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section Annulus.
Variable d : nat.
Implicit Types (P U S A B : 'M[R]_d).

Lemma paper_main_pairing_trace A B : paper_main_pairing A B = \tr(A^T *m B).
Proof.
rewrite /paper_main_pairing /mxtrace exchange_big.
by apply: eq_bigr => i _; rewrite mxE; apply: eq_bigr => j _; rewrite mxE.
Qed.

Lemma paper_main_pinching_orthogonal P S : P^T = P -> P *m P = P ->
  paper_main_pairing (P *m S *m P) ((1%:M-P) *m S *m (1%:M-P)) = 0.
Proof.
move=> HP HI.
pose Q := 1%:M-P.
have HPQ : P *m Q = 0 by rewrite /Q mulmxBr mulmx1 HI subrr.
have E : (P *m S *m P)^T *m (Q *m S *m Q) = 0.
  by rewrite !trmx_mul HP !mulmxA -(mulmxA (P *m S^T) P Q) HPQ !mulmx0 !mul0mx.
change (paper_main_pairing (P *m S *m P) (Q *m S *m Q) = 0).
by rewrite paper_main_pairing_trace E raddf0.
Qed.

Theorem paper_main_pinching_norm_split P S : P^T = P -> P *m P = P ->
  paper_main_frobenius (P *m S *m P)^+2+
  paper_main_frobenius ((1%:M-P) *m S *m (1%:M-P))^+2 =
  paper_main_frobenius (paper_main_pinching P S)^+2.
Proof.
move=> HP HI.
have H := paper_main_pinching_orthogonal P S HP HI.
rewrite !pmh_frobenius_sqr /paper_main_pinching pmh_pairingDl !pmh_pairingDr H.
rewrite (paper_main_pairingC d ((1%:M-P) *m S *m (1%:M-P)) (P *m S *m P)) H.
by rewrite add0r addr0.
Qed.

Theorem paper_main_pinching_annulus P U S :
  P^T = P -> P *m P = P -> U^T = U -> U *m U = U -> S^T = S -> P *m S = S *m P ->
  paper_main_frobenius S = 1 -> paper_main_frobenius (U-P)<=1/8 ->
  1/4<=paper_main_frobenius (U *m S *m U)^+2+
    paper_main_frobenius ((1%:M-U) *m S *m (1%:M-U))^+2<=4.
Proof.
move=> HP HI HU HJ HS HC Hnorm HD.
rewrite (paper_main_pinching_norm_split U S HU HJ).
have He := paper_main_pinching_perturbation d P U S HP HI HU HJ HS HC.
have Ht := pmh_frobenius_triangle d (paper_main_pinching U S) (S-paper_main_pinching U S).
have E : paper_main_pinching U S+(S-paper_main_pinching U S) = S by rewrite addrC subrK.
rewrite E Hnorm in Ht; rewrite Hnorm mulr1 in He.
have Hu := paper_main_pinching_frobenius d U S HU HJ; rewrite Hnorm mulr1 in Hu.
have Hf := pmh_frobenius_ge0 d (paper_main_pinching U S).
apply/andP; split; nra.
Qed.
End Annulus.
