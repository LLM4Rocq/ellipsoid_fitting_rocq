(* Positive and operator bounds for diagonal matrices in orthogonal coordinates. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic sesquilinear.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCoefficients PaperMainConeConditionOperator
  PaperMainSymmetricDiagonalization.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section Orthogonal.
Variable d : nat.
Implicit Types (A O : 'M[R]_d) (u v : 'cV[R]_d) (a : 'rV[R]_d).

Theorem paper_main_psd_congruence A O : paper_main_psd A -> paper_main_psd (O^T *m A *m O).
Proof.
move=> [HA HP]; split.
- apply/paper_main_symmetricP.
  have HAT : A^T = A by exact/paper_main_symmetricP.
  by rewrite !trmx_mul trmxK HAT mulmxA.
- move=> v; have H := HP (O *m v).
  by rewrite !paper_main_quadratic_formE trmx_mul !mulmxA in H *.
Qed.

Theorem paper_main_orthogonal_congruence_opnorm A O b : O^T *m O = 1%:M ->
  paper_main_cone_opnorm_le A b -> paper_main_cone_opnorm_le (O^T *m A *m O) b.
Proof.
move=> /paper_main_symmetric_orthogonalmx Oo /paper_main_cone_opnorm_leP HA.
apply/paper_main_cone_opnorm_leP.
by rewrite opnorm_orthogonalmxr // opnorm_orthogonalmxl ?trmx_orthogonal.
Qed.

Lemma paper_main_diagonal_vector_entry a v (i : 'I_d) :
  (diag_mx a *m v) i 0 = a 0 i*v i 0.
Proof.
rewrite mxE (bigD1 i) //= big1.
- by move=> j Hj; rewrite mxE eq_sym (negbTE Hj) mulr0n mul0r.
- by rewrite mxE eqxx mulr1n addr0.
Qed.

Theorem paper_main_diagonal_psd a : (forall i, 0<=a 0 i) -> paper_main_psd (diag_mx a).
Proof.
move=> Ha; split.
- apply/paper_main_symmetricP; exact: tr_diag_mx.
- move=> v; rewrite paper_main_symmetric_diag_form.
  by apply: sumr_ge0=>i _; apply: mulr_ge0; [exact: Ha|exact: sqr_ge0].
Qed.

Theorem paper_main_diagonal_opnorm a b : 0<=b -> (forall i, `|a 0 i|<=b) ->
  paper_main_cone_opnorm_le (diag_mx a) b.
Proof.
move=> Hb Ha; apply/paper_main_cone_opnorm_leP; rewrite ger0_norm //.
rewrite (@opnorm_spectral _ _ _ 1%:M a) ?orthogonalmx1 ?trmx1 ?mul1mx ?mulmx1 //.
by apply/bigmax_leP; split.
Qed.
End Orthogonal.
