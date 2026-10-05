(* Positive and operator bounds for diagonal matrices in orthogonal coordinates. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
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

Lemma paper_main_orthogonal_vector_norm O : O^T *m O = 1%:M ->
  forall v, ((O *m v)^T *m (O *m v)) 0 0 = (v^T *m v) 0 0.
Proof.
move=> HO v.
by rewrite trmx_mul !mulmxA -(mulmxA v^T O^T O) HO mulmx1.
Qed.

Lemma paper_main_action_to_opnorm A b :
  (forall v, ((A *m v)^T *m (A *m v)) 0 0<=b^+2*(v^T *m v) 0 0) ->
  paper_main_cone_opnorm_le A b.
Proof.
move=> HA u v.
have H1 := pmco_vec_cauchy_schwarz d u (A *m v).
rewrite mulmxA in H1.
have H2 := HA v; have Hu := pmh_vec_sqr_ge0 d u.
have H3 : (u^T *m u) 0 0*((A *m v)^T *m (A *m v)) 0 0<=
  (u^T *m u) 0 0*(b^+2*(v^T *m v) 0 0) by apply: ler_wpM2l.
nra.
Qed.

Theorem paper_main_orthogonal_congruence_opnorm A O b : O^T *m O = 1%:M ->
  paper_main_cone_opnorm_le A b -> paper_main_cone_opnorm_le (O^T *m A *m O) b.
Proof.
move=> HO HA u v; have H := HA (O *m u) (O *m v).
rewrite !paper_main_orthogonal_vector_norm // in H.
have E : ((O *m u)^T *m A *m (O *m v)) 0 0 =
  (u^T *m (O^T *m A *m O) *m v) 0 0 by rewrite trmx_mul !mulmxA.
by rewrite E in H.
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
move=> Hb Ha; apply: paper_main_action_to_opnorm=>v.
rewrite !pmh_vec_dot mulr_sumr; apply: ler_sum=>i _.
rewrite paper_main_diagonal_vector_entry -!expr2 exprMn.
apply: ler_wpM2r; first exact: sqr_ge0.
have H : `|a 0 i|^+2<=b^+2 by rewrite ler_sqr ?nnegrE ?normr_ge0.
by rewrite -normrX ger0_norm ?sqr_ge0 in H.
Qed.
End Orthogonal.
