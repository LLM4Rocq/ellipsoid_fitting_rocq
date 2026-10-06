(* A raw-feature Gram upper bound controls centered quadratic losses in L2. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import AnalysisBridge GaussianProbabilityProductContinuity SoftDefinitions PaperMainMatrixDuality
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadFeature PaperMainFeatureGramBlocks.
From EllipsoidFitting Require Import RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Delimit Scope R_scope with Rcoq.
Local Open Scope ring_scope.

Theorem paper_main_feature_gram_forward d N (W : 'I_N -> 'M[R]_d) (B : 'M[R]_d) K :
  0<=K -> paper_main_loewner_le (paper_main_head_gram W) (K *: 1%:M) ->
  \sum_(i<N) paper_main_pairing (W i) B ^+ 2<=K*paper_main_frobenius B ^+ 2.
Proof.
move=> HK [_ HG].
pose v := paper_main_head_residual W B.
pose A := paper_main_head_correction W v.
pose t := (v^T *m v) 0 0.
have Ht : 0<=t by exact: pmh_vec_sqr_ge0.
have HtE : t = \sum_(i<N) paper_main_pairing (W i) B ^+ 2.
  rewrite /t pmh_vec_dot; apply: eq_bigr => i _.
  by rewrite /v /paper_main_head_residual !mxE expr2.
have EP : paper_main_pairing B A = -t.
  rewrite /A paper_main_head_correction_pairing HtE.
  congr (- _); apply: eq_bigr=>i _.
  by rewrite /v /paper_main_head_residual mxE paper_main_pairingC expr2.
have HA : paper_main_frobenius A ^+ 2<=K*t.
  have H := HG v.
  rewrite pms_formB paper_main_form_scale pmh_form_id paper_main_quadratic_formE in H.
  rewrite /A paper_main_head_correction_frobenius /t; lra.
have HC := pmh_pairing_cauchy_schwarz d B A.
rewrite EP exprNn -!pmh_frobenius_sqr in HC.
have HB := sqr_ge0 (paper_main_frobenius B).
have HM : paper_main_frobenius B ^+ 2*paper_main_frobenius A ^+ 2<=
  paper_main_frobenius B ^+ 2*(K*t) by apply: ler_wpM2l.
have Hpos : 0<=K*paper_main_frobenius B ^+ 2 by exact: mulr_ge0.
rewrite -HtE.
have [Ht0|Ht0] := eqVneq t 0; first by rewrite Ht0.
have Htp : 0<t by rewrite lt0r Ht0.
nra.
Qed.

Lemma paper_main_raw_feature_pairing N d (x : paper_main_sample N d) i (B : 'M[R]_d) :
  paper_main_pairing (paper_main_raw_feature N d x i) B =
  paper_main_quadratic_form B (paper_main_point x i)-paper_main_trace B.
Proof.
rewrite /paper_main_raw_feature pmh_pairingBl pmh_pairing_id.
by rewrite paper_main_pairingC paper_main_pairing_outer.
Qed.

Theorem paper_main_raw_feature_forward N d (x : paper_main_sample N d) (B : 'M[R]_d) K :
  0<=K -> paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) ->
  \sum_(i<N) (paper_main_quadratic_form B (paper_main_point x i)-paper_main_trace B)^+2<=
    K*paper_main_frobenius B^+2.
Proof.
move=> HK HG.
have H := paper_main_feature_gram_forward d N (fun i => paper_main_raw_feature N d x i) B K HK HG.
have E : (\sum_(i<N) paper_main_pairing (paper_main_raw_feature N d x i) B ^+ 2) =
  \sum_(i<N) (paper_main_quadratic_form B (paper_main_point x i)-paper_main_trace B)^+2.
  by apply: eq_bigr=>i _; rewrite paper_main_raw_feature_pairing.
by rewrite E in H.
Qed.

Theorem paper_main_raw_feature_forward_difference N d (x : paper_main_sample N d) (B C : 'M[R]_d) K :
  0<=K -> paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) ->
  (finite_sum (fun i =>
    ((paper_main_quadratic_form B (paper_main_point x i)-paper_main_trace B)-
     (paper_main_quadratic_form C (paper_main_point x i)-paper_main_trace C))^2) (List.seq 0 N)
    <=K*paper_main_frobenius (B-C)%R^2)%Rcoq.
Proof.
move=> HK HG; apply/RleP.
rewrite finite_sum_seqE RmultE RpowE.
have H := paper_main_raw_feature_forward N d x (B-C) K HK HG.
apply: le_trans _ H; apply: ler_sum=>i _.
rewrite -RpowE pms_formB pms_traceB.
rewrite -!RminusE.
apply/RleP; change (((paper_main_quadratic_form B (paper_main_point x i)-paper_main_trace B)-
  (paper_main_quadratic_form C (paper_main_point x i)-paper_main_trace C))^2<=
  ((paper_main_quadratic_form B (paper_main_point x i)-paper_main_quadratic_form C (paper_main_point x i))-
   (paper_main_trace B-paper_main_trace C))^2)%Rcoq.
right; ring.
Qed.
