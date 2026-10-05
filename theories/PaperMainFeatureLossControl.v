(* Actual feature control bounds scalar offsets and empirical quadratic-loss perturbations. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianCovarianceSums PaperMainMatrixDuality
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius
  PaperMainGeometryHeadCorrection PaperMainFeatureGramBlocks PaperMainFeatureForwardBound
  PaperMainLossEmpirical PaperMainTranslatedLoss.
Import GRing.Theory Num.Theory Order.TTheory.
Delimit Scope R_scope with Rcoq.
Local Open Scope ring_scope.

Definition paper_main_quadratic_risk N d (x : paper_main_sample N d) (S : 'M[R]_d) b :=
  paper_main_loss_empirical N (fun i =>
    (paper_main_quadratic_form S (paper_main_point x i)-paper_main_trace S-b)%Rcoq).

Theorem paper_main_feature_witness_offset N d (x : paper_main_sample N d) (S : 'M[R]_d) b K L :
  (0<N)%N -> 0<=K -> 0<=L ->
  paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) ->
  K<=N%:R*L^+2 -> paper_main_frobenius S = 1 ->
  (forall i : 'I_N, paper_main_quadratic_form S (paper_main_point x i)-paper_main_trace S = b) -> `|b|<=L.
Proof.
move=> HN HK HL HG Hscale HS Hb.
have H := paper_main_raw_feature_forward N d x S K HK HG.
have E : (\sum_(i<N) (paper_main_quadratic_form S (paper_main_point x i)-paper_main_trace S)^+2) =
  N%:R*b^+2.
  under eq_bigr do rewrite Hb.
  by rewrite sumr_const card_ord mulr_natl.
rewrite E HS expr1n mulr1 in H.
have HNL : N%:R*b^+2<=N%:R*L^+2 := le_trans H Hscale.
have HNR : (0 : R)<N%:R by rewrite ltr0n.
have Hsq : b^+2<=L^+2 by move: HNL; rewrite ler_pM2l.
have Eabs : `|b|^+2 = b^+2 by rewrite -normrX ger0_norm ?sqr_ge0.
rewrite -Eabs in Hsq.
by move: Hsq; rewrite ler_sqr ?nnegrE ?normr_ge0.
Qed.

Theorem paper_main_feature_difference_normalized N d (x : paper_main_sample N d) (S T : 'M[R]_d) K L :
  0<=K -> paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) ->
  (K<=INR N*L^2)%Rcoq ->
  (finite_sum (fun i =>
    ((paper_main_quadratic_form S (paper_main_point x i)-paper_main_trace S)-
     (paper_main_quadratic_form T (paper_main_point x i)-paper_main_trace T))^2) (List.seq 0 N)
    <=INR N*(L*paper_main_frobenius (S-T)%R)^2)%Rcoq.
Proof.
move=> HK HG HS.
have H := paper_main_raw_feature_forward_difference N d x S T K HK HG.
have Hp := pow2_ge_0 (paper_main_frobenius (S-T)).
have Hmul := Rmult_le_compat_r (paper_main_frobenius (S-T)^2)%Rcoq _ _ Hp HS.
change (finite_sum (fun i =>
    ((paper_main_quadratic_form S (paper_main_point x i)-paper_main_trace S)-
     (paper_main_quadratic_form T (paper_main_point x i)-paper_main_trace T))^2) (List.seq 0 N)
    <=INR N*(L*paper_main_frobenius (S-T)%R)^2)%Rcoq.
eapply Rle_trans; [exact H|].
replace (INR N*(L*paper_main_frobenius (S-T))^2)%Rcoq with
  (INR N*L^2*paper_main_frobenius (S-T)^2)%Rcoq by ring.
exact Hmul.
Qed.

Theorem paper_main_quadratic_risk_lipschitz N d (x : paper_main_sample N d) (S T : 'M[R]_d) b K L :
  (0<N)%N -> 0<=K -> (0<=L)%Rcoq ->
  paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) ->
  (K<=INR N*L^2)%Rcoq ->
  (Rabs(paper_main_quadratic_risk N d x S b-paper_main_quadratic_risk N d x T b)<=
    4*L*paper_main_frobenius (S-T))%Rcoq.
Proof.
move=> HN HK HL HG HS.
have H := paper_main_feature_difference_normalized N d x S T K L HK HG HS.
apply: paper_main_loss_empirical_lipschitz.
- exact/ssrnat.ltP.
- exact HL.
- apply/RleP; exact: pmh_frobenius_ge0.
- have E : finite_sum (fun i =>
    ((paper_main_quadratic_form S (paper_main_point x i)-paper_main_trace S-b)-
     (paper_main_quadratic_form T (paper_main_point x i)-paper_main_trace T-b))^2)%Rcoq (List.seq 0 N) =
    finite_sum (fun i =>
    ((paper_main_quadratic_form S (paper_main_point x i)-paper_main_trace S)-
     (paper_main_quadratic_form T (paper_main_point x i)-paper_main_trace T))^2)%Rcoq (List.seq 0 N).
    apply: finite_sum_ext=>i _; f_equal; ring.
  by rewrite E.
Qed.

Theorem paper_main_quadratic_risk_zero N d (x : paper_main_sample N d) (S : 'M[R]_d) b :
  (forall i : 'I_N, paper_main_quadratic_form S (paper_main_point x i)-paper_main_trace S = b) ->
  paper_main_quadratic_risk N d x S b = 0.
Proof.
move=> Hb; apply: paper_main_loss_empirical_zero=>i Hi.
have Hi' : (i<N)%N by exact/ssrnat.ltP.
have H := Hb (Ordinal Hi'); change (paper_main_quadratic_form S (paper_main_point x i)-paper_main_trace S = b) in H.
by rewrite -RminusE in H; rewrite H; apply Rminus_diag.
Qed.
