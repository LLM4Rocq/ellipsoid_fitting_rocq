(* A feasible ellipsoid gives a bounded-offset, small-loss pinched candidate. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import Analysis.ContinuousTupleMeasurability
  PaperMainDefinitions Geometry.Psd Geometry.Homogeneous Geometry.HeadFrobenius
  Feature.GramBlocks Feature.LossControl Projection.Frobenius
  Projection.Pinching Projection.PinchingOperator Projection.PinchingAnnulus
  Loss.Empirical Cone.ConditionOperator.
Import GRing.Theory Num.Theory Order.TTheory.
Delimit Scope R_scope with Rcoq.
Local Open Scope ring_scope.

Theorem paper_main_fit_unit_witness N d (x : paper_main_sample N d) :
  (0<N)%N -> (0<d)%N -> paper_main_fit_event N d x ->
  exists (S : 'M[R]_d) b, paper_main_psd S /\ paper_main_frobenius S = 1 /\
    forall i : 'I_N, paper_main_quadratic_form S (paper_main_point x i)-paper_main_trace S = b.
Proof.
move=> HN Hd [S [HS HF]].
apply: (proj1 (paper_main_homogeneous_witness N d x)).
exists S; split=> //; split; last by exists d%:R.
apply: (paper_main_form_neq0 _ S (paper_main_point x (Ordinal HN))).
by rewrite HF pnatr_eq0 -lt0n.
Qed.

Theorem paper_main_pinching_witness_risk N d (x : paper_main_sample N d) (P U S : 'M[R]_d) b K L tau :
  (0<N)%N -> 0<=K -> (0<=L)%Rcoq ->
  paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) -> (K<=INR N*L^2)%Rcoq ->
  P^T = P -> P *m P = P -> U^T = U -> U *m U = U -> S^T = S -> P *m S = S *m P ->
  paper_main_frobenius S = 1 -> paper_main_frobenius (U-P)<=tau ->
  (forall i : 'I_N, paper_main_quadratic_form S (paper_main_point x i)-paper_main_trace S = b) ->
  (paper_main_quadratic_risk N d x (paper_main_pinching U S) b<=16*L*tau)%Rcoq.
Proof.
move=> HN HK HL HG Hscale HP HI HU HJ HS HC HF HD Hb.
have Hzero := paper_main_quadratic_risk_zero N d x S b Hb.
have Hlip := paper_main_quadratic_risk_lipschitz N d x S (paper_main_pinching U S) b K L HN HK HL HG Hscale.
rewrite Hzero Rminus_0_l Rabs_Ropp in Hlip.
have Hpert := paper_main_pinching_perturbation d P U S HP HI HU HJ HS HC.
rewrite HF mulr1 in Hpert.
have Hdist : (paper_main_frobenius (S-paper_main_pinching U S)<=4*tau)%Rcoq.
  have HpR : (paper_main_frobenius (S-paper_main_pinching U S)<=4*paper_main_frobenius (U-P))%Rcoq.
    have E4 : IZR 4 = (4%:R : R) by rewrite -INRE INR_IZR_INZ.
    apply/RleP; rewrite RmultE E4; exact Hpert.
  have HdR : (paper_main_frobenius (U-P)<=tau)%Rcoq by exact/RleP.
  eapply Rle_trans; [exact HpR|].
  apply Rmult_le_compat_l; [Stdlib.micromega.Lra.lra|exact HdR].
have HL4 : (0<=4*L)%Rcoq by Stdlib.micromega.Lra.lra.
have HH := Rmult_le_compat_l (4*L)%Rcoq _ _ HL4 Hdist.
have HA := Rle_abs (paper_main_quadratic_risk N d x (paper_main_pinching U S) b).
eapply Rle_trans; [exact HA|].
eapply Rle_trans; [exact Hlip|].
replace (16*L*tau)%Rcoq with ((4*L)*(4*tau))%Rcoq by Stdlib.micromega.Lra.nra.
exact HH.
Qed.

Theorem paper_main_pinching_unit_norm d (P U S : 'M[R]_d) :
  P^T = P -> P *m P = P -> U^T = U -> U *m U = U -> S^T = S -> P *m S = S *m P ->
  paper_main_frobenius S = 1 -> paper_main_frobenius (U-P)<=1/8 ->
  1/4<=paper_main_frobenius (paper_main_pinching U S)^+2<=4.
Proof.
move=> HP HI HU HJ HS HC HF HD.
have H := paper_main_pinching_annulus d P U S HP HI HU HJ HS HC HF HD.
by rewrite paper_main_pinching_norm_split in H.
Qed.

Theorem paper_main_pinching_cutoff_bulk d (P U H B : 'M[R]_d) eps tau :
  P^T = P -> U^T = U -> U *m U = U -> P *m H *m P = H ->
  0<=eps -> 0<=tau -> paper_main_frobenius H<=1 -> paper_main_frobenius (U-P)<=tau ->
  paper_main_cone_opnorm_le B eps ->
  paper_main_cone_opnorm_le ((1%:M-U) *m (H+B) *m (1%:M-U)) (eps+tau^+2).
Proof.
move=> HP HU HJ HS He Ht HH HD HB.
have Hop := paper_main_pinching_bulk_opnorm d P U H B eps HP HU HJ HS He HB.
have Ha : 0<=paper_main_frobenius (U-P)^+2*paper_main_frobenius H+eps.
  apply: addr_ge0=> //; apply: mulr_ge0; [exact: sqr_ge0|exact: pmh_frobenius_ge0].
have Hle : paper_main_frobenius (U-P)^+2*paper_main_frobenius H+eps<=eps+tau^+2.
  have H0 := pmh_frobenius_ge0 d (U-P); have HH0 := pmh_frobenius_ge0 d H.
  have Hsq : paper_main_frobenius (U-P)^+2<=tau^+2 by rewrite ler_sqr ?nnegrE.
  have HH1 : paper_main_frobenius (U-P)^+2*paper_main_frobenius H<=paper_main_frobenius (U-P)^+2*1.
    by apply: ler_wpM2l; first exact: sqr_ge0.
  nra.
exact: (paper_main_opnorm_monotone d _ _ _ Ha Hle Hop).
Qed.
