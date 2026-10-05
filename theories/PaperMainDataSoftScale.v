(* The clipping loss of the soft minimax of data scores
   (PaperMainDataSoftConcentration) at the scales of the proof. For
   d = S n, the operator bound is kappa / sqrt d, both inverse temperatures
   are A d sqrt d, the index lists are [0, r) and [0, s), the clipping
   level is U = d^(1/4) and the free parameter is a = d^6. Assume
   N <= C d^2, ln r <= H N and ln s <= H D, where D = d (d + 1) / 2 is the
   dimension of the symmetric matrices. Put
   M = 8 kappa^2 C^2 + 4 kappa^2 C + 2 (H (C + 1) / A)^2
   (paper_main_data_soft_scale_constant).
   - paper_main_data_soft_scaled_second: the second-moment bound
     paper_main_data_soft_second_bound is at most M d^4.
   - paper_main_data_soft_scaled_clipping: the clipping loss
     paper_main_data_soft_clipping_loss is at most
     M / d^2 + 2 C 38^19 / sqrt d.
   - paper_main_data_soft_scaled_clipping_large: for every eta > 0, the
     clipping loss is at most eta sqrt d for all large d. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainGaussianFeatureCoordinates PaperMainGaussianPsdWidthLimit
  PaperMainDataClippedGrowth PaperMainDataSoftConcentration PaperMainSoftClippingScale.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_data_soft_scale_constant kappa C H A :=
  8*kappa^2*C^2+4*kappa^2*C+2*(H*(C+1)/A)^2.

Lemma paper_main_data_soft_scale_constant_ge0 kappa C H A :
  0 <= C -> 0 <= paper_main_data_soft_scale_constant kappa C H A.
Proof.
move=> HC; rewrite /paper_main_data_soft_scale_constant.
have := pow2_ge_0 kappa; have := pow2_ge_0 C; have := pow2_ge_0 (H*(C+1)/A); nra.
Qed.

Theorem paper_main_data_soft_scaled_second n N r s kappa A C H :
  0 < A -> 0 <= C -> 0 <= H -> (0 < r)%coq_nat -> (0 < s)%coq_nat ->
  INR N <= C*(INR (S n))^2 ->
  Rpower.ln(INR r) <= H*INR N ->
  Rpower.ln(INR s) <= H*INR (paper_main_symmetric_dimension n) ->
  let d := INR (S n) in
  paper_main_data_soft_second_bound n N (kappa/sqrt d) (A*d*sqrt d) (A*d*sqrt d)
    (List.seq 0 r) (List.seq 0 s) <=
  paper_main_data_soft_scale_constant kappa C H A*d^4.
Proof.
move=> HA HC HH Hr Hs HN Hlr Hls d.
have Hd : 1 <= d by rewrite /d S_INR; have := pos_INR n; lra.
have Hd0 : 0 < d by lra.
have Hroot : 0 < sqrt d by exact: sqrt_lt_R0.
have Hb : 0 < A*d*sqrt d by repeat apply Rmult_lt_0_compat.
have Hrne : List.seq 0 r <> [].
{ move=> E; have := congr1 (@List.length nat) E; rewrite List.length_seq /=; lia. }
have Hsne : List.seq 0 s <> [].
{ move=> E; have := congr1 (@List.length nat) E; rewrite List.length_seq /=; lia. }
pose ent := paper_main_data_soft_entropy (A*d*sqrt d) (A*d*sqrt d) (List.seq 0 r) (List.seq 0 s).
have Hent0 : 0 <= ent by exact (paper_main_data_soft_entropy_ge0 (A*d*sqrt d) (A*d*sqrt d)
  (List.seq 0 r) (List.seq 0 s) Hb Hb Hrne Hsne).
have HE : 0 <= H*(C+1)/A.
{ unfold Rdiv; apply Rmult_le_pos; [nra|apply Rlt_le,Rinv_0_lt_compat; exact HA]. }
have HD : INR (paper_main_symmetric_dimension n) <= d^2.
{ rewrite paper_main_symmetric_dimension_real; fold d; nra. }
have Hent : ent <= (H*(C+1)/A)*sqrt d.
{ rewrite /ent /paper_main_data_soft_entropy !List.length_seq.
  exact: paper_main_soft_entropy_scale H C A d (INR N)
    (INR (paper_main_symmetric_dimension n)) (Rpower.ln(INR r)) (Rpower.ln(INR s))
    HH HC HA Hd0 HN HD Hlr Hls. }
have HV := paper_main_soft_second_scale kappa C (H*(C+1)/A) d (INR N) ent
  HC HE Hd (pos_INR N) HN Hent0 Hent.
rewrite /paper_main_data_soft_second_bound /paper_main_data_soft_scale_constant mult_INR.
fold d ent; exact HV.
Qed.

Theorem paper_main_data_soft_scaled_clipping n N r s kappa A C H :
  0 < A -> 0 <= C -> 0 <= H -> (0 < r)%coq_nat -> (0 < s)%coq_nat ->
  INR N <= C*(INR (S n))^2 ->
  Rpower.ln(INR r) <= H*INR N ->
  Rpower.ln(INR s) <= H*INR (paper_main_symmetric_dimension n) ->
  let d := INR (S n) in
  paper_main_data_soft_clipping_loss (sqrt(sqrt d)) n N (kappa/sqrt d)
    (A*d*sqrt d) (A*d*sqrt d) (List.seq 0 r) (List.seq 0 s) (d^6) <=
  paper_main_data_soft_scale_constant kappa C H A/d^2+2*C*38^19/sqrt d.
Proof.
move=> HA HC HH Hr Hs HN Hlr Hls d.
have Hd : 0 < d by unfold d; apply lt_0_INR; lia.
have HM := paper_main_data_soft_scale_constant_ge0 kappa C H A HC.
have HV := paper_main_data_soft_scaled_second n N r s kappa A C H HA HC HH Hr Hs HN Hlr Hls.
fold d in HV.
rewrite /paper_main_data_soft_clipping_loss (pow2_sqrt (sqrt d) (sqrt_pos d)).
exact: paper_main_soft_clipping_scale _ _ C (INR N) d HM HC Hd HN HV.
Qed.

Theorem paper_main_data_soft_scaled_clipping_large kappa A C H eta :
  0 < A -> 0 <= C -> 0 <= H -> 0 < eta ->
  exists D, forall n, Nat.le D n -> forall N r s,
    (0 < r)%coq_nat -> (0 < s)%coq_nat -> INR N <= C*(INR (S n))^2 ->
    Rpower.ln(INR r) <= H*INR N ->
    Rpower.ln(INR s) <= H*INR (paper_main_symmetric_dimension n) ->
    let d := INR (S n) in
    paper_main_data_soft_clipping_loss (sqrt(sqrt d)) n N (kappa/sqrt d)
      (A*d*sqrt d) (A*d*sqrt d) (List.seq 0 r) (List.seq 0 s) (d^6) <= eta*sqrt d.
Proof.
move=> HA HC HH He.
pose M := paper_main_data_soft_scale_constant kappa C H A.
have HM : 0 <= M by exact: paper_main_data_soft_scale_constant_ge0.
have [D HD] := INR_unbounded ((M+2*C*38^19)/eta).
exists D => n Hn N r s Hr Hs HN Hlr Hls d.
have Hd : 1 <= d by rewrite /d S_INR; have := pos_INR n; lra.
have HB := paper_main_data_soft_scaled_clipping n N r s kappa A C H HA HC HH Hr Hs HN Hlr Hls.
fold d M in HB.
have Hlarge : M+2*C*38^19 <= eta*d.
{ have HHN := le_INR D (S n) ltac:(lia).
  have Hratio : (M+2*C*38^19)/eta <= d by unfold d; lra.
  have HMUL := Rmult_le_compat_r eta _ _ (Rlt_le _ _ He) Hratio.
  replace ((M+2*C*38^19)/eta*eta) with (M+2*C*38^19) in HMUL by (field; lra).
  nra. }
have HL := paper_main_soft_clipping_margin M C eta d HM HC He Hd Hlarge.
lra.
Qed.
