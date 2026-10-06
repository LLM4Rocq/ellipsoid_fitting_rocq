(* A logarithmic coherence bound for all pairs of head features of the
   sample. The threshold is B_d = sqrt(64 d ln d)
   (paper_main_coherence_threshold), for which exp(-B_d^2 / (8 d)) = d^-8
   (paper_main_coherence_threshold_scale). The coherence event of
   PaperMainDataSampleTail at B_d says that some pair i < j < N has
   |x_i|^2 <= 4 d and |<x_i, x_j>| >= B_d.
   - paper_main_data_coherence_log_tail: for d > 1 it is measurable with
     probability at most 2 N^2 / d^8.
   - paper_main_data_coherence_log_tends_to_zero: if N(d) <= C d^2 for all
     large d, its probability tends to 0, since 2 N^2 / d^8 <=
     2 C^2 / sqrt d (paper_main_data_coherence_log_rate).
   - paper_main_data_coherence_log_good: outside it, if ln d >= 1 and
     |x_k|^2 <= 4 d for every k < N, the head features of two distinct
     points satisfy |<W_i, W_j>| <= 64 ln d + 9 <= 73 ln d. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import matrix.
From EllipsoidFitting Require Import AnalysisBridge PaperMainDefinitions
  PaperMainGeometryPsd PaperMainGeometryHeadFeature
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDataSampleTail PaperMainClippingRates PaperMainClippingLimits.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

Definition paper_main_coherence_threshold d := sqrt(64*d*Rpower.ln d).

Lemma paper_main_coherence_threshold_scale d :
  1 < d -> 0 < paper_main_coherence_threshold d /\
    (paper_main_coherence_threshold d)^2 = 64*d*Rpower.ln d /\
    exp(-(paper_main_coherence_threshold d)^2/(8*d)) = /(d^8).
Proof.
move=> Hd.
have Hln : 0 < Rpower.ln d by rewrite -ln_1; apply ln_increasing; lra.
have Hpos : 0 < 64*d*Rpower.ln d by nra.
have Hr : 0 < paper_main_coherence_threshold d by apply sqrt_lt_R0.
have HE : (paper_main_coherence_threshold d)^2 = 64*d*Rpower.ln d by apply pow2_sqrt; lra.
split; first exact Hr; split; first exact HE.
rewrite HE.
replace (-(64*d*Rpower.ln d)/(8*d)) with (-(8*Rpower.ln d)) by (field; lra).
rewrite exp_Ropp.
have H8 : INR 8 = 8 by simpl; ring.
rewrite -H8 paper_main_exp_nat_power (exp_ln d ltac:(lra)).
reflexivity.
Qed.

Theorem paper_main_data_coherence_log_tail N d :
  1 < INR d ->
  measurable (paper_main_data_coherence_event N d (paper_main_coherence_threshold (INR d))) /\
  (paper_main_probability N d (paper_main_data_coherence_event N d (paper_main_coherence_threshold (INR d))) <=
    (2*(INR N)^2/(INR d)^8)%Rcoq%:E)%E.
Proof.
move=> Hd.
have HdN : (0 < d)%N by apply/ssrnat.ltP; have HH : (INR 1 < INR d) := Hd; apply INR_lt in HH; lia.
have [Hr [HE Hexp]] := paper_main_coherence_threshold_scale (INR d) Hd.
have [HM HB] := paper_main_data_coherence_tail N d (paper_main_coherence_threshold (INR d)) HdN Hr.
split; first exact HM.
rewrite Hexp in HB.
apply: le_trans HB _; rewrite lee_fin; apply/RleP; rewrite -!RmultE.
change (2*INR N*INR N*/(INR d)^8 <= 2*(INR N)^2/(INR d)^8).
unfold Rdiv; right; ring.
Qed.

Lemma paper_main_data_coherence_log_rate C N d :
  0 <= C -> 0 <= N -> 1 <= d -> N <= C*d^2 ->
  2*N^2/d^8 <= (2*C^2)/sqrt d.
Proof.
move=> HC HN Hd Hbound.
have Hs : 0 < sqrt d by apply sqrt_lt_R0; lra.
have Hsq := pow2_sqrt d ltac:(lra).
have Hds : sqrt d <= d by nra.
have Hdp : d <= d^4.
{ have H2 : d <= d^2 by nra.
  have H4 : d^2 <= d^4 by nra.
  lra. }
have Hcoef : N^2 <= C^2*d^4 by nra.
have Hdp0 : 0 < d^4 by apply pow_lt; lra.
have Hpow0 : 0 < d^8 by apply pow_lt; lra.
apply (Rmult_le_reg_r (d^8*sqrt d)); first nra.
replace (2*N^2/d^8*(d^8*sqrt d)) with (2*N^2*sqrt d) by (field; lra).
replace (2*C^2/sqrt d*(d^8*sqrt d)) with (2*C^2*d^8) by (field; lra).
have HM := Rmult_le_compat_r (sqrt d) _ _ ltac:(lra) Hcoef.
have Hsd4 : sqrt d <= d^4 by lra.
have HC4 : 0 <= C^2*d^4 by nra.
have HP := Rmult_le_compat_l (C^2*d^4) _ _ HC4 Hsd4.
replace (d^8) with (d^4*d^4) by ring.
nra.
Qed.

Theorem paper_main_data_coherence_log_tends_to_zero (N : nat -> nat) C :
  0 <= C ->
  (exists D, forall d, Nat.le D d -> INR (N d) <= C*(INR d)^2) ->
  paper_main_tends_to (fun d => paper_main_probability (N d) d
    (paper_main_data_coherence_event (N d) d (paper_main_coherence_threshold (INR d)))) 0.
Proof.
move=> HC [D HD].
apply: (paper_main_sqrt_rate_tends_to_zero _ (2*C^2)); first nra.
- move=> d; exact: measure_ge0.
- exists (Nat.max D 2) => d Hdd.
  have Hd : 1 < INR d by change (INR 1 < INR d); apply lt_INR; lia.
  have [_ HB] := paper_main_data_coherence_log_tail (N d) d Hd.
  apply: le_trans HB _; rewrite lee_fin; apply/RleP.
  exact: (paper_main_data_coherence_log_rate C (INR (N d)) (INR d) HC (pos_INR _) ltac:(lra) (HD d ltac:(lia))).
Qed.

Theorem paper_main_data_coherence_log_good N d (x : paper_main_sample N d) :
  1 < INR d -> 1 <= Rpower.ln(INR d) ->
  (forall k, Nat.lt k N ->
    Rle (((paper_main_point x k)^T *m paper_main_point x k) ord0 ord0)%R (4*INR d)) ->
  ~ paper_main_data_coherence_event N d (paper_main_coherence_threshold (INR d)) x ->
  forall i j, Nat.lt i N -> Nat.lt j N -> i <> j ->
    Rabs (paper_main_pairing (paper_main_head_feature x i) (paper_main_head_feature x j)) <= 73*Rpower.ln(INR d).
Proof.
move=> Hd Hln Hrad Hgood i j Hi Hj Hij.
have HdN : (0 < d)%N by apply/ssrnat.ltP; have HH : (INR 1 < INR d) := Hd; apply INR_lt in HH; lia.
have [_ [HE _]] := paper_main_coherence_threshold_scale (INR d) Hd.
have HB := paper_main_data_coherence_good N d x (paper_main_coherence_threshold (INR d)) HdN Hrad Hgood i j Hi Hj Hij.
rewrite HE in HB.
replace (64*INR d*Rpower.ln(INR d)/INR d) with (64*Rpower.ln(INR d)) in HB by (field; lra).
lra.
Qed.
