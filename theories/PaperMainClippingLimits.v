(* Vanishing probabilities for the explicit coordinate clipping choice d^(1/4). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 PaperMainDefinitions PaperMainAsymptotics
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDataSampleTail PaperMainClippingRates.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

Theorem paper_main_sqrt_rate_tends_to_zero (p : nat -> \bar R) C :
  0 <= C -> (forall d, (0 <= p d)%E) ->
  (exists D, forall d, Nat.le D d -> (p d <= ((C/sqrt(INR d))%Rcoq)%:E)%E) ->
  paper_main_tends_to p 0.
Proof.
move=> HC Hp [D HD] eps Heps.
have HepsR : 0 < eps by exact/RltP.
have [K HK] := INR_unbounded ((C/eps)^2).
exists (Nat.max D (S K)) => d Hdd.
have HddN : Nat.le (Nat.max D (S K)) d by exact: (elimT ssrnat.leP Hdd).
have Hd : 0 < INR d by apply lt_0_INR; lia.
have Hs : 0 < sqrt(INR d) by apply sqrt_lt_R0.
have Hsq := pow2_sqrt (INR d) (pos_INR d).
have Hlarge : (C/eps)^2 < INR d by have := le_INR K d ltac:(lia); lra.
have Hdiv : 0 <= C/eps.
{ apply Rmult_le_pos; first exact HC; apply Rlt_le,Rinv_0_lt_compat; exact HepsR. }
have Hroot : C/eps < sqrt(INR d) by nra.
have Hmul := Rmult_lt_compat_r eps _ _ HepsR Hroot.
replace (C/eps*eps) with C in Hmul by (field; lra).
have Hrate : C/sqrt(INR d) < eps.
{ apply (Rmult_lt_reg_r (sqrt(INR d))); first exact Hs.
  replace (C/sqrt(INR d)*sqrt(INR d)) with C by (field; lra).
  lra. }
have HB := HD d ltac:(lia).
rewrite sube0 (gee0_abs (Hp d)).
apply: le_lt_trans HB _; rewrite lte_fin; apply/RltP; exact Hrate.
Qed.

Theorem paper_main_sqrt_polynomial_tends_to_zero (p : nat -> \bar R) C k :
  0 <= C -> (forall d, (0 <= p d)%E) ->
  (exists D, forall d, Nat.le D d ->
    (p d <= ((C*(INR d)^k*exp(-sqrt(INR d)/2))%Rcoq)%:E)%E) ->
  paper_main_tends_to p 0.
Proof.
move=> HC Hp [D HD].
pose A := (2*INR (S (2*k)))^(S (2*k)).
have HA : 0 <= A by apply pow_le; have := pos_INR (S (2*k)); lra.
apply: (paper_main_sqrt_rate_tends_to_zero p (C*A)) => //.
- exact: Rmult_le_pos.
- exists (S D) => d Hdd.
  have Hd : 0 < INR d by apply lt_0_INR; lia.
  have HB := paper_main_sqrt_exponential_rate k (INR d) Hd.
  have HM := Rmult_le_compat_l C _ _ HC HB.
  apply: (le_trans (HD d ltac:(lia))).
  rewrite lee_fin; apply/RleP.
  change (C*(INR d)^k*exp(-sqrt(INR d)/2) <= C*A/sqrt(INR d)).
  fold A in HM.
  unfold Rdiv in HM |- *.
  rewrite !Rmult_assoc in HM |- *.
  exact HM.
Qed.

Theorem paper_main_coordinate_clipping_tends_to_zero (N : nat -> nat) C :
  0 <= C ->
  (exists D, forall d, Nat.le D d -> INR (N d) <= C*(INR d)^2) ->
  paper_main_tends_to
    (fun d => paper_main_probability (N d) d
      (paper_main_data_coordinate_event (N d) d (sqrt(sqrt(INR d))))) 0.
Proof.
move=> HC [D HD].
apply: (paper_main_sqrt_rate_tends_to_zero _ (2*C*14^7)).
- apply Rmult_le_pos; first lra; apply pow_le; lra.
- move=> d; exact: measure_ge0.
- exists (S D) => d Hdd.
  have Hd : 0 < INR d by apply lt_0_INR; lia.
  have [HU2 HU] := paper_main_coordinate_clipping_scale (INR d) Hd.
  have [_ HB] := paper_main_data_coordinate_tail (N d) d (sqrt(sqrt(INR d))) HU.
  rewrite HU2 in HB.
  have HR := paper_main_coordinate_clipping_rate C (INR (N d)) (INR d) HC Hd (HD d ltac:(lia)).
  apply: (le_trans HB); rewrite lee_fin; apply/RleP; exact HR.
Qed.

Lemma paper_main_clipped_head_tail_rate c d :
  0 < c -> 1 <= d -> exp(-c*d*sqrt d/2) <= (2/c)/sqrt d.
Proof.
move=> Hc Hd.
have Hs : 0 < sqrt d by apply sqrt_lt_R0; lra.
pose t := c*d*sqrt d/2.
have HE := exp_ineq1_le t.
have Hp := exp_pos (-t).
have Hinv : exp t * exp(-t) = 1.
{ rewrite -exp_plus; replace (t + -t) with 0 by ring; exact exp_0. }
have HM := Rmult_le_compat_r (exp(-t)) _ _ (Rlt_le _ _ Hp) HE.
have Hcs : 0 <= c*sqrt d by nra.
have Hprod := Rmult_le_compat_l (c*sqrt d) _ _ Hcs Hd.
have Htd : c*sqrt d/2 <= t by unfold t; nra.
have HR := Rmult_le_compat_r (exp(-t)) _ _ (Rlt_le _ _ Hp) Htd.
replace (-c*d*sqrt d/2) with (-t) by (unfold t; field).
apply (Rmult_le_reg_r (c*sqrt d)); first nra.
replace ((2/c)/sqrt d*(c*sqrt d)) with 2 by (field; split; lra).
nra.
Qed.

Theorem paper_main_clipped_head_union_tends_to_zero (p : nat -> \bar R) C c :
  0 <= C -> 0 < c -> (forall d, (0 <= p d)%E) ->
  (exists D, forall d, Nat.le D d ->
    (p d <= ((exp(C*INR d*(Rpower.ln (INR d))^2)*
      exp(-c*INR d*sqrt(INR d)))%Rcoq)%:E)%E) ->
  paper_main_tends_to p 0.
Proof.
move=> HC Hc Hp [D HD].
pose a := 128*C/c.
have Ha : 0 <= a.
{ unfold a,Rdiv; apply Rmult_le_pos; first lra; apply Rlt_le,Rinv_0_lt_compat; exact Hc. }
have [K HK] := INR_unbounded (a^4).
apply: (paper_main_sqrt_rate_tends_to_zero p (2/c)) => //.
- apply Rmult_le_pos; first lra; apply Rlt_le,Rinv_0_lt_compat; exact Hc.
- exists (Nat.max (S D) K) => d Hdd.
  have Hd : 1 <= INR d.
  { have H := le_INR 1 d ltac:(lia); exact H. }
  have Hlarge : a^4 < INR d by have := le_INR K d ltac:(lia); lra.
  have Hroot : a <= sqrt(sqrt(INR d)).
  { have Hs := sqrt_pos (INR d).
    have Hr := sqrt_pos (sqrt(INR d)).
    have Hss := pow2_sqrt (INR d) (pos_INR d).
    have Hrr := pow2_sqrt (sqrt(INR d)) Hs.
    have HE : (sqrt(sqrt(INR d)))^4 = INR d by nra.
    case: (Rle_dec a (sqrt(sqrt(INR d)))) => H; first exact H.
    have HH : 0 <= sqrt(sqrt(INR d)) <= a by split; lra.
    have HP := pow_incr _ _ 4 HH.
    rewrite HE in HP; lra. }
  have Hunion := paper_main_clipped_head_union_rate C c (INR d) HC Hc Hd Hroot.
  have Hrate := paper_main_clipped_head_tail_rate c (INR d) Hc Hd.
  apply: (le_trans (HD d ltac:(lia))).
  rewrite lee_fin; apply/RleP.
  exact: Rle_trans Hunion Hrate.
Qed.
