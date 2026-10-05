(* Scalar bounds, with explicit constants, for the soft minimax of the data
   features at inverse temperature A d sqrt d and for its clipping error.
   Deterministic, at Stdlib's R.
   - paper_main_soft_entropy_scale: if q <= C d^2, D <= d^2 and the log
     cardinalities satisfy lr <= E q and ls <= E D, then
     lr/(A d sqrt d) + ls/(A d sqrt d) <= (E (C + 1)/A) sqrt d.
   - paper_main_soft_second_scale: for N <= C d^2 and an entropy term at
     most E sqrt d, the second moment bound 2 c^2 (4 D^2 + 2 D) + 2 C'^2 of
     paper_main_data_growth_law, at c = kappa/d, D = N d and C' the entropy
     term, is at most (8 kappa^2 C^2 + 4 kappa^2 C + 2 E^2) d^4.
   - paper_main_soft_clipping_scale: for a variance V <= M d^4 and
     N <= C d^2, V/d^6 plus the clipping error d^6 (2 N d exp(-sqrt d/2))
     is at most M/d^2 + 2 C 38^19/sqrt d, by
     paper_main_clipping_mean_error_rate.
   - paper_main_soft_clipping_margin: this is at most eta sqrt d once
     M + 2 C 38^19 <= eta d. *)
From Stdlib Require Import Reals Lia Lra Psatz.
From mathcomp Require Import ssreflect.
From EllipsoidFitting Require Import PaperMainClippingRates.
Open Scope R_scope.

Lemma paper_main_soft_entropy_scale E C A d q D lr ls :
  0 <= E -> 0 <= C -> 0 < A -> 0 < d ->
  q <= C*d^2 -> D <= d^2 -> lr <= E*q -> ls <= E*D ->
  lr/(A*d*sqrt d)+ls/(A*d*sqrt d) <= (E*(C+1)/A)*sqrt d.
Proof.
intros HE HC HA Hd Hq HD Hlr Hls.
pose proof (sqrt_lt_R0 d Hd) as Hs.
pose proof (pow2_sqrt d (Rlt_le _ _ Hd)) as Hs2.
assert (Hden : 0 < A*d*sqrt d) by (repeat apply Rmult_lt_0_compat; assumption).
apply (Rmult_le_reg_r (A*d*sqrt d)); [exact Hden|].
replace ((lr/(A*d*sqrt d)+ls/(A*d*sqrt d))*(A*d*sqrt d)) with (lr+ls) by (field; lra).
replace ((E*(C+1)/A)*sqrt d*(A*d*sqrt d)) with (E*(C+1)*d*(sqrt d)^2) by (field; lra).
rewrite Hs2.
pose proof (Rmult_le_compat_l E _ _ HE Hq).
pose proof (Rmult_le_compat_l E _ _ HE HD).
nra.
Qed.

Lemma paper_main_soft_second_scale kappa C E d N entropy :
  0 <= C -> 0 <= E -> 1 <= d -> 0 <= N -> N <= C*d^2 ->
  0 <= entropy -> entropy <= E*sqrt d ->
  2*(kappa/sqrt d/sqrt d)^2*(4*(N*d)^2+2*(N*d))+2*entropy^2 <=
    (8*kappa^2*C^2+4*kappa^2*C+2*E^2)*d^4.
Proof.
intros HC HE Hd HN0 HN Hent0 Hent.
assert (Hd0 : 0 < d) by lra.
pose proof (sqrt_lt_R0 d Hd0) as Hs.
pose proof (pow2_sqrt d (Rlt_le _ _ Hd0)) as Hs2.
assert (Hsprod : sqrt d*sqrt d=d) by nra.
assert (Hcoef : kappa/sqrt d/sqrt d=kappa/d).
{ replace (kappa/d) with (kappa/(sqrt d*sqrt d)) by (rewrite Hsprod; reflexivity).
  field; lra. }
rewrite Hcoef.
replace (2*(kappa/d)^2*(4*(N*d)^2+2*(N*d))+2*entropy^2) with
  (8*kappa^2*N^2+4*kappa^2*(N/d)+2*entropy^2) by (field; lra).
assert (HN2 : N^2 <= C^2*d^4).
{ pose proof (pow_incr N (C*d^2) 2 (conj HN0 HN)) as HH.
  replace ((C*d^2)^2) with (C^2*d^4) in HH by ring; exact HH. }
assert (HNdiv : N/d <= C*d).
{ apply (Rmult_le_reg_r d); [exact Hd0|].
  replace (N/d*d) with N by (field; lra); nra. }
assert (Hent2 : entropy^2 <= E^2*d).
{ pose proof (pow_incr entropy (E*sqrt d) 2 (conj Hent0 Hent)) as HH.
  rewrite Rpow_mult_distr Hs2 in HH; exact HH. }
assert (Hd4 : d <= d^4).
{ assert (1 <= d^3) by (apply pow_R1_Rle; lra).
  nra. }
pose proof (pow2_ge_0 kappa) as HK2.
pose proof (pow2_ge_0 E) as HE2.
pose proof (Rmult_le_compat_l (8*kappa^2) _ _ ltac:(nra) HN2) as H1.
pose proof (Rmult_le_compat_l (4*kappa^2) _ _ ltac:(nra) HNdiv) as H2.
pose proof (Rmult_le_compat_l (4*kappa^2*C+2*E^2) _ _ ltac:(nra) Hd4) as H3.
nra.
Qed.

Lemma paper_main_soft_clipping_scale V M C N d :
  0 <= M -> 0 <= C -> 0 < d -> N <= C*d^2 -> V <= M*d^4 ->
  V/d^6+d^6*(2*N*d*exp(-sqrt d/2)) <=
    M/d^2+2*C*38^19/sqrt d.
Proof.
intros HM HC Hd HN HV.
pose proof (paper_main_clipping_mean_error_rate (2*V) (2*M) C N d
  ltac:(lra) HC Hd HN ltac:(nra)) as HH.
replace (2*V/(2*d^6)) with (V/d^6) in HH by (field; lra).
replace (2*M/(2*d^2)) with (M/d^2) in HH by (field; lra).
exact HH.
Qed.

Lemma paper_main_soft_clipping_margin M C eta d :
  0 <= M -> 0 <= C -> 0 < eta -> 1 <= d ->
  M+2*C*38^19 <= eta*d ->
  M/d^2+2*C*38^19/sqrt d <= eta*sqrt d.
Proof.
intros HM HC He Hd Hlarge.
assert (Hd0 : 0 < d) by lra.
pose proof (sqrt_lt_R0 d Hd0) as Hs.
pose proof (pow2_sqrt d (Rlt_le _ _ Hd0)) as Hs2.
assert (Hsd1 : sqrt d <= d) by nra.
assert (Hsd : sqrt d <= d^2) by nra.
assert (Hratio : M*sqrt d/d^2 <= M).
{ apply (Rmult_le_reg_r (d^2)); [apply pow_lt; exact Hd0|].
  replace (M*sqrt d/d^2*d^2) with (M*sqrt d) by (field; lra).
  exact: Rmult_le_compat_l M _ _ HM Hsd. }
apply (Rmult_le_reg_r (sqrt d)); [exact Hs|].
replace ((M/d^2+2*C*38^19/sqrt d)*sqrt d) with
  (M*sqrt d/d^2+2*C*38^19) by (field; lra).
replace (eta*sqrt d*sqrt d) with (eta*(sqrt d)^2) by ring.
rewrite Hs2.
lra.
Qed.
