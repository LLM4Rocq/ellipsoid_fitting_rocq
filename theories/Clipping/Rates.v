(* Elementary inequalities, with explicit constants, behind clipping the
   Gaussian coordinates at the threshold d^(1/4). Deterministic, at
   Stdlib's R.

   - paper_main_exp_polynomial_bound: x^n exp(-x/2) <= (2n)^n for n > 0 and
     x >= 0, from 1 + y <= exp y at y = x/(2n). At x = sqrt d it gives
     paper_main_sqrt_exponential_rate: d^k exp(-sqrt d/2) is at most
     (2(2k+1))^(2k+1) / sqrt d.
   - paper_main_coordinate_clipping_rate: if N <= C d^2, the union bound
     2 N d exp(-sqrt d/2) over the N d coordinates is at most
     2 C 14^7 / sqrt d. paper_main_clipping_mean_error_rate: if moreover
     V <= M d^4, then V/(2 d^6) plus d^6 times this union bound is at most
     M/(2 d^2) + 2 C 38^19 / sqrt d.
   - paper_main_log_eighth_root and paper_main_log_square_quarter_root:
     ln d <= 8 d^(1/8) and (ln d)^2 <= 64 d^(1/4) for d >= 1. Hence
     paper_main_clipped_head_entropy and paper_main_clipped_head_union_rate:
     once 128 C/c <= d^(1/4), the factor exp(C d (ln d)^2) costs at most
     half of the exponent of exp(-c d sqrt d).
   - paper_main_clipped_concentration_scale computes the exponent of a
     concentration bound at deviation c sqrt d for the Lipschitz constant
     2 (kappa/sqrt d) d^(1/4). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import ssreflect.
Open Scope R_scope.

Lemma paper_main_exp_nat_power x n : exp (INR n * x) = (exp x)^n.
Proof.
induction n as [|n IH].
- simpl; rewrite Rmult_0_l exp_0; reflexivity.
- rewrite S_INR Rmult_plus_distr_r exp_plus IH Rmult_1_l.
  simpl; ring.
Qed.

Lemma paper_main_exp_polynomial_bound n x :
  (0 < n)%nat -> 0 <= x -> x^n * exp(-x/2) <= (2*INR n)^n.
Proof.
intros Hn Hx.
assert (HnR : 0 < INR n) by (apply lt_0_INR; exact Hn).
assert (Hc : 0 < 2*INR n) by lra.
assert (Hdiv : 0 <= x/(2*INR n)) by (unfold Rdiv; apply Rmult_le_pos; [exact Hx | apply Rlt_le, Rinv_0_lt_compat; exact Hc]).
pose proof (exp_ineq1_le (x/(2*INR n))) as Hexp.
assert (Hle : x/(2*INR n) <= exp(x/(2*INR n))) by lra.
pose proof (pow_incr (x/(2*INR n)) (exp(x/(2*INR n))) n (conj Hdiv Hle)) as Hpow.
assert (HE : (exp(x/(2*INR n)))^n = exp(x/2)).
{ rewrite <- paper_main_exp_nat_power; f_equal; field; lra. }
rewrite HE in Hpow.
assert (HC0 : 0 <= (2*INR n)^n) by (apply pow_le; lra).
pose proof (Rmult_le_compat_l ((2*INR n)^n) _ _ HC0 Hpow) as Hscale.
assert (HS : (2*INR n)^n * (x/(2*INR n))^n = x^n).
{ rewrite <- Rpow_mult_distr; f_equal; field; lra. }
rewrite HS in Hscale.
pose proof (exp_pos(-x/2)) as Hpos.
pose proof (Rmult_le_compat_r (exp(-x/2)) _ _ (Rlt_le _ _ Hpos) Hscale) as HM.
assert (Hinv : exp(x/2)*exp(-x/2) = 1).
{ rewrite <- exp_plus; replace (x/2 + -x/2) with 0 by field; apply exp_0. }
rewrite Rmult_assoc Hinv Rmult_1_r in HM; exact HM.
Qed.

Lemma paper_main_sqrt_odd_power k d :
  0 <= d -> (sqrt d)^(S (2*k)) = d^k*sqrt d.
Proof.
intro Hd; induction k as [|k IH].
- simpl; ring.
- replace (S (2*S k)) with (S (S (S (2*k)))) by lia.
  change (sqrt d*(sqrt d*(sqrt d)^(S (2*k))) = d*d^k*sqrt d).
  rewrite IH.
  pose proof (pow2_sqrt d Hd) as Hs; nra.
Qed.

Lemma paper_main_sqrt_exponential_rate k d :
  0 < d ->
  d^k * exp(-sqrt d/2) <= (2*INR (S (2*k)))^(S (2*k))/sqrt d.
Proof.
intro Hd.
pose proof (sqrt_lt_R0 d Hd) as Hs.
pose proof (paper_main_exp_polynomial_bound (S (2*k)) (sqrt d) ltac:(lia)
  (Rlt_le _ _ Hs)) as HB.
rewrite (paper_main_sqrt_odd_power k d (Rlt_le _ _ Hd)) in HB.
apply (Rmult_le_reg_r (sqrt d)); [exact Hs|].
replace (((2*INR (S (2*k)))^(S (2*k))/sqrt d)*sqrt d)
  with ((2*INR (S (2*k)))^(S (2*k))) by (field; lra).
nra.
Qed.

Lemma paper_main_coordinate_clipping_scale d :
  0 < d -> (sqrt (sqrt d))^2 = sqrt d /\
    0 < sqrt (sqrt d).
Proof.
intro Hd; split.
- apply pow2_sqrt, sqrt_pos.
- apply sqrt_lt_R0, sqrt_lt_R0; exact Hd.
Qed.

Lemma paper_main_clipped_concentration_scale d kappa c :
  0 < d -> 0 < kappa ->
  (c*sqrt d)^2/(2*(2*(kappa/sqrt d)*sqrt(sqrt d))^2) =
    c^2*d*sqrt d/(8*kappa^2).
Proof.
intros Hd Hk.
pose proof (sqrt_lt_R0 d Hd) as Hs.
pose proof (sqrt_lt_R0 (sqrt d) Hs) as Ht.
pose proof (pow2_sqrt d (Rlt_le _ _ Hd)) as Hsd.
pose proof (pow2_sqrt (sqrt d) (Rlt_le _ _ Hs)) as Hts.
remember (sqrt d) as s eqn:Es in *.
remember (sqrt s) as t eqn:Et in *.
replace d with (s*s) by nra.
replace s with (t*t) by nra.
field; repeat split; lra.
Qed.

Lemma paper_main_log_eighth_root d :
  1 <= d -> 0 <= ln d <= 8*sqrt(sqrt(sqrt d)).
Proof.
intro Hd.
assert (Hd0 : 0 < d) by lra.
pose proof (sqrt_lt_R0 d Hd0) as Hs.
pose proof (sqrt_lt_R0 (sqrt d) Hs) as Ht.
pose proof (sqrt_lt_R0 (sqrt(sqrt d)) Ht) as Hr.
pose proof (pow2_sqrt d (Rlt_le _ _ Hd0)) as Hsd.
pose proof (pow2_sqrt (sqrt d) (Rlt_le _ _ Hs)) as Hts.
pose proof (pow2_sqrt (sqrt(sqrt d)) (Rlt_le _ _ Ht)) as Hrt.
remember (sqrt d) as s eqn:Es in *.
remember (sqrt s) as t eqn:Et in *.
remember (sqrt t) as r eqn:Er in *.
assert (HE : r^8 = d).
{ rewrite -Hsd -Hts -Hrt; ring. }
pose proof (exp_ineq1_le (ln r)) as Hlog.
rewrite (exp_ln r Hr) in Hlog.
pose proof (ln_pow r Hr 8) as Hpow.
assert (E8 : INR 8 = 8) by (simpl; ring).
rewrite HE E8 in Hpow.
split.
- destruct (Rle_lt_or_eq_dec _ _ Hd) as [Hgt|Heq].
  + rewrite <- ln_1; left; apply ln_increasing; lra.
  + rewrite -Heq ln_1; lra.
- lra.
Qed.

Lemma paper_main_log_square_quarter_root d :
  1 <= d -> (ln d)^2 <= 64*sqrt(sqrt d).
Proof.
intro Hd.
pose proof (paper_main_log_eighth_root d Hd) as Hlog.
pose proof (sqrt_pos (sqrt(sqrt d))) as Hr.
pose proof (pow2_sqrt (sqrt(sqrt d)) (sqrt_pos (sqrt d))) as Hsq.
nra.
Qed.

Lemma paper_main_clipped_head_entropy C c d :
  0 <= C -> 0 < c -> 1 <= d ->
  128*C/c <= sqrt(sqrt d) ->
  C*d*(ln d)^2 - c*d*sqrt d <= -c*d*sqrt d/2.
Proof.
intros HC Hc Hd Hlarge.
pose proof (paper_main_log_square_quarter_root d Hd) as Hlog.
pose proof (sqrt_pos (sqrt d)) as Ht.
pose proof (pow2_sqrt (sqrt d) (sqrt_pos d)) as Hts.
assert (Hscale : 128*C <= c*sqrt(sqrt d)).
{ apply (Rmult_le_reg_r (/c)); [apply Rinv_0_lt_compat; exact Hc|].
  replace (c*sqrt(sqrt d)*/c) with (sqrt(sqrt d)) by (field; lra).
  exact Hlarge. }
assert (Hlogscale : C*d*(ln d)^2 <= 64*C*d*sqrt(sqrt d)).
{ pose proof (Rmult_le_compat_l (C*d) _ _ ltac:(nra) Hlog); nra. }
pose proof (Rmult_le_compat_r (d*sqrt(sqrt d)) _ _ ltac:(nra) Hscale) as Hprod.
nra.
Qed.

Lemma paper_main_clipped_head_union_rate C c d :
  0 <= C -> 0 < c -> 1 <= d ->
  128*C/c <= sqrt(sqrt d) ->
  exp(C*d*(ln d)^2)*exp(-c*d*sqrt d) <= exp(-c*d*sqrt d/2).
Proof.
intros HC Hc Hd Hlarge; rewrite <- exp_plus.
pose proof (paper_main_clipped_head_entropy C c d HC Hc Hd Hlarge) as HB.
assert (HE : C*d*(ln d)^2 + -c*d*sqrt d <= -c*d*sqrt d/2) by lra.
destruct (Rle_lt_or_eq_dec _ _ HE) as [Hlt|Heq].
- left; apply exp_increasing; exact Hlt.
- rewrite Heq; right; reflexivity.
Qed.

Lemma paper_main_coordinate_clipping_rate C N d :
  0 <= C -> 0 < d -> N <= C*d^2 ->
  2*N*d*exp(-sqrt d/2) <= 2*C*14^7/sqrt d.
Proof.
intros HC Hd HN.
pose proof (paper_main_sqrt_exponential_rate 3 d Hd) as HB.
assert (EC : (2*INR (S (2*3)))^(S (2*3)) = 14^7) by (simpl; ring).
rewrite EC in HB.
pose proof (sqrt_lt_R0 d Hd) as Hs.
pose proof (exp_pos(-sqrt d/2)) as He.
pose proof (Rmult_le_compat_r (2*d*exp(-sqrt d/2)) _ _ ltac:(nra) HN) as HM.
pose proof (Rmult_le_compat_l (2*C) _ _ ltac:(lra) HB) as HR.
unfold Rdiv in *; nra.
Qed.

Lemma paper_main_clipping_mean_error_rate V M C N d :
  0 <= M -> 0 <= C -> 0 < d -> N <= C*d^2 -> V <= M*d^4 ->
  V/(2*d^6) + d^6*(2*N*d*exp(-sqrt d/2)) <=
    M/(2*d^2) + 2*C*38^19/sqrt d.
Proof.
intros HM HC Hd HN HV.
assert (HD6 : 0 < 2*d^6) by (apply Rmult_lt_0_compat; [lra|apply pow_lt; exact Hd]).
assert (HVrate : V/(2*d^6) <= M/(2*d^2)).
{ apply (Rmult_le_reg_r (2*d^6)); [exact HD6|].
  replace (V/(2*d^6)*(2*d^6)) with V by (field; lra).
  replace (M/(2*d^2)*(2*d^6)) with (M*d^4) by (field; lra).
  exact HV. }
pose proof (paper_main_sqrt_exponential_rate 9 d Hd) as HB.
assert (EC : (2*INR (S (2*9)))^(S (2*9)) = 38^19) by (simpl; ring).
rewrite EC in HB.
pose proof (exp_pos(-sqrt d/2)) as He.
assert (Hfac : 0 <= 2*d^7*exp(-sqrt d/2)).
{ apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow_le; lra]|lra]. }
pose proof (Rmult_le_compat_r (2*d^7*exp(-sqrt d/2)) _ _ Hfac HN) as HNrate.
pose proof (Rmult_le_compat_l (2*C) _ _ ltac:(lra) HB) as HCbound.
assert (Hterm : d^6*(2*N*d*exp(-sqrt d/2)) <= 2*C*38^19/sqrt d).
{ eapply Rle_trans.
  - replace (d^6*(2*N*d*exp(-sqrt d/2))) with (N*(2*d^7*exp(-sqrt d/2))) by ring.
    exact HNrate.
  - replace (C*d^2*(2*d^7*exp(-sqrt d/2))) with (2*C*(d^9*exp(-sqrt d/2))) by ring.
    unfold Rdiv in *; nra. }
lra.
Qed.
