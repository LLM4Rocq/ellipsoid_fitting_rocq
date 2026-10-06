(* Elementary logarithmic inequalities for the bound on the Gram matrix of
   the raw head and data features that holds simultaneously for every head
   of at most K d ln d sample points (paper_main_head_data_log_event).
   Deterministic, at Stdlib's R.
   - paper_main_log_successor_bound: 0 <= ln(x + 1) <= x for x >= 0.
   - paper_main_log_quadratic_count: if N <= C d^2 and d >= 1, then
     ln(N + 1) <= ln(C + 1) + 2 ln d, which is at most (ln(C + 1) + 2) ln d
     when ln d >= 1 (paper_main_log_quadratic_count_coarse).
   - paper_main_head_data_budget: the integer paper_main_gordon_ceiling of
     K d ln d lies in the interval (K d ln d, (K + 1) d ln d].
   - paper_main_head_data_operator_rate: for N <= C d^2 and k <= K d ln d,
     8 (E (d + k) + ln(k + 1) + k ln(N + 1) + ln d) is at most an explicit
     constant times d (ln d)^2.
   - paper_main_head_data_tail_rate: 2 exp(-ln d) = 2/d <= 2/sqrt d. *)
From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import Gordon.Quantization.
Open Scope R_scope.

Lemma paper_main_log_successor_bound x :
  0 <= x -> 0 <= ln(x+1) <= x.
Proof.
intro Hx.
assert (Hp : 0 < x+1) by lra.
pose proof (exp_ineq1_le (ln(x+1))) as HE.
rewrite (exp_ln _ Hp) in HE.
split; [|lra].
destruct (Req_dec x 0) as [->|Hne].
- rewrite Rplus_0_l,ln_1; lra.
- rewrite <- ln_1; left; apply ln_increasing; lra.
Qed.

Lemma paper_main_log_quadratic_count C N d :
  0 <= C -> 0 <= N -> 1 <= d -> N <= C*d^2 ->
  ln(N+1) <= ln(C+1)+2*ln d.
Proof.
intros HC HN Hd Hbound.
assert (Harg : N+1 <= (C+1)*d^2) by nra.
assert (Hlarge : 0 < (C+1)*d^2) by nra.
assert (Hlog : ln(N+1) <= ln((C+1)*d^2)).
{ destruct (Rle_lt_or_eq_dec _ _ Harg) as [Hlt|Heq].
  - left; apply ln_increasing; lra.
  - rewrite Heq; right; reflexivity. }
rewrite ln_mult in Hlog; try nra.
rewrite ln_pow in Hlog; try lra.
assert (E2 : INR 2 = 2) by (simpl; ring).
rewrite E2 in Hlog; exact Hlog.
Qed.

Lemma paper_main_log_quadratic_count_coarse C N d :
  0 <= C -> 0 <= N -> 1 <= d -> 1 <= ln d -> N <= C*d^2 ->
  ln(N+1) <= (ln(C+1)+2)*ln d.
Proof.
intros HC HN Hd Hlog Hbound.
pose proof (paper_main_log_quadratic_count C N d HC HN Hd Hbound) as HB.
pose proof (paper_main_log_successor_bound C HC) as HC1.
nra.
Qed.

Lemma paper_main_head_data_budget K d :
  0 <= K -> 1 <= d -> 1 <= ln d ->
  K*d*ln d < INR (paper_main_gordon_ceiling (K*d*ln d)) <= (K+1)*d*ln d.
Proof.
intros HK Hd Hlog.
assert (Hnonneg : 0 <= K*d*ln d) by (repeat apply Rmult_le_pos; lra).
pose proof (paper_main_gordon_ceiling_bound (K*d*ln d) Hnonneg) as [Hlt Hle].
split; [exact Hlt|]; nra.
Qed.

Lemma paper_main_head_data_operator_rate C E K N k d :
  0 <= C -> 0 <= E -> 0 <= K -> 0 <= N -> 0 <= k ->
  1 <= d -> 1 <= ln d -> N <= C*d^2 -> k <= K*d*ln d ->
  8*(E*(d+k)+ln(k+1)+k*ln(N+1)+ln d) <=
    (8*(E*(1+K)+K+K*(ln(C+1)+2)+1))*d*(ln d)^2.
Proof.
intros HC HE HK HN Hk Hd Hl HNb Hkb.
pose proof (paper_main_log_successor_bound k Hk) as Hlk.
pose proof (paper_main_log_successor_bound C HC) as Hlc.
pose proof (paper_main_log_quadratic_count_coarse C N d HC HN Hd Hl HNb) as Hln.
pose (l := ln d); fold l in Hl,Hkb,Hln |- *.
pose (M := ln(C+1)+2); fold M in Hln |- *.
assert (HM : 0 <= M) by (unfold M; lra).
assert (Hdl : d*l <= d*l^2).
{ assert (Hl2 : l <= l^2) by nra; nra. }
assert (Hdl0 : 0 <= d*l) by nra.
assert (Hk2 : k <= K*d*l^2) by nra.
assert (Hdk : d+k <= (1+K)*d*l^2).
{ assert (Hdd : d <= d*l^2) by nra; nra. }
pose proof (Rmult_le_compat_l E _ _ HE Hdk) as HEb.
pose proof (Rmult_le_compat_l k _ _ Hk Hln) as Hprod1.
assert (HMl : 0 <= M*l) by nra.
pose proof (Rmult_le_compat_r (M*l) _ _ HMl Hkb) as Hprod2.
assert (Hlast : l <= d*l^2) by nra.
nra.
Qed.

Lemma paper_main_head_data_tail_rate d :
  1 <= d -> 2*exp(-ln d) = 2/d /\ 2/d <= 2/sqrt d.
Proof.
intro Hd.
assert (Hd0 : 0 < d) by lra.
assert (Hs : 0 < sqrt d) by (apply sqrt_lt_R0; lra).
pose proof (pow2_sqrt d ltac:(lra)) as Hsq.
assert (Hsd : sqrt d <= d) by nra.
split.
- rewrite exp_Ropp,(exp_ln _ Hd0); unfold Rdiv; reflexivity.
- apply (Rmult_le_reg_r (d*sqrt d)); [nra|].
  replace (2/d*(d*sqrt d)) with (2*sqrt d) by (field; lra).
  replace (2/sqrt d*(d*sqrt d)) with (2*d) by (field; lra).
  lra.
Qed.
