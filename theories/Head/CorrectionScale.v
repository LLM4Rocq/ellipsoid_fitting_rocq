(* The dimension scale t = d^(1/32) (paper_main_head_scale, five square
   roots) and the constants of the head correction bounds of
   lem:head-correction-bounds of the paper at that scale. Deterministic.
   - paper_main_head_scale_powers: for d >= 1, t >= 1, t^8 = d^(1/4) and
     t^32 = d. paper_main_head_scale_log: 0 <= ln d <= 32 t.
   - paper_main_head_scale_eventually: t >= T for all large d.
     paper_main_head_inverse_power_small: C / t^k tends to 0 for k > 0.
   - paper_main_head_correction_eventual: for K, a, Q, L >= 0, c, c0 > 0
     and kappa >= 1 there are constants E, A, B, F such that, for all large
     d, if m <= K d ln d, q <= Q ln d and lam <= L d (ln d)^2, then the
     quantities eta = E / t^7, A1 = A / t^7, Ainf = B / (d t^6) and
     delta = F / (sqrt d t^4) satisfy
       m (a/t^8)^2 <= c d eta^2, 0 <= eta < 1, m (a/t^8) <= c d A1,
       a/t^8 + q A1 <= c0 d Ainf, (Ainf lam + A1) / sqrt d <= delta,
       delta < 1 / (kappa sqrt d) and
       kappa / sqrt d + delta <= 2 kappa^2 (1 / (kappa sqrt d) - delta).
     The proof bounds ln d by 32 t and applies the scalar inequalities of
     Head.CorrectionRates. *)
From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import Head.CorrectionRates.
Open Scope R_scope.

Definition paper_main_head_scale d := sqrt(sqrt(sqrt(sqrt(sqrt d)))).

Lemma paper_main_head_scale_powers d :
  1 <= d ->
  1 <= paper_main_head_scale d /\
  (paper_main_head_scale d)^8 = sqrt(sqrt d) /\
  (paper_main_head_scale d)^32 = d.
Proof.
intro Hd.
assert (H1 : 1 <= sqrt d).
{ rewrite <- sqrt_1; apply sqrt_le_1_alt; exact Hd. }
assert (H2 : 1 <= sqrt(sqrt d)).
{ rewrite <- sqrt_1; apply sqrt_le_1_alt; exact H1. }
assert (H3 : 1 <= sqrt(sqrt(sqrt d))).
{ rewrite <- sqrt_1; apply sqrt_le_1_alt; exact H2. }
assert (H4 : 1 <= sqrt(sqrt(sqrt(sqrt d)))).
{ rewrite <- sqrt_1; apply sqrt_le_1_alt; exact H3. }
assert (H5 : 1 <= paper_main_head_scale d).
{ unfold paper_main_head_scale; rewrite <- sqrt_1; apply sqrt_le_1_alt; exact H4. }
pose proof (pow2_sqrt d ltac:(lra)) as E1.
pose proof (pow2_sqrt (sqrt d) ltac:(lra)) as E2.
pose proof (pow2_sqrt (sqrt(sqrt d)) ltac:(lra)) as E3.
pose proof (pow2_sqrt (sqrt(sqrt(sqrt d))) ltac:(lra)) as E4.
pose proof (pow2_sqrt (sqrt(sqrt(sqrt(sqrt d)))) ltac:(lra)) as E5.
fold (paper_main_head_scale d) in E5.
assert (E8 : (paper_main_head_scale d)^8 = sqrt(sqrt d)).
{ replace ((paper_main_head_scale d)^8) with ((((paper_main_head_scale d)^2)^2)^2) by ring.
  rewrite E5, E4; exact E3. }
split; [exact H5|]; split; [exact E8|].
replace ((paper_main_head_scale d)^32) with ((((paper_main_head_scale d)^8)^2)^2) by ring.
rewrite E8, E2; exact E1.
Qed.

Lemma paper_main_head_scale_log d :
  1 <= d -> 0 <= ln d <= 32*paper_main_head_scale d.
Proof.
intro Hd.
destruct (paper_main_head_scale_powers d Hd) as [Ht [E8 E32]].
assert (Ht0 : 0 < paper_main_head_scale d) by lra.
pose proof (exp_ineq1_le (ln (paper_main_head_scale d))) as HB.
rewrite (exp_ln _ Ht0) in HB.
pose proof (ln_pow _ Ht0 32) as HP.
assert (H32 : INR 32 = 32) by (simpl; ring).
rewrite E32, H32 in HP.
split.
- destruct (Rle_lt_or_eq_dec _ _ Hd) as [Hlt|Heq].
  + rewrite <- ln_1; left; apply ln_increasing; lra.
  + rewrite <- Heq,ln_1; lra.
- lra.
Qed.

Lemma paper_main_head_scale_large T d :
  1 <= T -> T^32 <= d -> T <= paper_main_head_scale d.
Proof.
intros HT Hd.
assert (HTp : 1 <= T^32).
{ pose proof (pow_incr 1 T 32 ltac:(lra)); simpl in H; lra. }
assert (Hd1 : 1 <= d) by lra.
destruct (paper_main_head_scale_powers d Hd1) as [Ht [E8 E32]].
destruct (Rle_dec T (paper_main_head_scale d)) as [H|H]; [exact H|].
assert (Hlt : paper_main_head_scale d < T) by lra.
assert (HP0 : 0 < T^31) by (apply pow_lt; lra).
pose proof (pow_incr (paper_main_head_scale d) T 31 ltac:(lra)) as HP.
pose proof (Rmult_le_compat_l (paper_main_head_scale d) _ _ ltac:(lra) HP) as Hle.
pose proof (Rmult_lt_compat_r (T^31) _ _ HP0 Hlt) as Hstrict.
assert (HP32 : (paper_main_head_scale d)^32 < T^32).
{ change (paper_main_head_scale d*(paper_main_head_scale d)^31 < T*T^31); lra. }
rewrite E32 in HP32; lra.
Qed.

Lemma paper_main_head_scale_eventually T :
  1 <= T -> exists D : nat, forall d, (D <= d)%nat -> T <= paper_main_head_scale (INR d).
Proof.
intro HT.
destruct (INR_unbounded (T^32)) as [D HD].
exists D; intros d Hdd.
apply paper_main_head_scale_large; [exact HT|].
pose proof (le_INR D d Hdd); lra.
Qed.

Lemma paper_main_head_inverse_power_small C k eps :
  0 <= C -> (0 < k)%nat -> 0 < eps ->
  exists D : nat, forall d, (D <= d)%nat ->
    0 <= C/(paper_main_head_scale (INR d))^k < eps.
Proof.
intros HC Hk He.
pose (T := 2+C/eps).
assert (HT : 1 <= T).
{ assert (Hdiv : 0 <= C/eps).
  { unfold Rdiv; apply Rmult_le_pos; [exact HC|apply Rlt_le,Rinv_0_lt_compat; exact He]. }
  unfold T; lra. }
destruct (paper_main_head_scale_eventually T HT) as [D HD].
exists D; intros d Hdd.
pose (t := paper_main_head_scale (INR d)).
assert (Hlarge : T <= t) by apply HD,Hdd.
assert (Ht : 1 <= t) by lra.
assert (Hpow : t <= t^k).
{ destruct k as [|j]; [lia|].
  pose proof (pow_incr 1 t j ltac:(lra)) as HP.
  rewrite pow1 in HP; simpl; nra. }
assert (Hp : 0 < t^k) by lra.
change (0 <= C/t^k < eps).
split.
- unfold Rdiv; apply Rmult_le_pos; [exact HC|apply Rlt_le,Rinv_0_lt_compat; exact Hp].
- apply (Rmult_lt_reg_r (t^k)); [exact Hp|].
  replace (C/t^k*t^k) with C by (field; lra).
  assert (HE : eps*T = 2*eps+C) by (unfold T; field; lra).
  nra.
Qed.

Theorem paper_main_head_correction_eventual K a c c0 Q L kappa :
  0 <= K -> 0 <= a -> 0 < c -> 0 < c0 -> 0 <= Q -> 0 <= L -> 1 <= kappa ->
  exists E A B F D, 0 < E /\ 0 <= A /\ 0 <= B /\ 0 < F /\
    forall d : nat, (D <= d)%nat -> forall m q lam : R,
      m <= K*INR d*ln(INR d) -> q <= Q*ln(INR d) ->
      lam <= L*INR d*(ln(INR d))^2 ->
      let t := paper_main_head_scale (INR d) in
      let eta := E/t^7 in let A1 := A/t^7 in let Ainf := B/(INR d*t^6) in
      let delta := F/(sqrt(INR d)*t^4) in
      0 < INR d /\ 1 <= t /\
      m*(a/t^8)^2 <= c*INR d*eta^2 /\ 0 <= eta < 1 /\
      m*(a/t^8) <= c*INR d*A1 /\ a/t^8+q*A1 <= c0*INR d*Ainf /\
      (Ainf*lam+A1)/sqrt(INR d) <= delta /\
      delta < 1/(kappa*sqrt(INR d)) /\
      kappa/sqrt(INR d)+delta <= (2*kappa^2)*(1/(kappa*sqrt(INR d))-delta).
Proof.
intros HK Ha Hc Hc0 HQ HL Hk.
assert (HK' : 0 <= 32*K) by lra.
assert (HQ' : 0 <= 32*Q) by lra.
assert (HL' : 0 <= 1024*L) by lra.
destruct (paper_main_head_rate_constants (32*K) a c c0 (32*Q) (1024*L)
  HK' Ha Hc Hc0 HQ' HL') as (E & A & B & F & HE & HA & HB & HF & HEc & HAc & HBc & HFc).
destruct (paper_main_head_rate_cutoff kappa E F Hk ltac:(lra) ltac:(lra)) as [T [HT Hcut]].
destruct (paper_main_head_scale_eventually T HT) as [D HD].
exists E,A,B,F,(Nat.max 1 D).
split; [exact HE|]; split; [exact HA|]; split; [exact HB|]; split; [exact HF|].
intros d Hdd m q lam Hm Hq Hlam; cbv zeta.
assert (Hd1 : 1 <= INR d).
{ change (INR 1 <= INR d); apply le_INR; lia. }
assert (Hd : 0 < INR d) by lra.
pose (t := paper_main_head_scale (INR d)); fold t.
assert (HTt : T <= t) by (apply HD; lia).
destruct (Hcut t HTt) as [Ht [HEt HFt]].
pose proof (paper_main_head_scale_log (INR d) Hd1) as Hlog; fold t in Hlog.
assert (Hm' : m <= (32*K)*INR d*t).
{ pose proof (Rmult_le_compat_l (K*INR d) _ _ ltac:(nra) (proj2 Hlog)); nra. }
assert (Hq' : q <= (32*Q)*t).
{ pose proof (Rmult_le_compat_l Q _ _ HQ (proj2 Hlog)); nra. }
assert (Hlam' : lam <= (1024*L)*INR d*t^2).
{ assert (Hsq : (ln(INR d))^2 <= 1024*t^2) by nra.
  pose proof (Rmult_le_compat_l (L*INR d) _ _ ltac:(nra) Hsq); nra. }
pose proof (paper_main_head_rate_frobenius (INR d) t m (32*K) a c E
  Hd Ht HK' Ha Hc Hm' HEc) as Hfro.
pose proof (paper_main_head_rate_l1 (INR d) t m (32*K) a c A
  Hd Ht Ha Hm' HAc) as Hl1.
pose proof (paper_main_head_rate_linfty (INR d) t q (32*Q) a A c0 B
  Hd Ht Ha HA Hq' HBc) as Hinf.
pose proof (paper_main_head_rate_operator (INR d) t lam (1024*L) A B F
  Hd Ht HA HB Hlam' HFc) as Hop.
pose proof (paper_main_head_rate_cone (INR d) t kappa F Hd Ht Hk ltac:(lra) HFt) as Hcone.
pose proof (paper_main_head_rate_eta t E Ht ltac:(lra) HEt) as Heta.
tauto.
Qed.
