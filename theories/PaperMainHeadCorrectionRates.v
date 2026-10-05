(* Scalar inequalities that fix the rates of the head correction: powers
   of a parameter t >= 1 absorb the constants. Deterministic.
   - paper_main_head_rate_frobenius, paper_main_head_rate_l1,
     paper_main_head_rate_linfty, paper_main_head_rate_operator: from
     hypotheses such as m <= K d t and K a^2 <= c E^2, coefficient bounds of
     the forms m (a / t^8)^2 <= c d (E / t^7)^2 and
     (B / (d t^6) lam + A / t^7) / sqrt d <= F / (sqrt d t^4).
   - paper_main_head_rate_cone: if (1 + 2 kappa^2) F < kappa t^4, then
     F / (sqrt d t^4) < 1 / (kappa sqrt d) and
       kappa / sqrt d + F / (sqrt d t^4)
         <= 2 kappa^2 (1 / (kappa sqrt d) - F / (sqrt d t^4)).
   - paper_main_head_rate_eta: E < t^7 gives 0 <= E / t^7 < 1.
   - paper_main_head_rate_constants: constants E, A, B, F satisfying
     K a^2 <= c E^2, K a <= c A, a + Q A <= c0 B and B L + A <= F exist.
   - paper_main_head_rate_cutoff: some T >= 1 gives 1 <= t, E < t^7 and
     (1 + 2 kappa^2) F < kappa t^4 for every t >= T. *)
From Stdlib Require Import Reals Lia Lra Psatz.
Open Scope R_scope.

Lemma paper_main_head_rate_frobenius d t m K a c E :
  0 < d -> 1 <= t -> 0 <= K -> 0 <= a -> 0 < c ->
  m <= K*d*t -> K*a^2 <= c*E^2 ->
  m*(a/t^8)^2 <= c*d*(E/t^7)^2.
Proof.
intros Hd Ht HK Ha Hc Hm HE.
apply (Rmult_le_reg_r (t^16)); [apply pow_lt; lra|].
replace (m*(a/t^8)^2*t^16) with (m*a^2) by (field; lra).
replace (c*d*(E/t^7)^2*t^16) with (c*d*E^2*t^2) by (field; lra).
pose proof (Rmult_le_compat_r (a^2) _ _ (pow2_ge_0 a) Hm) as H1.
assert (Hdt : 0 <= d*t) by nra.
pose proof (Rmult_le_compat_r (d*t) _ _ Hdt HE) as H2.
assert (Hce : 0 <= c*d*E^2) by (apply Rmult_le_pos; [nra|apply pow2_ge_0]).
assert (Htt : t <= t^2) by nra.
pose proof (Rmult_le_compat_l (c*d*E^2) _ _ Hce Htt) as H3.
nra.
Qed.

Lemma paper_main_head_rate_l1 d t m K a c A :
  0 < d -> 1 <= t -> 0 <= a ->
  m <= K*d*t -> K*a <= c*A ->
  m*(a/t^8) <= c*d*(A/t^7).
Proof.
intros Hd Ht Ha Hm HA.
apply (Rmult_le_reg_r (t^8)); [apply pow_lt; lra|].
replace (m*(a/t^8)*t^8) with (m*a) by (field; lra).
replace (c*d*(A/t^7)*t^8) with (c*d*A*t) by (field; lra).
pose proof (Rmult_le_compat_r a _ _ Ha Hm) as H1.
assert (Hdt : 0 <= d*t) by nra.
pose proof (Rmult_le_compat_r (d*t) _ _ Hdt HA) as H2.
nra.
Qed.

Lemma paper_main_head_rate_linfty d t q Q a A c0 B :
  0 < d -> 1 <= t -> 0 <= a -> 0 <= A ->
  q <= Q*t -> a+Q*A <= c0*B ->
  a/t^8+q*(A/t^7) <= c0*d*(B/(d*t^6)).
Proof.
intros Hd Ht Ha HA Hq HB.
apply (Rmult_le_reg_r (t^8)); [apply pow_lt; lra|].
replace ((a/t^8+q*(A/t^7))*t^8) with (a+q*A*t) by (field; lra).
replace (c0*d*(B/(d*t^6))*t^8) with (c0*B*t^2) by (field; split; lra).
assert (HAt : 0 <= A*t) by nra.
pose proof (Rmult_le_compat_r (A*t) _ _ HAt Hq) as H1.
pose proof (Rmult_le_compat_r (t^2) _ _ (pow2_ge_0 t) HB) as H2.
assert (Htt : 1 <= t^2) by nra.
pose proof (Rmult_le_compat_l a _ _ Ha Htt) as H3.
nra.
Qed.

Lemma paper_main_head_rate_operator d t lam L A B F :
  0 < d -> 1 <= t -> 0 <= A -> 0 <= B ->
  lam <= L*d*t^2 -> B*L+A <= F ->
  (B/(d*t^6)*lam+A/t^7)/sqrt d <= F/(sqrt d*t^4).
Proof.
intros Hd Ht HA HB Hlam HF.
pose proof (sqrt_lt_R0 d Hd) as Hsd.
assert (Hden : 0 < sqrt d*d*t^7) by (repeat apply Rmult_lt_0_compat; try lra; apply pow_lt; lra).
apply (Rmult_le_reg_r (sqrt d*d*t^7)); [exact Hden|].
replace ((B/(d*t^6)*lam+A/t^7)/sqrt d*(sqrt d*d*t^7)) with (B*lam*t+A*d)
  by (field; repeat split; lra).
replace (F/(sqrt d*t^4)*(sqrt d*d*t^7)) with (F*d*t^3)
  by (field; split; lra).
assert (HBt : 0 <= B*t) by nra.
pose proof (Rmult_le_compat_r (B*t) _ _ HBt Hlam) as H1.
assert (Hdt : 0 <= d*t^3) by (apply Rmult_le_pos; [lra|apply pow_le;lra]).
pose proof (Rmult_le_compat_r (d*t^3) _ _ Hdt HF) as H2.
assert (Ht3 : 1 <= t^3) by nra.
assert (HAd : 0 <= A*d) by nra.
pose proof (Rmult_le_compat_l (A*d) _ _ HAd Ht3) as H3.
nra.
Qed.

Lemma paper_main_head_rate_cone d t kappa F :
  0 < d -> 1 <= t -> 1 <= kappa -> 0 <= F ->
  (1+2*kappa^2)*F < kappa*t^4 ->
  F/(sqrt d*t^4) < 1/(kappa*sqrt d) /\
  kappa/sqrt d+F/(sqrt d*t^4) <=
    (2*kappa^2)*(1/(kappa*sqrt d)-F/(sqrt d*t^4)).
Proof.
intros Hd Ht Hk HF Hlarge.
pose proof (sqrt_lt_R0 d Hd) as Hs.
assert (Hpow : 0 < t^4) by (apply pow_lt; lra).
assert (Hsmall : F*kappa < t^4).
{ assert (Hcomp : kappa^2*F <= (1+2*kappa^2)*F) by nra.
  nra. }
assert (Hden : 0 < sqrt d*t^4*kappa) by (repeat apply Rmult_lt_0_compat; lra).
split.
- apply (Rmult_lt_reg_r (sqrt d*t^4*kappa)); [exact Hden|].
  replace (F/(sqrt d*t^4)*(sqrt d*t^4*kappa)) with (F*kappa)
    by (field; repeat split; lra).
  replace (1/(kappa*sqrt d)*(sqrt d*t^4*kappa)) with (t^4)
    by (field; split; lra).
  exact Hsmall.
- apply (Rmult_le_reg_r (sqrt d*t^4*kappa)); [exact Hden|].
  replace ((kappa/sqrt d+F/(sqrt d*t^4))*(sqrt d*t^4*kappa))
    with (kappa^2*t^4+F*kappa) by (field; split; lra).
  replace ((2*kappa^2)*(1/(kappa*sqrt d)-F/(sqrt d*t^4))*(sqrt d*t^4*kappa))
    with (2*kappa^2*t^4-2*kappa^3*F) by (field; repeat split; lra).
  pose proof (Rmult_lt_compat_r kappa _ _ ltac:(lra) Hlarge) as Hmul.
  nra.
Qed.

Lemma paper_main_head_rate_eta t E :
  1 <= t -> 0 <= E -> E < t^7 -> 0 <= E/t^7 < 1.
Proof.
intros Ht HE Hsmall.
assert (Hp : 0 < t^7) by (apply pow_lt; lra).
split.
- unfold Rdiv; apply Rmult_le_pos; [exact HE|apply Rlt_le,Rinv_0_lt_compat; exact Hp].
- apply (Rmult_lt_reg_r (t^7)); [exact Hp|].
  replace (E/t^7*t^7) with E by (field; lra).
  lra.
Qed.

Theorem paper_main_head_rate_constants K a c c0 Q L :
  0 <= K -> 0 <= a -> 0 < c -> 0 < c0 -> 0 <= Q -> 0 <= L ->
  exists E A B F, 0 < E /\ 0 <= A /\ 0 <= B /\ 0 < F /\
    K*a^2 <= c*E^2 /\ K*a <= c*A /\ a+Q*A <= c0*B /\ B*L+A <= F.
Proof.
intros HK Ha Hc Hc0 HQ HL.
pose (u := K*a^2/c).
pose (E := 1+u).
pose (A := K*a/c).
pose (B := (a+Q*A)/c0).
pose (F := B*L+A+1).
assert (Hu : 0 <= u).
{ unfold u,Rdiv; apply Rmult_le_pos; [nra|apply Rlt_le,Rinv_0_lt_compat; lra]. }
assert (HA : 0 <= A).
{ unfold A,Rdiv; repeat apply Rmult_le_pos; try lra; apply Rlt_le,Rinv_0_lt_compat; lra. }
assert (HB : 0 <= B).
{ unfold B,Rdiv; apply Rmult_le_pos; [nra|apply Rlt_le,Rinv_0_lt_compat;lra]. }
assert (HuE : c*u=K*a^2) by (unfold u; field; lra).
assert (HAE : c*A=K*a) by (unfold A; field; lra).
assert (HBE : c0*B=a+Q*A) by (unfold B; field; lra).
assert (HE : u <= E^2) by (unfold E; nra).
pose proof (Rmult_le_compat_l c _ _ ltac:(lra) HE) as HCE.
exists E,A,B,F; repeat split; try lra; unfold E,F; nra.
Qed.

Lemma paper_main_head_rate_cutoff kappa E F :
  1 <= kappa -> 0 <= E -> 0 <= F ->
  exists T, 1 <= T /\ forall t, T <= t ->
    1 <= t /\ E < t^7 /\ (1+2*kappa^2)*F < kappa*t^4.
Proof.
intros Hk HE HF.
pose (T := 2+E+(1+2*kappa^2)*F).
assert (HT : 1 <= T) by (unfold T; nra).
exists T; split; [exact HT|].
intros t Ht.
assert (Ht1 : 1 <= t) by lra.
assert (Htp4 : t <= t^4).
{ assert (H2 : 1 <= t^2) by nra.
  assert (Htt2 : t <= t^2) by nra.
  assert (H24 : t^2 <= t^4) by nra.
  nra. }
assert (Htp7 : t <= t^7).
{ assert (H3 : 1 <= t^3) by nra.
  assert (H4 : 0 <= t^4) by (apply pow_le; lra).
  pose proof (Rmult_le_compat_l (t^4) _ _ H4 H3) as HH.
  assert (H7 : t^7=t^4*t^3) by ring.
  nra. }
assert (Hp4 : 0 <= t^4) by (apply pow_le; lra).
assert (Ht4 : t^4 <= kappa*t^4) by nra.
unfold T in Ht; repeat split; nra.
Qed.
