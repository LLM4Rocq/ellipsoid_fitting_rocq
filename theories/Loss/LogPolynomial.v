(* Uniform polynomial approximation of the logarithm on [a, 1], a > 0.
   Deterministic. The Taylor polynomial P_n(z) = sum_(k=1..n) z^k / k
   (paper_main_loss_log_poly) of -ln(1 - z) satisfies
   0 <= -ln(1 - z) - P_n(z) <= q^n / (1 - q) for 0 <= z <= q < 1
   (paper_main_loss_log_remainder), by the mean value theorem: the
   remainder vanishes at 0 and has derivative z^n / (1 - z). Hence P_n
   converges to -ln(1 - z) uniformly on [0, q]
   (paper_main_loss_log_uniform), and P_n(1 - x) converges to -ln x
   uniformly on [a, 1] (paper_main_loss_log_factor_uniform).
   Loss.Replica applies this to the Gibbs row factor, which lies
   in [exp(-beta), 1]. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.CurveDerivatives.
Open Scope R_scope.

Fixpoint paper_main_loss_log_poly (n : nat) (z : R) : R :=
  match n with O => 0 | S k => paper_main_loss_log_poly k z + z ^ (S k) / INR (S k) end.
Fixpoint paper_main_loss_geom (n : nat) (z : R) : R :=
  match n with O => 0 | S k => paper_main_loss_geom k z + z ^ k end.

Lemma paper_main_loss_geom_identity n z :
  (1-z)*paper_main_loss_geom n z = 1-z^n.
Proof. induction n; simpl; [ring|nra]. Qed.

Lemma paper_main_loss_log_poly_zero n : paper_main_loss_log_poly n 0 = 0.
Proof. induction n; simpl; rewrite ?IHn; unfold Rdiv; ring. Qed.

Lemma paper_main_loss_log_poly_derive n z :
  derivable_pt_lim (paper_main_loss_log_poly n) z (paper_main_loss_geom n z).
Proof.
induction n as [|n IH]; simpl.
- apply derivable_pt_lim_const.
- apply (derivable_pt_lim_plus (paper_main_loss_log_poly n)
    (fun t => t ^ S n / INR(S n))).
  + exact IH.
  + assert (HN : INR(S n) <> 0) by (apply not_0_INR; lia).
    replace (z ^ n) with ((INR(S n)*z^n)*/INR(S n)) by (field; exact HN).
    apply derivable_pt_lim_scal_right; exact (derivable_pt_lim_pow z (S n)).
Qed.

Lemma paper_main_loss_log_remainder_derive n z : z < 1 ->
  derivable_pt_lim (fun t => -ln(1-t)-paper_main_loss_log_poly n t) z
    (z^n/(1-z)).
Proof.
intro Hz.
assert (HD : derivable_pt_lim (fun t => ln(1-t)) z ((/(1-z))*(-1))).
{ apply (derivable_pt_lim_comp (fun t => 1-t) ln z (-1) (/(1-z))).
  - replace (-1) with (0-1) by ring.
    apply derivable_pt_lim_minus; [apply derivable_pt_lim_const|apply derivable_pt_lim_id].
  - apply derivable_pt_lim_ln; lra. }
replace (z^n/(1-z)) with (-((/(1-z))*(-1))-paper_main_loss_geom n z).
- apply derivable_pt_lim_minus; [apply derivable_pt_lim_opp; exact HD|apply paper_main_loss_log_poly_derive].
- pose proof (paper_main_loss_geom_identity n z) as HG.
  apply (Rmult_eq_reg_r (1-z)); [field_simplify; nra|lra].
Qed.

Theorem paper_main_loss_log_remainder n q z :
  0 <= q < 1 -> 0 <= z <= q ->
  0 <= -ln(1-z)-paper_main_loss_log_poly n z <= q^n/(1-q).
Proof.
intros Hq Hz.
destruct (Req_dec z 0) as [->|Hz0].
- rewrite Rminus_0_r, ln_1, paper_main_loss_log_poly_zero.
  replace (-0-0) with 0 by ring.
  split; [lra|unfold Rdiv; apply Rmult_le_pos; [apply pow_le; lra|apply Rlt_le, Rinv_0_lt_compat; lra]].
- destruct (MVT_cor2
    (fun t => -ln(1-t)-paper_main_loss_log_poly n t)
    (fun t => t^n/(1-t)) 0 z ltac:(lra)) as [c [HE HC]].
  + intros t Ht; apply paper_main_loss_log_remainder_derive; lra.
  + rewrite Rminus_0_r, ln_1, paper_main_loss_log_poly_zero in HE.
    pose proof (pow_le c n ltac:(lra)) as HCn.
    pose proof (pow_incr c q n ltac:(lra)) as HCq.
    assert (HD : 0 <= c^n/(1-c)) by (unfold Rdiv; apply Rmult_le_pos; [exact HCn|apply Rlt_le, Rinv_0_lt_compat; lra]).
    assert (HU : c^n/(1-c) <= q^n/(1-q)).
    { apply (Rmult_le_reg_r (1-c)); [lra|].
      assert (H1 : (c^n/(1-c))*(1-c)=c^n) by (field; lra).
      rewrite H1; apply (Rmult_le_reg_r (1-q)); [lra|].
      assert (H2 : (q^n/(1-q)*(1-c))*(1-q)=q^n*(1-c)) by (field; lra).
      rewrite H2; nra. }
    assert (HB : 0 <= q^n/(1-q)) by (unfold Rdiv; apply Rmult_le_pos; [apply pow_le; lra|apply Rlt_le, Rinv_0_lt_compat; lra]).
    split; nra.
Qed.

Theorem paper_main_loss_log_uniform q eps : 0 <= q < 1 -> 0 < eps ->
  exists N, forall n, (N <= n)%nat -> forall z, 0 <= z <= q ->
    Rabs(-ln(1-z)-paper_main_loss_log_poly n z) < eps.
Proof.
intros Hq He.
assert (Habs : Rabs q < 1) by (rewrite Rabs_pos_eq; lra).
destruct (pow_lt_1_zero q Habs (eps*(1-q)) ltac:(nra)) as [N HN].
exists N; intros n Hn z Hz.
pose proof (paper_main_loss_log_remainder n q z Hq Hz) as [HL HU].
rewrite Rabs_pos_eq; [|exact HL].
pose proof (HN n Hn) as HP; rewrite Rabs_pos_eq in HP; [|apply pow_le; lra].
assert (HH : q^n/(1-q) < eps).
{ apply (Rmult_lt_reg_r (1-q)); [lra|].
  assert (HC : q^n/(1-q)*(1-q)=q^n) by (field; lra).
  rewrite HC; exact HP. }
lra.
Qed.

Corollary paper_main_loss_log_factor_uniform a eps :
  0 < a <= 1 -> 0 < eps -> exists N, forall n, (N <= n)%nat ->
  forall x, a <= x <= 1 ->
    Rabs(-ln x-paper_main_loss_log_poly n (1-x)) < eps.
Proof.
intros Ha He.
destruct (paper_main_loss_log_uniform (1-a) eps ltac:(lra) He) as [N HN].
exists N; intros n Hn x Hx.
pose proof (HN n Hn (1-x) ltac:(lra)) as HH.
replace (1-(1-x)) with x in HH by ring; exact HH.
Qed.
