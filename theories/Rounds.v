From Stdlib Require Import Reals Lra Lia ZArith.

Open Scope R_scope.

(** An explicit logarithmic bound on the number of geometric peeling rounds.
    The strict integer upper bound [up] may take one extra round when the
    logarithmic quotient is integral; the final constant absorbs that round. *)

Lemma logarithmic_rounds (d : nat) :
  (2 <= d)%nat ->
  exists K : nat,
    1 / 4 ^ K <= 1 / (INR d) ^ 4 /\
    INR K <= (4 / ln 2) * ln (INR d).
Proof.
  intro Hd.
  assert (HdR : 2 <= INR d).
  { change (INR 2 <= INR d). now apply le_INR. }
  assert (Hln2 : 0 < ln 2).
  { pose proof (ln_increasing 1 2 ltac:(lra) ltac:(lra)).
    rewrite ln_1 in H. exact H. }
  assert (HlnD : ln 2 <= ln (INR d)).
  { destruct (Rle_lt_or_eq_dec _ _ HdR) as [Hlt | Heq].
    - left. now apply ln_increasing; try lra.
    - now rewrite <- Heq. }
  set (q := 2 * ln (INR d) / ln 2).
  assert (Hq : 2 <= q).
  { unfold q. apply (Rmult_le_reg_r (ln 2)); [exact Hln2 |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  destruct (archimed q) as [Hup_gt Hup_le].
  assert (Hup_nonnegative : (0 <= up q)%Z).
  { apply le_IZR. simpl. lra. }
  set (K := Z.to_nat (up q)).
  assert (HK : INR K = IZR (up q)).
  { unfold K. rewrite INR_IZR_INZ, Z2Nat.id; auto. }
  assert (HKlower : q < INR K) by (rewrite HK; exact Hup_gt).
  assert (HKupper : INR K <= q + 1) by (rewrite HK; lra).
  exists K. split.
  - assert (Hpow : (INR d)^4 < 4^K).
    { apply ln_lt_inv; try (apply pow_lt; lra).
      rewrite !ln_pow by lra.
      assert (Hln4 : ln 4 = 2 * ln 2).
      { replace 4 with (2 * 2) by ring.
        rewrite ln_mult by lra. ring. }
      rewrite Hln4. simpl INR.
      assert (Hmult := Rmult_lt_compat_r (ln 2) _ _ Hln2 HKlower).
      unfold q, Rdiv in Hmult.
      rewrite Rmult_assoc, Rinv_l in Hmult by lra.
      nra. }
    unfold Rdiv. rewrite !Rmult_1_l.
    left. apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat; apply pow_lt; lra.
    + exact Hpow.
  - assert (Hqeq : (4 / ln 2) * ln (INR d) = 2 * q).
    { unfold q, Rdiv. ring. }
    rewrite Hqeq. lra.
Qed.
