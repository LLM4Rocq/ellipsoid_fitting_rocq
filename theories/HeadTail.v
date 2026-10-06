From Stdlib Require Import Reals List Permutation Lia Lra Psatz.
From EllipsoidFitting Require Import Definitions Peeling Rounds FiniteSets NormBounds.
Import ListNotations.
Open Scope R_scope.

(* A head-tail decomposition of a unit vector y of R^n
   (head_tail_decomposition_explicit). For theta > 0 and d >= 1 there is a
   set J of at most head_tail_constant theta * d * ln d coordinates, where
   head_tail_constant theta = 16 / (theta^2 ln 2), such that the tail, the
   coordinates outside J, either has norm at most 1 / d^2, or has positive
   norm and every tail coordinate of y divided by that norm is at most
   theta / sqrt d in absolute value. The proof removes large coordinates in
   at most (4 / ln 2) ln d rounds of peeling_iteration. *)

Lemma tail_indices_empty (n : nat) : tail_indices n [] = seq 0 n.
Proof.
  unfold tail_indices, outside.
  induction (seq 0 n) as [|i A IH]; simpl; [reflexivity |].
  f_equal; exact IH.
Qed.

Lemma energy_permutation (w : nat -> R) (A B : list nat) :
  Permutation A B -> energy w A = energy w B.
Proof.
  intro H; induction H; simpl; try lra; congruence.
Qed.

Lemma squared_energy_nonneg (y : nat -> R) (A : list nat) :
  0 <= squared_energy y A.
Proof.
  apply energy_nonneg; intros; nra.
Qed.

Lemma head_tail_constant_positive (theta : R) :
  0 < theta -> 0 < head_tail_constant theta.
Proof.
  intro Htheta; unfold head_tail_constant.
  assert (Hlog : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
  apply Rdiv_lt_0_compat; [lra |].
  apply Rmult_lt_0_compat; [now apply pow_lt | exact Hlog].
Qed.

Lemma peeling_head_size (theta D N K : R) :
  0 < theta -> 0 < D ->
  N * (theta ^ 2 / (4 * D)) <= K ->
  K <= (4 / ln 2) * ln D ->
  N <= head_tail_constant theta * D * ln D.
Proof.
  intros Htheta HD Hcount Hrounds.
  assert (Hlog : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
  assert (Hbeta : 0 < theta ^ 2 / (4 * D)) by
    (apply Rdiv_lt_0_compat; nra).
  apply (Rmult_le_reg_r (theta ^ 2 / (4 * D))); [exact Hbeta |].
  unfold head_tail_constant.
  replace (16 / (theta ^ 2 * ln 2) * D * ln D * (theta ^ 2 / (4 * D))) with
    ((4 / ln 2) * ln D) by (field; repeat split; nra).
  lra.
Qed.

Theorem head_tail_decomposition_explicit (theta : R) (d n : nat) (y : nat -> R) :
  0 < theta -> (1 <= d)%nat -> squared_energy y (seq 0 n) = 1 ->
  exists J : list nat,
    NoDup J /\ incl J (seq 0 n) /\
    INR (length J) <= head_tail_constant theta * INR d * ln (INR d) /\
    (vector_norm y (tail_indices n J) <= 1 / (INR d) ^ 2 \/
     (0 < vector_norm y (tail_indices n J) /\
      forall i, In i (tail_indices n J) ->
        Rabs (y i / vector_norm y (tail_indices n J)) <= theta / sqrt (INR d))).
Proof.
  intros Htheta Hd Hy.
  destruct (Nat.eq_dec d 1) as [Hd1 | Hd1].
  - subst d; exists [].
    split; [constructor |].
    split; [intros i Hi; contradiction |].
    split.
    + simpl INR; simpl length; rewrite ln_1; lra.
    + left; rewrite tail_indices_empty.
      unfold vector_norm; rewrite Hy, sqrt_1.
      change (1 <= 1 / 1 ^ 2); right; field.
  - assert (Hd2 : (2 <= d)%nat) by lia.
    assert (HD : 0 < INR d) by (apply lt_0_INR; lia).
    set (beta := theta ^ 2 / (4 * INR d)).
    assert (Hbeta : 0 < beta) by (unfold beta; apply Rdiv_lt_0_compat; nra).
    destruct (logarithmic_rounds d Hd2) as [K [Hdecay Hrounds]].
    assert (HA : NoDup (seq 0 n)) by apply seq_NoDup.
    assert (Hw : forall i, In i (seq 0 n) -> 0 <= y i ^ 2) by (intros; nra).
    destruct (peeling_iteration (fun i => y i ^ 2) (seq 0 n) beta K HA Hw Hbeta)
      as [B [HB [HNB [Hcount Hcase]]]].
    exists (outside B (seq 0 n)).
    split; [now apply outside_nodup |].
    split; [apply outside_incl |].
    split.
    + rewrite outside_length by assumption.
      eapply peeling_head_size; [exact Htheta | exact HD | exact Hcount | exact Hrounds].
    + assert (Hperm : Permutation (tail_indices n (outside B (seq 0 n))) B).
      { unfold tail_indices; now apply outside_twice_permutation. }
      assert (HE : squared_energy y (tail_indices n (outside B (seq 0 n))) =
        squared_energy y B).
      { unfold squared_energy; now apply energy_permutation. }
      assert (HE0 : 0 <= squared_energy y B) by apply squared_energy_nonneg.
      unfold vector_norm; rewrite HE.
      destruct Hcase as [Hsmall | Hcap].
      * left; apply norm_tiny_from_energy; [exact HD | exact HE0 |].
        change (squared_energy y B <= squared_energy y (seq 0 n) / 4 ^ K) in Hsmall.
        rewrite Hy in Hsmall; eapply Rle_trans; eauto.
      * destruct (Rlt_dec 0 (squared_energy y B)) as [HEpos | HEpos].
        -- right; split; [now apply sqrt_lt_R0 |].
           intros i Hi; apply norm_cap_from_energy; try assumption.
           assert (HiB : In i B) by (eapply Permutation_in; eauto).
           specialize (Hcap i HiB).
           change (y i ^ 2 <= 4 * beta * squared_energy y B) in Hcap.
           replace (theta ^ 2 / INR d * squared_energy y B) with
             (4 * beta * squared_energy y B) by (unfold beta; field; lra).
           exact Hcap.
        -- left; apply norm_tiny_from_energy; [exact HD | exact HE0 |].
           assert (Hthreshold : 0 < 1 / INR d ^ 4) by
             (apply Rdiv_lt_0_compat; [lra | now apply pow_lt]).
           lra.
Qed.
