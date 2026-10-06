From Stdlib Require Import Reals List Lra Lia.
From EllipsoidFitting Require Import Head.TailDefinitions.
Import ListNotations.
Open Scope R_scope.

(** Iterative removal of heavy coordinates. energy w A is the sum of the
    weights w i over A, and i is heavy at threshold beta if
    beta * energy w A < w i. With nonnegative weights there are at most
    1 / beta heavy indices (heavy_count), and a round removes them
    (peeling_round). After at most K rounds, at most K / beta indices are
    removed, and either the energy is at most energy w A / 4 ^ K, or every
    remaining weight is at most 4 * beta times the remaining energy
    (peeling_iteration). Classical comparison (Rlt_dec) only selects the
    heavy indices, and empty and zero-energy lists are covered. *)
Lemma energy_nonneg w A :
  (forall i, In i A -> 0 <= w i) -> 0 <= energy w A.
Proof.
  induction A as [|a A IH]; simpl; intros H; [lra|].
  assert (0 <= w a) by (apply H; auto).
  assert (0 <= energy w A) by (apply IH; intros; apply H; auto).
  lra.
Qed.

Lemma energy_member_le w A i :
  (forall j, In j A -> 0 <= w j) -> In i A -> w i <= energy w A.
Proof.
  induction A as [|a A IH]; simpl; intros H Hi; [contradiction|].
  assert (HA : forall j, In j A -> 0 <= w j) by (intros; apply H; auto).
  pose proof (energy_nonneg w A HA).
  assert (0 <= w a) by (apply H; auto).
  destruct Hi as [<-|Hi]; [lra|].
  specialize (IH HA Hi); lra.
Qed.

Lemma filter_incl_nat (f : nat -> bool) A : incl (filter f A) A.
Proof. intros i Hi; apply filter_In in Hi; tauto. Qed.

Lemma energy_filter_nonneg w A f :
  (forall i, In i A -> 0 <= w i) -> 0 <= energy w (filter f A).
Proof.
  intros H; apply energy_nonneg; intros i Hi; apply H.
  now apply (filter_incl_nat f A).
Qed.

Lemma energy_filter_split w A f :
  energy w A = energy w (filter f A) +
    energy w (filter (fun i => negb (f i)) A).
Proof.
  induction A; simpl; [lra|]. destruct (f a); simpl; lra.
Qed.

Lemma filter_length_split_nat (f : nat -> bool) A :
  (length A = length (filter f A) +
    length (filter (fun i => negb (f i)) A))%nat.
Proof. induction A; simpl; [lia|]. destruct (f a); simpl; lia. Qed.

Lemma energy_lower_bound w A c :
  (forall i, In i A -> c <= w i) -> INR (length A) * c <= energy w A.
Proof.
  induction A as [|a A IH]; simpl; intros H; [lra|].
  assert (c <= w a) by (apply H; auto).
  assert (INR (length A) * c <= energy w A)
    by (apply IH; intros; apply H; auto).
  change (INR (S (length A)) * c <= w a + energy w A).
  rewrite S_INR; nra.
Qed.

Definition is_heavy (w : nat -> R) (A : list nat) (beta : R) (i : nat) : bool :=
  if Rlt_dec (beta * energy w A) (w i) then true else false.

Definition heavy w A beta := filter (is_heavy w A beta) A.
Definition remainder w A beta :=
  filter (fun i => negb (is_heavy w A beta i)) A.

Lemma heavy_member w A beta i :
  In i (heavy w A beta) <-> In i A /\ beta * energy w A < w i.
Proof.
  unfold heavy; rewrite filter_In; unfold is_heavy.
  destruct (Rlt_dec (beta * energy w A) (w i)); simpl; intuition congruence.
Qed.

Lemma remainder_member w A beta i :
  In i (remainder w A beta) <-> In i A /\ w i <= beta * energy w A.
Proof.
  unfold remainder; rewrite filter_In; unfold is_heavy.
  destruct (Rlt_dec (beta * energy w A) (w i)); simpl; intuition lra.
Qed.

Lemma heavy_count w A beta :
  (forall i, In i A -> 0 <= w i) -> 0 <= beta ->
  INR (length (heavy w A beta)) * beta <= 1.
Proof.
  intros Hw Hbeta.
  pose proof (energy_nonneg w A Hw) as HE.
  destruct (Req_dec (energy w A) 0) as [Hz|Hz].
  - assert (Hnil : heavy w A beta = []).
    { destruct (heavy w A beta) as [|i B] eqn:Hhead; [reflexivity|].
      exfalso.
      assert (Hi : In i (heavy w A beta)) by (rewrite Hhead; simpl; auto).
      apply heavy_member in Hi. destruct Hi as [Hi Hlarge].
      pose proof (energy_member_le w A i Hw Hi). rewrite Hz in *; nra. }
    rewrite Hnil; simpl; lra.
  - assert (Hlower : INR (length (heavy w A beta)) *
        (beta * energy w A) <= energy w (heavy w A beta)).
    { apply energy_lower_bound. intros i Hi; apply heavy_member in Hi; lra. }
    pose proof (energy_filter_split w A (is_heavy w A beta)) as Hsplit.
    pose proof (energy_filter_nonneg w A
      (fun i => negb (is_heavy w A beta i)) Hw) as Htail.
    change (energy w A = energy w (heavy w A beta) +
      energy w (remainder w A beta)) in Hsplit.
    change (0 <= energy w (remainder w A beta)) in Htail.
    nra.
Qed.

Lemma peeling_round w A beta :
  NoDup A -> (forall i, In i A -> 0 <= w i) -> 0 <= beta ->
  exists B, incl B A /\ NoDup B /\
    INR (length A - length B) * beta <= 1 /\
    (4 * energy w B < energy w A \/
      forall i, In i B -> w i <= 4 * beta * energy w B).
Proof.
  intros Hnd Hw Hbeta. exists (remainder w A beta).
  split; [apply filter_incl_nat|].
  split; [apply NoDup_filter; exact Hnd|].
  split.
  - pose proof (filter_length_split_nat (is_heavy w A beta) A) as Hlen.
    change (length A = (length (heavy w A beta) +
      length (remainder w A beta))%nat) in Hlen.
    replace (length A - length (remainder w A beta))%nat
      with (length (heavy w A beta)) by lia.
    now apply heavy_count.
  - destruct (Rlt_dec (4 * energy w (remainder w A beta)) (energy w A)).
    + now left.
    + right. intros i Hi. apply remainder_member in Hi.
      destruct Hi as [_ Hi]. nra.
Qed.

Lemma incl_nodup_length_nat (A B : list nat) :
  NoDup A -> incl A B -> (length A <= length B)%nat.
Proof. apply NoDup_incl_length. Qed.

Theorem peeling_iteration w A beta K :
  NoDup A -> (forall i, In i A -> 0 <= w i) -> 0 < beta ->
  exists B, incl B A /\ NoDup B /\
    INR (length A - length B) * beta <= INR K /\
    (energy w B <= energy w A / (4 ^ K) \/
      forall i, In i B -> w i <= 4 * beta * energy w B).
Proof.
  revert A. induction K as [|K IH]; intros A Hnd Hw Hbeta.
  - exists A. split; [apply incl_refl|]. split; [exact Hnd|].
    split; [rewrite Nat.sub_diag; simpl; lra|].
    left; simpl; unfold Rdiv; rewrite Rinv_1; lra.
  - destruct (peeling_round w A beta Hnd Hw (Rlt_le _ _ Hbeta))
      as [B [HBA [HndB [Hcount Hround]]]].
    assert (HwB : forall i, In i B -> 0 <= w i)
      by (intros i Hi; apply Hw; apply HBA; exact Hi).
    destruct Hround as [Hdec|Hcap].
    + destruct (IH B HndB HwB Hbeta)
        as [C [HCB [HndC [HcountC Hresult]]]].
      exists C. split; [eapply incl_tran; eauto|].
      split; [exact HndC|]. split.
      * assert (HBA_len : (length B <= length A)%nat)
          by (apply incl_nodup_length_nat; assumption).
        assert (HCB_len : (length C <= length B)%nat)
          by (apply incl_nodup_length_nat; assumption).
        replace (length A - length C)%nat with
          ((length A - length B) + (length B - length C))%nat by lia.
        rewrite plus_INR, S_INR; nra.
      * destruct Hresult as [Hsmall|Hcap]; [left|now right].
        assert (Hp : 0 < 4 ^ K) by (apply pow_lt; lra).
        pose proof (Rmult_le_compat_r (4 ^ K) _ _ (Rlt_le _ _ Hp) Hsmall) as Hscaled.
        replace (energy w B / 4 ^ K * 4 ^ K) with (energy w B)
          in Hscaled by (field; lra).
        apply (Rmult_le_reg_r (4 * 4 ^ K)); [nra|].
        replace (4 ^ S K) with (4 * 4 ^ K) by reflexivity.
        replace (energy w A / (4 * 4 ^ K) * (4 * 4 ^ K))
          with (energy w A) by (field; lra).
        nra.
    + exists B. split; [exact HBA|]. split; [exact HndB|].
      split; [rewrite S_INR; pose proof (pos_INR K); lra|now right].
Qed.
