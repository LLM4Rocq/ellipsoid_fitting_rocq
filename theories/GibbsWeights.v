From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions.
Import ListNotations.
Open Scope R_scope.

Lemma gibbs_sum_ext (f g : nat -> R) (I : list nat) :
  (forall i, In i I -> f i = g i) -> finite_sum f I = finite_sum g I.
Proof.
  induction I as [|i I IH]; intros H; simpl; [reflexivity|].
  rewrite H by (simpl; auto).
  rewrite IH; [reflexivity|].
  intros j Hj; apply H; simpl; auto.
Qed.

Lemma gibbs_sum_add (f g : nat -> R) (I : list nat) :
  finite_sum (fun i => f i + g i) I = finite_sum f I + finite_sum g I.
Proof. induction I; simpl; [ring|rewrite IHI; ring]. Qed.

Lemma gibbs_sum_scale (a : R) (f : nat -> R) (I : list nat) :
  finite_sum (fun i => a * f i) I = a * finite_sum f I.
Proof. induction I; simpl; [ring|rewrite IHI; ring]. Qed.

Lemma gibbs_sum_zero (I : list nat) : finite_sum (fun _ => 0) I = 0.
Proof. induction I; simpl; lra. Qed.

Lemma gibbs_sum_nonnegative (f : nat -> R) (I : list nat) :
  (forall i, In i I -> 0 <= f i) -> 0 <= finite_sum f I.
Proof.
  induction I as [|i I IH]; intros H; simpl; [lra|].
  assert (Hi : 0 <= f i) by (apply H; simpl; auto).
  assert (HI : 0 <= finite_sum f I).
  { apply IH; intros j Hj; apply H; simpl; auto. }
  lra.
Qed.

Lemma gibbs_sum_member (f : nat -> R) (I : list nat) (i : nat) :
  (forall j, In j I -> 0 <= f j) -> In i I -> f i <= finite_sum f I.
Proof.
  induction I as [|j I IH]; intros H Hin; [contradiction|].
  simpl in Hin |- *.
  assert (Hj : 0 <= f j) by (apply H; simpl; auto).
  assert (HI : forall k, In k I -> 0 <= f k).
  { intros k Hk; apply H; simpl; auto. }
  destruct Hin as [->|Hin].
  - pose proof (gibbs_sum_nonnegative f I HI); lra.
  - specialize (IH HI Hin); lra.
Qed.

Lemma gibbs_sum_const (a : R) (I : list nat) :
  finite_sum (fun _ => a) I = INR (length I) * a.
Proof.
  induction I as [|i I IH]; [simpl; ring|].
  change (a + finite_sum (fun _ => a) I = INR (S (length I)) * a).
  rewrite IH, S_INR; ring.
Qed.

Theorem partition_positive (c : R) (f : nat -> R) (I : list nat) :
  I <> [] -> 0 < partition c f I.
Proof.
  intros H; destruct I as [|i I]; [contradiction|].
  unfold partition; simpl.
  assert (HI : 0 <= finite_sum (fun j => exp (c * f j)) I).
  { apply gibbs_sum_nonnegative; intros; left; apply exp_pos. }
  pose proof (exp_pos (c * f i)); lra.
Qed.

Theorem gibbs_weight_positive (c : R) (f : nat -> R)
    (I : list nat) (i : nat) :
  I <> [] -> 0 < gibbs_weight c f I i.
Proof.
  intros HI; unfold gibbs_weight; apply Rdiv_lt_0_compat.
  - apply exp_pos.
  - apply partition_positive; exact HI.
Qed.

Theorem gibbs_weight_nonnegative (c : R) (f : nat -> R)
    (I : list nat) (i : nat) :
  I <> [] -> 0 <= gibbs_weight c f I i.
Proof. intros HI; left; apply gibbs_weight_positive; exact HI. Qed.

Theorem gibbs_weights_normalized (c : R) (f : nat -> R) (I : list nat) :
  I <> [] -> finite_sum (gibbs_weight c f I) I = 1.
Proof.
  intros HI.
  transitivity (finite_sum (fun i => / partition c f I * exp (c * f i)) I).
  - apply gibbs_sum_ext; intros; unfold gibbs_weight, Rdiv; ring.
  - rewrite gibbs_sum_scale.
    change (/ partition c f I * partition c f I = 1).
    apply Rinv_l; pose proof (partition_positive c f I HI); lra.
Qed.

Theorem gibbs_weight_at_most_one (c : R) (f : nat -> R)
    (I : list nat) (i : nat) :
  I <> [] -> In i I -> gibbs_weight c f I i <= 1.
Proof.
  intros HI Hi.
  rewrite <- (gibbs_weights_normalized c f I HI).
  apply gibbs_sum_member; [|exact Hi].
  intros; apply gibbs_weight_nonnegative; exact HI.
Qed.

Theorem gibbs_average_ratio (c : R) (f : nat -> R) (I : list nat)
    (h : nat -> R) :
  gibbs_average c f I h =
    finite_sum (fun i => exp (c * f i) * h i) I / partition c f I.
Proof.
  unfold gibbs_average, gibbs_weight, Rdiv.
  rewrite Rmult_comm, <- gibbs_sum_scale.
  apply gibbs_sum_ext; intros; ring.
Qed.

Theorem gibbs_average_ext (c : R) (f : nat -> R) (I : list nat)
    (u v : nat -> R) :
  (forall i, In i I -> u i = v i) ->
  gibbs_average c f I u = gibbs_average c f I v.
Proof.
  intros H; unfold gibbs_average; apply gibbs_sum_ext.
  intros i Hi; rewrite H by exact Hi; reflexivity.
Qed.

Theorem gibbs_average_add (c : R) (f : nat -> R) (I : list nat)
    (u v : nat -> R) :
  gibbs_average c f I (fun i => u i + v i) =
    gibbs_average c f I u + gibbs_average c f I v.
Proof.
  unfold gibbs_average; rewrite <- gibbs_sum_add.
  apply gibbs_sum_ext; intros; ring.
Qed.

Theorem gibbs_average_scale (c : R) (f : nat -> R) (I : list nat)
    (a : R) (u : nat -> R) :
  gibbs_average c f I (fun i => a * u i) = a * gibbs_average c f I u.
Proof.
  unfold gibbs_average; rewrite <- gibbs_sum_scale.
  apply gibbs_sum_ext; intros; ring.
Qed.

Theorem gibbs_average_const (c : R) (f : nat -> R) (I : list nat) (a : R) :
  I <> [] -> gibbs_average c f I (fun _ => a) = a.
Proof.
  intros HI; unfold gibbs_average.
  transitivity (finite_sum (fun i => a * gibbs_weight c f I i) I).
  - apply gibbs_sum_ext; intros; ring.
  - rewrite gibbs_sum_scale, gibbs_weights_normalized by exact HI; ring.
Qed.

Theorem gibbs_average_nonnegative (c : R) (f : nat -> R) (I : list nat)
    (u : nat -> R) :
  I <> [] -> (forall i, In i I -> 0 <= u i) ->
  0 <= gibbs_average c f I u.
Proof.
  intros HI Hu; unfold gibbs_average; apply gibbs_sum_nonnegative.
  intros i Hi; apply Rmult_le_pos.
  - apply gibbs_weight_nonnegative; exact HI.
  - apply Hu; exact Hi.
Qed.

Theorem gibbs_covariance_centered (c : R) (f : nat -> R) (I : list nat)
    (u v : nat -> R) :
  I <> [] ->
  gibbs_covariance c f I u v =
  gibbs_average c f I
    (fun i => (u i - gibbs_average c f I u) *
              (v i - gibbs_average c f I v)).
Proof.
  intros HI; unfold gibbs_covariance.
  transitivity (gibbs_average c f I
    (fun i => u i * v i +
       (- gibbs_average c f I v) * u i +
       (- gibbs_average c f I u) * v i +
       gibbs_average c f I u * gibbs_average c f I v)).
  - repeat rewrite gibbs_average_add.
    repeat rewrite gibbs_average_scale.
    rewrite gibbs_average_const by exact HI; ring.
  - apply gibbs_average_ext; intros; ring.
Qed.

Theorem gibbs_variance_nonnegative (c : R) (f : nat -> R)
    (I : list nat) (u : nat -> R) :
  I <> [] -> 0 <= gibbs_variance c f I u.
Proof.
  intros HI; unfold gibbs_variance.
  rewrite gibbs_covariance_centered by exact HI.
  apply gibbs_average_nonnegative; [exact HI|].
  intros i _; cbn; apply Rle_0_sqr.
Qed.
