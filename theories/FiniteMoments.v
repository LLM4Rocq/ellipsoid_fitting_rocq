From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights MomentDefinitions.
Import ListNotations.
Open Scope R_scope.

Lemma weighted_average_ext q I f g :
  (forall i, In i I -> f i = g i) ->
  weighted_average q I f = weighted_average q I g.
Proof.
  intros H; unfold weighted_average; apply gibbs_sum_ext.
  intros i Hi; rewrite H by exact Hi; reflexivity.
Qed.

Lemma weighted_average_add q I f g :
  weighted_average q I (fun i => f i + g i) =
  weighted_average q I f + weighted_average q I g.
Proof.
  unfold weighted_average; rewrite <- gibbs_sum_add.
  apply gibbs_sum_ext; intros; ring.
Qed.

Lemma weighted_average_scale q I a f :
  weighted_average q I (fun i => a * f i) = a * weighted_average q I f.
Proof.
  unfold weighted_average; rewrite <- gibbs_sum_scale.
  apply gibbs_sum_ext; intros; ring.
Qed.

Lemma weighted_average_const q I a :
  finite_probability q I -> weighted_average q I (fun _ => a) = a.
Proof.
  intros [_ Hq]; unfold weighted_average.
  transitivity (finite_sum (fun i => a * q i) I).
  - apply gibbs_sum_ext; intros; ring.
  - rewrite gibbs_sum_scale, Hq; ring.
Qed.

Lemma weighted_average_nonnegative q I f :
  finite_probability q I ->
  (forall i, In i I -> 0 <= f i) -> 0 <= weighted_average q I f.
Proof.
  intros [Hq _] Hf; unfold weighted_average; apply gibbs_sum_nonnegative.
  intros i Hi; apply Rmult_le_pos; auto.
Qed.

Lemma weighted_average_monotone q I f g :
  finite_probability q I ->
  (forall i, In i I -> f i <= g i) ->
  weighted_average q I f <= weighted_average q I g.
Proof.
  intros HP H.
  assert (HD : 0 <= weighted_average q I (fun i => g i + (-1) * f i)).
  { apply weighted_average_nonnegative; [exact HP|].
    intros i Hi; specialize (H i Hi); lra. }
  rewrite weighted_average_add, weighted_average_scale in HD; lra.
Qed.

Lemma weighted_average_abs_nonnegative q I u :
  (forall i, In i I -> 0 <= q i) ->
  Rabs (weighted_average q I u) <= weighted_average q I (fun i => Rabs (u i)).
Proof.
  unfold weighted_average; induction I as [|i I IH]; intros Hq; simpl.
  - rewrite Rabs_R0; lra.
  - assert (Hi : 0 <= q i) by (apply Hq; simpl; auto).
    assert (HT : forall j, In j I -> 0 <= q j).
    { intros j Hj; apply Hq; simpl; auto. }
    specialize (IH HT).
    eapply Rle_trans; [apply Rabs_triang|].
    rewrite Rabs_mult, Rabs_pos_eq by exact Hi; lra.
Qed.

Theorem weighted_average_abs q I u :
  finite_probability q I ->
  Rabs (weighted_average q I u) <= weighted_average q I (fun i => Rabs (u i)).
Proof. intros [Hq _]; apply weighted_average_abs_nonnegative; exact Hq. Qed.

Lemma cubic_young_nonnegative (x y : R) :
  0 <= x -> 0 <= y -> 3 * x ^ 2 * y <= 2 * x ^ 3 + y ^ 3.
Proof.
  intros Hx Hy.
  assert (H : 0 <= (x - y) ^ 2 * (2 * x + y)).
  { apply Rmult_le_pos; [apply pow2_ge_0|lra]. }
  nra.
Qed.

Theorem weighted_cubic_jensen q I r :
  finite_probability q I -> (forall i, In i I -> 0 <= r i) ->
  (weighted_average q I r) ^ 3 <= weighted_average q I (fun i => r i ^ 3).
Proof.
  intros HP Hr.
  set (m := weighted_average q I r).
  assert (Hm : 0 <= m) by (unfold m; apply weighted_average_nonnegative; assumption).
  assert (Ht : forall i, In i I ->
    m ^ 3 + (3 * m ^ 2) * r i + (-3 * m ^ 3) <= r i ^ 3).
  { intros i Hi; specialize (Hr i Hi).
    assert (Hs : 0 <= (r i - m) ^ 2 * (r i + 2 * m)).
    { apply Rmult_le_pos; [apply pow2_ge_0|lra]. }
    nra. }
  pose proof (weighted_average_monotone q I
    (fun i => m ^ 3 + (3 * m ^ 2) * r i + (-3 * m ^ 3))
    (fun i => r i ^ 3) HP Ht) as H.
  rewrite !weighted_average_add, weighted_average_scale in H.
  repeat rewrite weighted_average_const in H by exact HP.
  fold m in H; nra.
Qed.

Theorem weighted_moment_product q I r :
  finite_probability q I -> (forall i, In i I -> 0 <= r i) ->
  weighted_average q I (fun i => r i ^ 2) * weighted_average q I r <=
  weighted_average q I (fun i => r i ^ 3).
Proof.
  intros HP Hr.
  assert (Hj : forall j, In j I ->
    (3 * weighted_average q I (fun i => r i ^ 2)) * r j <=
    2 * weighted_average q I (fun i => r i ^ 3) + r j ^ 3).
  { intros j Hin.
    assert (Hpt : forall i, In i I ->
      (3 * r j) * r i ^ 2 <= 2 * r i ^ 3 + r j ^ 3).
    { intros i Hi; pose proof (cubic_young_nonnegative (r i) (r j) (Hr i Hi) (Hr j Hin)); nra. }
    pose proof (weighted_average_monotone q I
      (fun i => (3 * r j) * r i ^ 2)
      (fun i => 2 * r i ^ 3 + r j ^ 3) HP Hpt) as H.
    rewrite weighted_average_add, !weighted_average_scale in H.
    rewrite weighted_average_const in H by exact HP; nra. }
  pose proof (weighted_average_monotone q I
    (fun j => (3 * weighted_average q I (fun i => r i ^ 2)) * r j)
    (fun j => 2 * weighted_average q I (fun i => r i ^ 3) + r j ^ 3) HP Hj) as H.
  rewrite weighted_average_add, weighted_average_scale in H.
  rewrite weighted_average_const in H by exact HP; nra.
Qed.

Lemma cubic_sum_bound (a b : R) :
  0 <= a -> 0 <= b -> (a + b) ^ 3 <= 4 * (a ^ 3 + b ^ 3).
Proof.
  intros Ha Hb.
  assert (H : 0 <= (a - b) ^ 2 * (a + b)).
  { apply Rmult_le_pos; [apply pow2_ge_0|lra]. }
  nra.
Qed.

(* This scalar envelope also applies once a normed-space argument bounds a
   centered norm by an original norm plus its finite weighted average. *)
Theorem weighted_cubic_envelope q I r z :
  finite_probability q I ->
  (forall i, In i I -> 0 <= r i) ->
  (forall i, In i I -> 0 <= z i) ->
  (forall i, In i I -> z i <= r i + weighted_average q I r) ->
  weighted_average q I (fun i => z i ^ 3) <=
    8 * weighted_average q I (fun i => r i ^ 3).
Proof.
  intros HP Hr Hz Hcap.
  set (m := weighted_average q I r).
  assert (Hm : 0 <= m) by (unfold m; apply weighted_average_nonnegative; assumption).
  assert (Hj : m ^ 3 <= weighted_average q I (fun i => r i ^ 3))
    by (unfold m; apply weighted_cubic_jensen; assumption).
  assert (Hpt : forall i, In i I -> z i ^ 3 <= 4 * (r i ^ 3 + m ^ 3)).
  { intros i Hi; eapply Rle_trans with (r2 := (r i + m) ^ 3).
    - apply pow_incr; split; [apply Hz; exact Hi|apply Hcap; exact Hi].
    - apply cubic_sum_bound; [apply Hr; exact Hi|exact Hm]. }
  pose proof (weighted_average_monotone q I (fun i => z i ^ 3)
    (fun i => 4 * (r i ^ 3 + m ^ 3)) HP Hpt) as H.
  rewrite weighted_average_scale, weighted_average_add in H.
  rewrite weighted_average_const in H by exact HP; lra.
Qed.
