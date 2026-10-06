(* Finite sums and lists: the algebra of finite_sum (extensionality on
   members, sums of sums, scalars, opposites, constants, concatenation,
   shifted index ranges, exchange of two sums, absolute values, bounds and
   signs); the reading of List.nth on map g (seq 0 K), on firstn and on
   skipn; and a uniform bound for finitely many matrix entries
   (finite_matrix_bound).

   The module imports Stdlib and SoftDefinitions only, so +, *, nth, map,
   seq and length are Stdlib's, and (i < d)%nat is Peano's lt. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import SoftDefinitions.
Import ListNotations.
Open Scope R_scope.

Lemma finite_sum_ext (f g : nat -> R) I :
  (forall i, In i I -> f i = g i) -> finite_sum f I = finite_sum g I.
Proof.
  induction I as [|i I IH]; intros H; [reflexivity|].
  simpl; rewrite (H i (or_introl eq_refl)), IH; [reflexivity|].
  intros j Hj; apply H; right; exact Hj.
Qed.

Lemma finite_sum_plus (f g : nat -> R) I :
  finite_sum (fun i => f i + g i) I = finite_sum f I + finite_sum g I.
Proof. induction I as [|i I IH]; simpl; [ring|rewrite IH; ring]. Qed.

Lemma finite_sum_scale (c : R) (f : nat -> R) I :
  finite_sum (fun i => c * f i) I = c * finite_sum f I.
Proof. induction I as [|i I IH]; simpl; [ring|rewrite IH; ring]. Qed.

Lemma finite_sum_scale_r (c : R) (f : nat -> R) I :
  finite_sum (fun i => f i * c) I = finite_sum f I * c.
Proof. induction I as [|i I IH]; simpl; [ring|rewrite IH; ring]. Qed.

Lemma finite_sum_minus (f g : nat -> R) I :
  finite_sum (fun i => f i - g i) I = finite_sum f I - finite_sum g I.
Proof. induction I as [|i I IH]; simpl; [ring|rewrite IH; ring]. Qed.

Lemma finite_sum_zero I : finite_sum (fun _ => 0) I = 0.
Proof. induction I as [|i I IH]; simpl; [ring|rewrite IH; ring]. Qed.

Lemma finite_sum_const (c : R) I : finite_sum (fun _ => c) I = INR (length I) * c.
Proof.
  induction I as [|i I IH]; [simpl; ring|].
  simpl finite_sum; simpl length; rewrite IH, S_INR; ring.
Qed.

Lemma finite_sum_app (f : nat -> R) I J :
  finite_sum f (I ++ J) = finite_sum f I + finite_sum f J.
Proof. induction I as [|i I IH]; simpl; [ring|rewrite IH; ring]. Qed.

Lemma finite_sum_seq_shift (f : nat -> R) p q :
  finite_sum f (seq p q) = finite_sum (fun k => f (p + k)%nat) (seq 0 q).
Proof.
  revert f p; induction q as [|q IH]; intros f p; [reflexivity|].
  simpl; rewrite (IH f (S p)), (IH (fun k => f (p + k)%nat) 1%nat).
  rewrite Nat.add_0_r; f_equal.
  apply finite_sum_ext; intros k _; f_equal; lia.
Qed.

Lemma finite_sum_seq_split (f : nat -> R) p q :
  finite_sum f (seq 0 (p + q)) =
  finite_sum f (seq 0 p) + finite_sum (fun k => f (p + k)%nat) (seq 0 q).
Proof.
  rewrite seq_app, finite_sum_app, Nat.add_0_l, (finite_sum_seq_shift f p q); reflexivity.
Qed.

Lemma finite_sum_seq_S (f : nat -> R) j :
  finite_sum f (seq 0 (S j)) = finite_sum f (seq 0 j) + f j.
Proof. rewrite seq_S, finite_sum_app, Nat.add_0_l; simpl; ring. Qed.

Lemma finite_sum_swap (f : nat -> nat -> R) I J :
  finite_sum (fun i => finite_sum (fun j => f i j) J) I =
  finite_sum (fun j => finite_sum (fun i => f i j) I) J.
Proof.
  induction I as [|i I IH]; simpl.
  - rewrite finite_sum_zero; reflexivity.
  - rewrite IH, finite_sum_plus; reflexivity.
Qed.

Lemma finite_sum_abs_le (f : nat -> R) I :
  Rabs (finite_sum f I) <= finite_sum (fun i => Rabs (f i)) I.
Proof.
  induction I as [|i I IH]; simpl.
  - rewrite Rabs_R0; lra.
  - eapply Rle_trans; [apply Rabs_triang|lra].
Qed.

Lemma finite_sum_le (f g : nat -> R) I :
  (forall i, In i I -> f i <= g i) -> finite_sum f I <= finite_sum g I.
Proof.
  induction I as [|i I IH]; intros H; simpl; [lra|].
  specialize (IH (fun j Hj => H j (or_intror Hj))).
  specialize (H i (or_introl eq_refl)); lra.
Qed.

Lemma finite_sum_nonneg (f : nat -> R) I :
  (forall i, In i I -> 0 <= f i) -> 0 <= finite_sum f I.
Proof.
  intros H; rewrite <- (finite_sum_zero I); apply finite_sum_le; exact H.
Qed.

Lemma finite_sum_bound (f : nat -> R) I M :
  (forall i, In i I -> Rabs (f i) <= M) ->
  Rabs (finite_sum f I) <= INR (length I) * M.
Proof.
  intros H; eapply Rle_trans; [apply finite_sum_abs_le|].
  rewrite <- (finite_sum_const M I); apply finite_sum_le; exact H.
Qed.

Lemma in_seq_lt i K : In i (seq 0 K) -> (i < K)%nat.
Proof. intros H; apply in_seq in H; lia. Qed.

Lemma lt_in_seq i K : (i < K)%nat -> In i (seq 0 K).
Proof. intros H; apply in_seq; lia. Qed.

(* List.nth on the list of the values of g at 0, ..., K-1. *)
Lemma length_map_seq {A : Type} (g : nat -> A) K : length (map g (seq 0 K)) = K.
Proof. rewrite length_map, length_seq; reflexivity. Qed.

Lemma nth_map_seq (g : nat -> R) K a :
  (a < K)%nat -> nth a (map g (seq 0 K)) 0 = g a.
Proof.
  intros Ha.
  rewrite (nth_indep _ 0 (g 0%nat)) by (rewrite length_map_seq; exact Ha).
  rewrite map_nth, seq_nth by exact Ha; reflexivity.
Qed.

Lemma nth_firstn_lt (xs : list R) p k :
  (k < p)%nat -> nth k (firstn p xs) 0 = nth k xs 0.
Proof.
  revert p k; induction xs as [|x xs IH]; intros p k Hk.
  - rewrite firstn_nil; reflexivity.
  - destruct p as [|p]; [lia|]. destruct k as [|k]; simpl; [reflexivity|].
    apply IH; lia.
Qed.

Lemma nth_skipn_add (xs : list R) p k : nth k (skipn p xs) 0 = nth (p + k) xs 0.
Proof.
  revert p k; induction xs as [|x xs IH]; intros p k.
  - rewrite skipn_nil; destruct (p + k)%nat, k; reflexivity.
  - destruct p as [|p]; simpl; [reflexivity|apply IH].
Qed.

Lemma list_nth_ext (xs ys : list R) :
  length xs = length ys ->
  (forall i, (i < length xs)%nat -> nth i xs 0 = nth i ys 0) -> xs = ys.
Proof. intros HL H; apply (nth_ext xs ys 0 0 HL H). Qed.

(* A uniform bound for the entries P a k, a < K, k < p. *)
Lemma finite_row_bound (c : nat -> R) p :
  exists M, 0 <= M /\ forall k, (k < p)%nat -> Rabs (c k) <= M.
Proof.
  induction p as [|p [M [HM Hb]]].
  - exists 0; split; [lra|intros k Hk; lia].
  - exists (Rmax M (Rabs (c p))); split.
    + apply Rle_trans with M; [exact HM|apply Rmax_l].
    + intros k Hk. destruct (Nat.eq_dec k p) as [->|Hne]; [apply Rmax_r|].
      apply Rle_trans with M; [apply Hb; lia|apply Rmax_l].
Qed.

Lemma finite_matrix_bound (P : nat -> nat -> R) K p :
  exists M, 0 <= M /\ forall a k, (a < K)%nat -> (k < p)%nat -> Rabs (P a k) <= M.
Proof.
  induction K as [|K [M [HM Hb]]].
  - exists 0; split; [lra|intros a k Ha; lia].
  - destruct (finite_row_bound (P K) p) as [M' [HM' Hb']].
    exists (Rmax M M'); split.
    + apply Rle_trans with M; [exact HM|apply Rmax_l].
    + intros a k Ha Hk. destruct (Nat.eq_dec a K) as [->|Hne].
      * apply Rle_trans with M'; [apply Hb'; exact Hk|apply Rmax_r].
      * apply Rle_trans with M; [apply Hb; [lia|exact Hk]|apply Rmax_l].
Qed.
