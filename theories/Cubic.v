From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import SoftDefinitions.
Import ListNotations.
Open Scope R_scope.

Lemma cubic_sum_nonnegative (f : nat -> R) (I : list nat) :
  (forall i, In i I -> 0 <= f i) -> 0 <= finite_sum f I.
Proof.
  induction I as [|i I IH]; simpl; intros H.
  - lra.
  - assert (Hi : 0 <= f i) by (apply H; auto).
    assert (Ht : 0 <= finite_sum f I) by (apply IH; intros; apply H; auto).
    lra.
Qed.

Lemma cubic_sum_le (f g : nat -> R) (I : list nat) :
  (forall i, In i I -> f i <= g i) -> finite_sum f I <= finite_sum g I.
Proof.
  induction I as [|i I IH]; simpl; intros H.
  - lra.
  - assert (Hi : f i <= g i) by (apply H; auto).
    assert (Ht : finite_sum f I <= finite_sum g I)
      by (apply IH; intros; apply H; auto).
    lra.
Qed.

Lemma cubic_sum_scale (a : R) (f : nat -> R) (I : list nat) :
  finite_sum (fun i => a * f i) I = a * finite_sum f I.
Proof.
  induction I as [|i I IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma cubic_sum_add (f g : nat -> R) (I : list nat) :
  finite_sum (fun i => f i + g i) I = finite_sum f I + finite_sum g I.
Proof.
  induction I as [|i I IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma cubic_sum_ext (f g : nat -> R) (I : list nat) :
  (forall i, In i I -> f i = g i) -> finite_sum f I = finite_sum g I.
Proof.
  induction I as [|i I IH]; simpl; intros H; [reflexivity |].
  f_equal; [apply H; auto | apply IH; intros; apply H; auto].
Qed.

Lemma cubic_sum_zero (I : list nat) : finite_sum (fun _ => 0) I = 0.
Proof. induction I; simpl; [reflexivity | rewrite IHI; ring]. Qed.

Lemma cubic_sum_swap (f : nat -> nat -> R) (I J : list nat) :
  finite_sum (fun i => finite_sum (f i) J) I =
  finite_sum (fun j => finite_sum (fun i => f i j) I) J.
Proof.
  induction I as [|i I IH]; simpl.
  - symmetry; apply cubic_sum_zero.
  - rewrite cubic_sum_add, <- IH; reflexivity.
Qed.

Lemma cubic_squared_norm_nonnegative (y : nat -> R) (I : list nat) :
  0 <= squared_norm y I.
Proof.
  unfold squared_norm; apply cubic_sum_nonnegative; intros; nra.
Qed.

Lemma cubic_unit_squared_norm (y : nat -> R) (I : list nat) :
  euclidean_norm y I = 1 -> squared_norm y I = 1.
Proof.
  unfold euclidean_norm; intros H.
  pose proof (sqrt_def (squared_norm y I) (cubic_squared_norm_nonnegative y I)) as Hsq.
  rewrite H in Hsq; nra.
Qed.

(* The bound is valid for arbitrary finite coordinate lists, including []. *)
Theorem cubic_mass_coordinate_cap (y : nat -> R) (I : list nat) (a : R) :
  (forall i, In i I -> Rabs (y i) <= a) ->
  cubic_mass y I <= a * squared_norm y I.
Proof.
  intros Hcap; unfold cubic_mass, squared_norm.
  rewrite <- cubic_sum_scale; apply cubic_sum_le; intros i Hi.
  specialize (Hcap i Hi).
  assert (Habs : Rabs (y i) ^ 2 = y i ^ 2).
  { rewrite <- !Rsqr_pow2, <- Rsqr_abs; reflexivity. }
  pose proof (Rle_0_sqr (y i)) as Hsq.
  replace (Rabs (y i) ^ 3) with (Rabs (y i) * (y i ^ 2)).
  - apply Rmult_le_compat_r; [nra | exact Hcap].
  - rewrite <- Habs; ring.
Qed.

Theorem cubic_mass_unit_cap (y : nat -> R) (I : list nat) (a : R) :
  euclidean_norm y I = 1 ->
  (forall i, In i I -> Rabs (y i) <= a) -> cubic_mass y I <= a.
Proof.
  intros Hunit Hcap.
  pose proof (cubic_mass_coordinate_cap y I a Hcap) as Hbound.
  rewrite (cubic_unit_squared_norm y I Hunit) in Hbound; nra.
Qed.

(* A probability distribution is given concretely by nonnegative weights
   whose finite sum is one. Repeated indices are counted with multiplicity. *)
Theorem weighted_cubic_mass_unit_cap
    (y : nat -> nat -> R) (q : nat -> R) (I Y : list nat) (a : R) :
  (forall k, In k Y -> 0 <= q k) -> finite_sum q Y = 1 ->
  (forall k, In k Y -> euclidean_norm (y k) I = 1) ->
  (forall k i, In k Y -> In i I -> Rabs (y k i) <= a) ->
  finite_sum (fun k => q k * cubic_mass (y k) I) Y <= a.
Proof.
  intros Hq Hsum Hunit Hcap.
  assert (Hbound : finite_sum (fun k => q k * cubic_mass (y k) I) Y <=
                   finite_sum (fun k => a * q k) Y).
  { apply cubic_sum_le; intros k Hk.
    pose proof (cubic_mass_unit_cap (y k) I a (Hunit k Hk)
      (fun i Hi => Hcap k i Hk Hi)) as Hmass.
    specialize (Hq k Hk); nra. }
  rewrite cubic_sum_scale, Hsum in Hbound; nra.
Qed.

Theorem weighted_cubic_mass_low_influence
    (y : nat -> nat -> R) (q : nat -> R) (I Y : list nat)
    (d : nat) (theta : R) :
  (1 <= d)%nat -> 0 < theta ->
  (forall k, In k Y -> 0 <= q k) -> finite_sum q Y = 1 ->
  (forall k, In k Y -> euclidean_norm (y k) I = 1) ->
  (forall k i, In k Y -> In i I -> Rabs (y k i) <= theta / sqrt (INR d)) ->
  finite_sum (fun k => q k * cubic_mass (y k) I) Y <= theta / sqrt (INR d).
Proof.
  intros Hd Htheta; apply weighted_cubic_mass_unit_cap.
Qed.
