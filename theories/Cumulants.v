From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights ThirdDefinitions.
Import ListNotations.
Open Scope R_scope.

Lemma gibbs_average_zero (c : R) (f : nat -> R) (I : list nat) :
  gibbs_average c f I (fun _ => 0) = 0.
Proof.
  unfold gibbs_average; transitivity (finite_sum (fun _ => 0) I).
  - apply gibbs_sum_ext; intros; ring.
  - apply gibbs_sum_zero.
Qed.

Lemma gibbs_average_product_comm (c : R) (f : nat -> R) (I : list nat)
    (u v : nat -> R) :
  gibbs_average c f I (fun i => u i * v i) =
  gibbs_average c f I (fun i => v i * u i).
Proof. apply gibbs_average_ext; intros; ring. Qed.

Theorem gibbs_covariance_sym (c : R) (f : nat -> R) (I : list nat)
    (u v : nat -> R) :
  gibbs_covariance c f I u v = gibbs_covariance c f I v u.
Proof.
  unfold gibbs_covariance; rewrite (gibbs_average_product_comm c f I u v); ring.
Qed.

Theorem gibbs_covariance_scale_left (c : R) (f : nat -> R) (I : list nat)
    (a : R) (u v : nat -> R) :
  gibbs_covariance c f I (fun i => a * u i) v =
  a * gibbs_covariance c f I u v.
Proof.
  unfold gibbs_covariance.
  assert (HE : gibbs_average c f I (fun i => a * u i * v i) =
    gibbs_average c f I (fun i => a * (u i * v i))).
  { apply gibbs_average_ext; intros; ring. }
  rewrite HE, !gibbs_average_scale; ring.
Qed.

Theorem gibbs_covariance_scale_right (c : R) (f : nat -> R) (I : list nat)
    (a : R) (u v : nat -> R) :
  gibbs_covariance c f I u (fun i => a * v i) =
  a * gibbs_covariance c f I u v.
Proof.
  rewrite (gibbs_covariance_sym c f I u (fun i => a * v i)).
  rewrite gibbs_covariance_scale_left, (gibbs_covariance_sym c f I v u).
  reflexivity.
Qed.

Theorem gibbs_covariance_zero_left (c : R) (f : nat -> R) (I : list nat)
    (u : nat -> R) :
  gibbs_covariance c f I (fun _ => 0) u = 0.
Proof.
  unfold gibbs_covariance.
  assert (HE : gibbs_average c f I (fun i => 0 * u i) =
    gibbs_average c f I (fun _ => 0)).
  { apply gibbs_average_ext; intros; ring. }
  rewrite HE, gibbs_average_zero; ring.
Qed.

Theorem gibbs_covariance_zero_right (c : R) (f : nat -> R) (I : list nat)
    (u : nat -> R) :
  gibbs_covariance c f I u (fun _ => 0) = 0.
Proof. rewrite gibbs_covariance_sym; apply gibbs_covariance_zero_left. Qed.

Theorem gibbs_cumulant3_expanded (c : R) (f : nat -> R) (I : list nat)
    (u v w : nat -> R) :
  I <> [] ->
  gibbs_cumulant3 c f I u v w =
    gibbs_average c f I (fun i => u i * v i * w i) -
    gibbs_average c f I u * gibbs_average c f I (fun i => v i * w i) -
    gibbs_average c f I v * gibbs_average c f I (fun i => u i * w i) -
    gibbs_average c f I w * gibbs_average c f I (fun i => u i * v i) +
    2 * gibbs_average c f I u * gibbs_average c f I v * gibbs_average c f I w.
Proof.
  intros HI; unfold gibbs_cumulant3.
  transitivity (gibbs_average c f I (fun i =>
    u i * v i * w i +
    (- gibbs_average c f I u) * (v i * w i) +
    (- gibbs_average c f I v) * (u i * w i) +
    (- gibbs_average c f I w) * (u i * v i) +
    (gibbs_average c f I u * gibbs_average c f I v) * w i +
    (gibbs_average c f I u * gibbs_average c f I w) * v i +
    (gibbs_average c f I v * gibbs_average c f I w) * u i +
    (- gibbs_average c f I u * gibbs_average c f I v * gibbs_average c f I w))).
  - apply gibbs_average_ext; intros; ring.
  - repeat rewrite gibbs_average_add.
    repeat rewrite gibbs_average_scale.
    rewrite gibbs_average_const by exact HI; ring.
Qed.

Theorem gibbs_cumulant3_covariance (c : R) (f : nat -> R) (I : list nat)
    (u v w : nat -> R) :
  I <> [] ->
  gibbs_covariance c f I (fun i => u i * v i) w -
    gibbs_covariance c f I u w * gibbs_average c f I v -
    gibbs_average c f I u * gibbs_covariance c f I v w =
  gibbs_cumulant3 c f I u v w.
Proof.
  intros HI; rewrite gibbs_cumulant3_expanded by exact HI.
  unfold gibbs_covariance; ring.
Qed.

Theorem gibbs_cumulant3_swap_left (c : R) (f : nat -> R) (I : list nat)
    (u v w : nat -> R) :
  gibbs_cumulant3 c f I u v w = gibbs_cumulant3 c f I v u w.
Proof. unfold gibbs_cumulant3; apply gibbs_average_ext; intros; ring. Qed.

Theorem gibbs_cumulant3_swap_right (c : R) (f : nat -> R) (I : list nat)
    (u v w : nat -> R) :
  gibbs_cumulant3 c f I u v w = gibbs_cumulant3 c f I u w v.
Proof. unfold gibbs_cumulant3; apply gibbs_average_ext; intros; ring. Qed.

Theorem gibbs_third_central_power (c : R) (f : nat -> R) (I : list nat)
    (u : nat -> R) :
  gibbs_third_central c f I u =
  gibbs_average c f I (fun i => (u i - gibbs_average c f I u) ^ 3).
Proof.
  unfold gibbs_third_central, gibbs_cumulant3.
  apply gibbs_average_ext; intros; ring.
Qed.
