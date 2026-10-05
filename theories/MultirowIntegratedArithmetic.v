From Stdlib Require Import Reals List Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Helper for the challenge multirow_integrated_bound: the real arithmetic of
   the integrated estimate, separated from the analysis. Written by the
   solving session on 30 September 2026; it depends on Stdlib and on
   SoftDefinitions only, and proves nothing about expectations.

   The constants of the statement: with d = INR (S n), M3 = 10 k^3
   (beta+gamma)^2 theta / sqrt d, radius the expected maximum squared radius
   and radius_bound = d + 2 sqrt (d ln N) + 2 ln N,
   - the derivative bound: the derivative of the interpolation is
     sqrt t / (2 d sqrt d) times the sum of the row remainder expectations,
     and that sum is at most 4 M3 radius in absolute value, which gives
     (2 sqrt t / (d sqrt d)) radius M3;
   - the scalar integration lemma of WeightedComparison gives 2 K / 3 from
     the bound K sqrt t, with K = 2 radius M3 / (d sqrt d);
   - the explicit constant: (4 radius / (3 d sqrt d)) M3 is
     (40/3) k^3 (beta+gamma)^2 theta radius / d^2, at most the same with
     radius_bound in place of radius.
   Also the two forms of the unit-vector hypothesis: the statement of the
   integrated bound writes euclidean_norm (y z) I = 1, the expectation
   derivative challenge writes finite_sum (fun i => y z i * y z i) I = 1;
   they are equivalent since euclidean_norm is the square root of that sum. *)

(* |c * s| <= (2 sqrt t / (d sqrt d)) * radius * M3 when c = sqrt t / (2 d sqrt d)
   and |s| <= 4 * M3 * radius, for d > 0, radius >= 0, M3 >= 0, t >= 0. *)
Lemma multirow_integrated_derivative_bound (d t radius M3 s : R) :
  0 < d -> 0 <= t -> 0 <= radius -> 0 <= M3 ->
  Rabs s <= 4 * M3 * radius ->
  Rabs (sqrt t / (2 * d * sqrt d) * s) <= (2 * sqrt t / (d * sqrt d)) * radius * M3.
Proof.
  intros Hd Ht Hr HM Hs.
  assert (Hsd : 0 < sqrt d) by (apply sqrt_lt_R0; exact Hd).
  assert (Hst : 0 <= sqrt t) by apply sqrt_pos.
  rewrite Rabs_mult, (Rabs_right (sqrt t / (2 * d * sqrt d)));
    [|apply Rle_ge; apply Rmult_le_pos; [exact Hst|left; apply Rinv_0_lt_compat; nra]].
  replace ((2 * sqrt t / (d * sqrt d)) * radius * M3) with
    (sqrt t / (2 * d * sqrt d) * (4 * M3 * radius)) by (field; split; lra).
  apply Rmult_le_compat_l; [apply Rmult_le_pos; [exact Hst|left; apply Rinv_0_lt_compat; nra]|exact Hs].
Qed.


(* The same bound in the form K * sqrt t of the scalar integration lemma,
   with K = 2 radius M3 / (d sqrt d). *)
Lemma multirow_integrated_derivative_bound_K (d t radius M3 s : R) :
  0 < d -> 0 <= t -> 0 <= radius -> 0 <= M3 ->
  Rabs s <= 4 * M3 * radius ->
  Rabs (sqrt t / (2 * d * sqrt d) * s) <= (2 * radius * M3 / (d * sqrt d)) * sqrt t.
Proof.
  intros Hd Ht Hr HM Hs.
  assert (Hsd : 0 < sqrt d) by (apply sqrt_lt_R0; exact Hd).
  replace ((2 * radius * M3 / (d * sqrt d)) * sqrt t) with ((2 * sqrt t / (d * sqrt d)) * radius * M3)
    by (field; split; lra).
  apply multirow_integrated_derivative_bound; assumption.
Qed.

(* The scalar lemma's constant: 2 K / 3 with K = 2 radius M3 / (d sqrt d). *)
Lemma multirow_integrated_two_thirds (d radius M3 : R) :
  0 < d ->
  2 * (2 * radius * M3 / (d * sqrt d)) / 3 = (4 * radius / (3 * d * sqrt d)) * M3.
Proof.
  intros Hd; assert (Hsd : 0 < sqrt d) by (apply sqrt_lt_R0; exact Hd).
  field; split; lra.
Qed.

Lemma multirow_integrated_K_nonneg (d radius M3 : R) :
  0 < d -> 0 <= radius -> 0 <= M3 -> 0 <= 2 * radius * M3 / (d * sqrt d).
Proof.
  intros Hd Hr HM; assert (Hsd : 0 < sqrt d) by (apply sqrt_lt_R0; exact Hd).
  apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; nra].
Qed.

(* The explicit constant of the paper: 40/3 k^3 (beta+gamma)^2 theta radius_bound / d^2. *)
Lemma multirow_integrated_explicit_constant (d k beta gamma theta radius radius_bound : R) :
  0 < d -> 0 <= k -> 0 < theta -> 0 <= radius -> radius <= radius_bound ->
  (4 * radius / (3 * d * sqrt d)) * (10 * k ^ 3 * (beta + gamma) ^ 2 * theta / sqrt d) <=
    (40 / 3) * k ^ 3 * (beta + gamma) ^ 2 * theta * radius_bound / d ^ 2.
Proof.
  intros Hd Hk Hth Hr Hrb.
  assert (Hsd : 0 < sqrt d) by (apply sqrt_lt_R0; exact Hd).
  assert (Hdd : sqrt d * sqrt d = d) by (apply sqrt_sqrt; lra).
  set (s := sqrt d) in *.
  assert (Hk3 : 0 <= k ^ 3) by (apply pow_le; exact Hk).
  assert (Hbg : 0 <= (beta + gamma) ^ 2) by apply pow2_ge_0.
  set (C := (40 / 3) * k ^ 3 * (beta + gamma) ^ 2 * theta / d ^ 2).
  assert (HC : 0 <= C).
  { unfold C, Rdiv; apply Rmult_le_pos; [|left; apply Rinv_0_lt_compat; apply pow_lt; exact Hd].
    apply Rmult_le_pos; [|lra]. apply Rmult_le_pos; [|exact Hbg]. apply Rmult_le_pos; [lra|exact Hk3]. }
  apply Rle_trans with (C * radius).
  - right. unfold C. rewrite <- Hdd. field. lra.
  - replace ((40 / 3) * k ^ 3 * (beta + gamma) ^ 2 * theta * radius_bound / d ^ 2) with (C * radius_bound)
      by (unfold C; field; lra).
    apply Rmult_le_compat_l; [exact HC|exact Hrb].
Qed.
