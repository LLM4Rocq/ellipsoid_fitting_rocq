(* The expected maximum radius of N independent standard Gaussian vectors
   of dimension d. gaussian_maximum_radius N d xs is the largest squared
   Euclidean norm of the N consecutive blocks of d coordinates of xs. It
   bounds every block (gaussian_maximum_radius_ge_row) and, for N > 0, is
   attained at one (gaussian_maximum_radius_attained). For N > 0 and d > 0
   it is integrable, and its expectation is at most
   INR d + 2 * sqrt (INR d * ln (INR N)) + 2 * ln (INR N)
   (gaussian_expected_maximum_radius). *)

From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import Gaussian.Iterated.Definitions
  Radius.Definitions Radius.Regularity Radius.ExpectedMaximum.
Import ListNotations.
Open Scope R_scope.

Theorem gaussian_maximum_radius_ge_row N d i xs :
  (i<N)%nat ->
  gaussian_sum_squares (firstn d (skipn (i*d) xs)) <= gaussian_maximum_radius N d xs.
Proof.
  revert i xs; induction N as [|N IH]; intros i xs Hi; [lia|].
  destruct i as [|i].
  - change (gaussian_sum_squares (firstn d xs) <=
      Rmax (gaussian_sum_squares (firstn d xs)) (gaussian_maximum_radius N d (skipn d xs))).
    apply Rmax_l.
  - specialize (IH i (skipn d xs) ltac:(lia)).
    rewrite skipn_skipn in IH.
    rewrite Nat.mul_succ_l.
    eapply Rle_trans; [exact IH|apply Rmax_r].
Qed.

Theorem gaussian_maximum_radius_attained N d xs :
  (0<N)%nat -> exists i, (i<N)%nat /\
    gaussian_maximum_radius N d xs = gaussian_sum_squares (firstn d (skipn (i*d) xs)).
Proof.
  revert xs; induction N as [|N IH]; intros xs HN; [lia|].
  destruct N as [|N].
  - exists O; split; [lia|].
    change (Rmax (gaussian_sum_squares (firstn d xs)) 0 = gaussian_sum_squares (firstn d xs)).
    apply Rmax_left, maximum_radius_squares_nonnegative.
  - change (exists i, (i<S(S N))%nat /\
      Rmax (gaussian_sum_squares (firstn d xs))
        (gaussian_maximum_radius (S N) d (skipn d xs)) =
      gaussian_sum_squares (firstn d (skipn (i*d) xs))).
    destruct (Rle_dec (gaussian_maximum_radius (S N) d (skipn d xs))
      (gaussian_sum_squares (firstn d xs))) as [Hle|Hgt].
    + exists O; split; [lia|]. rewrite Rmax_left by exact Hle; reflexivity.
    + destruct (IH (skipn d xs) ltac:(lia)) as [i [Hi HE]].
      exists (S i); split; [lia|]. rewrite Rmax_right by lra.
      rewrite HE, skipn_skipn, Nat.mul_succ_l; reflexivity.
Qed.

Theorem gaussian_expected_maximum_radius N d :
  (0<N)%nat -> (0<d)%nat ->
  gaussian_iterated_integrable (N*d) (gaussian_maximum_radius N d) /\
  gaussian_iterated_absolutely_integrable (N*d) (gaussian_maximum_radius N d) /\
  gaussian_iterated_has_expectation (N*d) (gaussian_maximum_radius N d)
    (gaussian_iterated_expectation (N*d) (gaussian_maximum_radius N d)) /\
  gaussian_iterated_has_expectation (N*d) (fun xs => Rabs (gaussian_maximum_radius N d xs))
    (gaussian_iterated_expectation (N*d) (fun xs => Rabs (gaussian_maximum_radius N d xs))) /\
  (forall xs, length xs=(N*d)%nat ->
    (forall i, (i<N)%nat ->
      gaussian_sum_squares (firstn d (skipn (i*d) xs)) <= gaussian_maximum_radius N d xs) /\
    (exists i, (i<N)%nat /\
      gaussian_maximum_radius N d xs = gaussian_sum_squares (firstn d (skipn (i*d) xs)))) /\
  gaussian_iterated_expectation (N*d) (gaussian_maximum_radius N d) <=
    INR d + 2*sqrt (INR d * ln (INR N)) + 2*ln (INR N).
Proof.
  intros HN Hd.
  destruct (gaussian_maximum_radius_domain N d) as [HI [HA [HV HAV]]].
  split; [exact HI|]. split; [exact HA|]. split; [exact HV|]. split; [exact HAV|].
  split.
  - intros xs Hxs; split.
    + intros i Hi; apply gaussian_maximum_radius_ge_row, Hi.
    + apply gaussian_maximum_radius_attained, HN.
  - apply gaussian_maximum_radius_expected_bound; assumption.
Qed.
