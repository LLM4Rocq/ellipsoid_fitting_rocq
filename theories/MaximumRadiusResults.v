(* Port of theories/MaximumRadiusResults.v from Coquelicot to
   MathComp-Analysis. It proves the restated challenge
   analysis/challenges/maximum_radius/Challenge.v.

   The three theorems keep their names, their arguments in the same order
   and their text. The theorem gaussian_expected_maximum_radius has exactly
   the text of the frozen statement. The only change to the file is that the
   import line "From Coquelicot Require Import Coquelicot." is dropped: no
   statement or proof here names a Coquelicot notion. The proofs are the
   original ones, word for word.

   This module imports no MathComp library itself, and none of its imports
   re-exports one, as in Challenge.v. So (0<N)%nat, (0<d)%nat and (i<N)%nat
   are Peano's lt, N*d and i*d are Nat.mul, ln is Stdlib's Rpower.ln, and
   firstn, skipn, length, sqrt, INR, Rabs and the operations on R are
   Stdlib's, as in the original and in the statement.

   The proofs use gaussian_maximum_radius_domain and
   maximum_radius_squares_nonnegative of the ported MaximumRadiusRegularity
   and gaussian_maximum_radius_expected_bound of the ported
   MaximumRadiusComparison. Their statements have their original texts, up
   to the Rpower.ln qualification in the last one, which is the same
   constant as ln here.

   Assumptions. Stdlib defines Rpower.ln through ln_exists, whose proof uses
   Stdlib.Logic.Classical_Prop.classic, so the main theorem carries that
   axiom besides the seven of analysis/README.md. *)

From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import GaussianProductDefinitions MaximumRadiusDefinitions
  MaximumRadiusRegularity MaximumRadiusComparison.
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
