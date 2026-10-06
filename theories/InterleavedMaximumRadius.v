(* The maximum squared radius of N rows of d Gaussian coordinates when each
   row is followed by D other coordinates. row_prefixes N d D keeps the
   first d coordinates of each of the N rows of length d + D, and
   gaussian_maximum_radius N d is the maximum over the rows of their sums
   of squares. gaussian_interleaved_maximum_ge_row and
   gaussian_interleaved_maximum_attained: the maximum is at least the
   squared radius of each row and is attained.
   gaussian_interleaved_expected_maximum_radius: its iterated Gaussian
   expectation over the N * (d + D) coordinates exists, equals that over
   the N * d coordinates of the prefixes, and is at most
   d + 2 sqrt (d ln N) + 2 ln N. *)

From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import GaussianProductDefinitions
  RowCoordinateDefinitions RowMarginalDefinitions RowPrefixes GaussianRowMarginal
  MaximumRadiusDefinitions MaximumRadiusRegularity MaximumRadiusResults.
Open Scope R_scope.

Theorem gaussian_interleaved_maximum_ge_row N d D i xs :
  length xs=(N*(d+D))%nat -> (i<N)%nat ->
  gaussian_sum_squares (firstn d (row_chunk (d+D) i xs)) <=
    gaussian_maximum_radius N d (row_prefixes N d D xs).
Proof.
  intros HL Hi; pose proof (gaussian_maximum_radius_ge_row N d i
    (row_prefixes N d D xs) Hi) as H.
  change (gaussian_sum_squares (row_chunk d i (row_prefixes N d D xs)) <=
    gaussian_maximum_radius N d (row_prefixes N d D xs)) in H.
  rewrite row_prefixes_row_chunk in H by assumption; exact H.
Qed.

Theorem gaussian_interleaved_maximum_attained N d D xs :
  length xs=(N*(d+D))%nat -> (0<N)%nat -> exists i, (i<N)%nat /\
  gaussian_maximum_radius N d (row_prefixes N d D xs) =
    gaussian_sum_squares (firstn d (row_chunk (d+D) i xs)).
Proof.
  intros HL HN; destruct (gaussian_maximum_radius_attained N d (row_prefixes N d D xs) HN)
    as [i [Hi HE]].
  exists i; split; [exact Hi|].
  change (gaussian_maximum_radius N d (row_prefixes N d D xs) =
    gaussian_sum_squares (row_chunk d i (row_prefixes N d D xs))) in HE.
  rewrite row_prefixes_row_chunk in HE by assumption; exact HE.
Qed.

Theorem gaussian_interleaved_expected_maximum_radius N d D :
  (0<N)%nat -> (0<d)%nat ->
  gaussian_iterated_integrable (N*(d+D))
    (fun xs=>gaussian_maximum_radius N d (row_prefixes N d D xs)) /\
  gaussian_iterated_absolutely_integrable (N*(d+D))
    (fun xs=>gaussian_maximum_radius N d (row_prefixes N d D xs)) /\
  gaussian_iterated_has_expectation (N*(d+D))
    (fun xs=>gaussian_maximum_radius N d (row_prefixes N d D xs))
    (gaussian_iterated_expectation (N*d) (gaussian_maximum_radius N d)) /\
  gaussian_iterated_has_expectation (N*(d+D))
    (fun xs=>Rabs(gaussian_maximum_radius N d (row_prefixes N d D xs)))
    (gaussian_iterated_expectation (N*d) (fun xs=>Rabs(gaussian_maximum_radius N d xs))) /\
  gaussian_iterated_expectation (N*(d+D))
    (fun xs=>gaussian_maximum_radius N d (row_prefixes N d D xs)) =
    gaussian_iterated_expectation (N*d) (gaussian_maximum_radius N d) /\
  gaussian_iterated_expectation (N*(d+D))
    (fun xs=>Rabs(gaussian_maximum_radius N d (row_prefixes N d D xs))) =
    gaussian_iterated_expectation (N*d) (fun xs=>Rabs(gaussian_maximum_radius N d xs)) /\
  (forall xs, length xs=(N*(d+D))%nat ->
    (forall i, (i<N)%nat -> gaussian_sum_squares(firstn d(row_chunk(d+D)i xs)) <=
      gaussian_maximum_radius N d(row_prefixes N d D xs)) /\
    (exists i, (i<N)%nat /\ gaussian_maximum_radius N d(row_prefixes N d D xs) =
      gaussian_sum_squares(firstn d(row_chunk(d+D)i xs)))) /\
  gaussian_iterated_expectation (N*(d+D))
    (fun xs=>gaussian_maximum_radius N d(row_prefixes N d D xs)) <=
    INR d+2*sqrt(INR d*ln(INR N))+2*ln(INR N).
Proof.
  intros HN Hd.
  destruct (row_prefixes_gaussian_domain N d D (gaussian_maximum_radius N d)
    (INR(N*d)) 2 (gaussian_maximum_radius_continuous N d)
    (gaussian_maximum_radius_polynomial N d)) as [HI [HA [HV [HAV [HE HEA]]]]].
  split; [exact HI|]. split; [exact HA|]. split; [exact HV|]. split; [exact HAV|].
  split; [exact HE|]. split; [exact HEA|]. split.
  - intros xs HL; split.
    + intros i Hi; apply gaussian_interleaved_maximum_ge_row; assumption.
    + apply gaussian_interleaved_maximum_attained; assumption.
  - rewrite HE; exact (proj2 (proj2 (proj2 (proj2 (proj2
      (gaussian_expected_maximum_radius N d HN Hd)))))).
Qed.
