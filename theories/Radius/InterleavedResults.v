(* The maximum squared radius of N independent standard Gaussian vectors of
   R^d, read as the first d coordinates of N consecutive rows of length
   d + D (gaussian_interleaved_expected_maximum_radius). The function
   xs |-> gaussian_maximum_radius N d (row_prefixes N d D xs) of N * (d + D)
   Gaussian coordinates is integrable, has the same expectation as
   gaussian_maximum_radius N d of N * d coordinates (and so has its absolute
   value), is the largest squared norm of the row prefixes, and its
   expectation is at most d + 2 sqrt (d ln N) + 2 ln N. The theorem
   restates the one of Radius.InterleavedRows in a module that imports no
   MathComp library, so that every operation in it is Stdlib's. *)

From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Gaussian.IteratedExpectationDefinitions
  Radius.Definitions Row.CoordinateDefinitions Row.PrefixDefinitions.
From EllipsoidFitting Require Radius.InterleavedRows.
Open Scope R_scope.

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
  exact (Radius.InterleavedRows.gaussian_interleaved_expected_maximum_radius N d D).
Qed.
