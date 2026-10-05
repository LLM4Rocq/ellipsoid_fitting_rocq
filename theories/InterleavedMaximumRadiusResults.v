(* Port of theories/InterleavedMaximumRadiusResults.v from Coquelicot to
   MathComp-Analysis. It proves the restated challenge
   analysis/challenges/interleaved_maximum_radius/Challenge.v.

   The theorem gaussian_interleaved_expected_maximum_radius has exactly the
   text of the frozen statement, under the imports of Challenge.v in the
   same order. The only change to the file is that the import line
   "From Coquelicot Require Import Coquelicot." is dropped: no statement or
   proof here names a Coquelicot notion. The proof is the original one: it
   applies the theorem of the same name of the ported
   InterleavedMaximumRadius, whose text is, byte for byte, this statement.

   This module imports no MathComp library itself, and none of its imports
   re-exports one, as in Challenge.v. So (0<N)%nat, (0<d)%nat and (i<N)%nat
   are Peano's lt, N*(d+D) and N*d are Nat.mul and Nat.add, ln is Stdlib's
   Rpower.ln, and firstn, length, sqrt, INR, Rabs and the operations on R are
   Stdlib's, as in the original and in the statement.

   Assumptions. Stdlib defines Rpower.ln through ln_exists, whose proof uses
   Stdlib.Logic.Classical_Prop.classic, so the theorem carries that axiom
   besides the seven of analysis/README.md. *)

From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import GaussianProductDefinitions MaximumRadiusDefinitions
  RowCoordinateDefinitions RowMarginalDefinitions.
From EllipsoidFitting Require InterleavedMaximumRadius.
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
  exact (InterleavedMaximumRadius.gaussian_interleaved_expected_maximum_radius N d D).
Qed.
