(* Port of theories/InterleavedMaximumRadius.v from Coquelicot to
   MathComp-Analysis.

   Every theorem keeps its name, its arguments in the same order, and its
   text. The only change to the file is that the import line
   "From Coquelicot Require Import Coquelicot." is dropped: no statement or
   proof here names a Coquelicot notion. The proofs are the original ones,
   word for word.

   The meaning of the statements follows the ported definitions they use.
   gaussian_maximum_radius (MaximumRadiusDefinitions), gaussian_sum_squares
   (GaussianProductDefinitions), row_chunk (RowCoordinateDefinitions) and
   row_prefixes (RowMarginalDefinitions) have the original text, so
   gaussian_interleaved_maximum_ge_row and gaussian_interleaved_maximum_attained
   say what they said before. In gaussian_interleaved_expected_maximum_radius,
   gaussian_iterated_integrable, gaussian_iterated_absolutely_integrable and
   gaussian_iterated_has_expectation (GaussianProductDefinitions) now ask at
   each level for Lebesgue integrability over the line against the Gaussian
   kernel and record Lebesgue integrals against gaussian_density, in place of
   improper Riemann integrals (difference 4 of analysis/README.md). The
   maximum radius composed with row_prefixes is continuous and polynomially
   bounded, so it is absolutely integrable and the two notions agree on it.
   No statement is weakened. The text of the last theorem is, byte for byte,
   the statement of analysis/challenges/interleaved_maximum_radius/Challenge.v.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So firstn, length, the %nat scope, ln (Stdlib's
   Rpower.ln) and the operations on R are Stdlib's, as in the original. *)

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
