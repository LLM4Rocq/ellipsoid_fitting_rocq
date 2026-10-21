(* The SigmaRing instance of the measurable structure of matrices (phase 13,
   the repair of the checks; the user's decision of 15 October 2026,
   reviews/phase13-checker-repair.md, section 7).

   The statements of phase 12, batch 1, name the instance
   matrix_matrix__canonical__measurable_structure_SigmaRing, which the
   HB.instance declaration of library/gaussian/measurable_matrix.v generates
   together with the SemiRingOfSets and Measurable instances of matrices.
   The lemma below names that instance and equates its measurable sets with
   those that matrix_measurable_characterization of
   check/ApplicationsDefinitions.v characterizes: the sigma-algebra generated
   by the boxes whose sides are measurable sets. It is proved by
   reflexivity, so a change of the instance that changes its measurable sets
   makes make check fail. scripts/check_sources.py fixes the code of this
   file (NEW_CHECK_CODE), and the snapshot SnapshotMatrixSigmaRing prints
   the statement of the lemma. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions measure.
From GaussianAnalysis.gaussian Require Import measurable_matrix.

Lemma matrix_sigma_ring_characterization {dT} (T : measurableType dT) m n :
  @measurable _ (@matrix_matrix__canonical__measurable_structure_SigmaRing dT T m n) =
  @measurable _ 'M[T]_(m, n).
Proof. by []. Qed.
