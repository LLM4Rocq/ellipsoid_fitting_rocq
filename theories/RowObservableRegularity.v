From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions MatrixDefinitions OperatorDefinitions GoeDefinitions
  GaussianProductDefinitions GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateSteinDomains RowObservableDefinitions RowObservableContinuity RowObservableBounds.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/RowObservableRegularity.v from Coquelicot to
   MathComp-Analysis.

   Imports. The original imported Coquelicot and the bundle
   GaussianCoordinateProofs, and opened its inner module
   GaussianCoordinateSteinDomains. The port imports the standalone ported
   module GaussianCoordinateSteinDomains directly, in the place of the
   bundle, and drops the import of Coquelicot: neither statement nor proof
   names a Coquelicot notion. The other imports are those of the original.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So (i<=m)%nat is Stdlib's Peano order le, + and * on nat
   are Nat.add and Nat.mul, seq is Stdlib's List.seq, and the operations on
   R are Stdlib's, as in the original. The two theorems keep their names,
   their arguments in the same order and their texts word for word. No item
   is added.

   The ported RowObservableContinuity and RowObservableBounds write the
   order as (i<=m)%coq_nat, which is the same le, and the dimension as
   (S m * (S n + S (goe_vector_index n)))%coq_nat, which elaborates to
   Nat.mul (S m) (addn (S n) (S (goe_vector_index n))). Here the dimension
   is Nat.mul (S m) (Nat.add (S n) (S (goe_vector_index n))), the term of
   the original. In MathComp 2.6 addn unfolds to Nat.add, so the two terms
   are convertible, and the proofs apply the lemmas of those modules
   unchanged. An importer that loads ssreflect and writes %coq_nat gets the
   addn form, and can use these theorems by conversion.

   The meaning of the statements follows the ported definitions they use.
   finite_joint_continuous (GaussianCoordinateDefinitions) and
   finite_polynomial_bound (GaussianCoordinateWeightDefinitions) have their
   original texts and involve no integral. gaussian_iterated_integrable,
   gaussian_iterated_absolutely_integrable, gaussian_iterated_has_expectation
   and gaussian_iterated_expectation (GaussianProductDefinitions) now ask at
   each level for the Lebesgue integral over the line against the Gaussian
   kernel, in place of the improper Riemann integral (difference 4 of
   analysis/README.md). The proofs are the original ones, word for word.

   Assumptions. The statements mention gaussian_row_velocity and
   gaussian_row_remainder, which are built from lower_block_first and
   lower_block_third, and so from soft_max and Stdlib's Rpower.ln. So
   Print Assumptions lists the seven axioms of analysis/README.md and
   Classical_Prop.classic for both theorems. *)

Theorem gaussian_row_observables_regular n m beta gamma y B Y S k t i :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] -> 0<=k -> (i<=m)%nat ->
  (forall z, In z Y -> euclidean_norm (y z) (seq 0 (Datatypes.S m))=1) ->
  (forall s, In s S -> matrix_operator_norm n (B s)<=k) ->
  finite_joint_continuous (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n)))
    (gaussian_row_velocity n m beta gamma y B Y S t i) /\
  finite_joint_continuous (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n)))
    (gaussian_row_remainder n m beta gamma y B Y S t i) /\
  exists CV CR : R,
    finite_polynomial_bound (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n))) CV 2
      (gaussian_row_velocity n m beta gamma y B Y S t i) /\
    finite_polynomial_bound (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n))) CR 2
      (gaussian_row_remainder n m beta gamma y B Y S t i).
Proof.
  intros Hb Hg HY HS Hk Hi Hy HB; split.
  - apply gaussian_row_velocity_continuous; assumption.
  - split; [apply gaussian_row_remainder_continuous; assumption|].
    apply (gaussian_row_observables_polynomial_bounds n m beta gamma y B Y S k t i); assumption.
Qed.
