From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Soft.Definitions Matrix.Definitions
  Matrix.OperatorDefinitions Goe.Definitions
  Gaussian.IteratedExpectationDefinitions
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinatePolynomialDomain Row.ObservableDefinitions
  Row.ObservableContinuity Row.ObservableBounds.
Import ListNotations.
Open Scope R_scope.

(* Regularity of the row observables under the hypotheses of
   Row.ObservableBounds. Let 0 < beta, 0 < gamma, Y and S be nonempty, each
   y z be a unit vector, the operator norms of the B s be at most k, and
   i <= m. Then gaussian_row_velocity and gaussian_row_remainder are jointly
   continuous functions of S m * (S n + S (goe_vector_index n)) coordinates,
   bounded by polynomials of degree 2 (gaussian_row_observables_regular).
   Multirow.ObservableBounds proves the same without the hypotheses on y and
   B. This module loads no MathComp library, so (i<=m)%nat is Stdlib's le
   and + and * on nat are Nat.add and Nat.mul. The lemmas it applies write
   the dimension with %coq_nat; the two forms are convertible. *)

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
