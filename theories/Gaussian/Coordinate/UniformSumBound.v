(* A polynomial bound for a finite sum of functions of d coordinates: if
   every F i, for i in the list I, satisfies finite_polynomial_bound d C p
   with C >= 0, then xs |-> finite_sum (fun i => F i xs) I satisfies
   finite_polynomial_bound d (length I * C) p
   (finite_polynomial_bound_sum_uniform). *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import Soft.Definitions
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  Gaussian.Coordinate.PolynomialContinuity
  Gaussian.Coordinate.WeightDefinitions Gaussian.Coordinate.Weights
  Gaussian.Coordinate.DerivativeDefinitions Gaussian.Iterated.Stein
  Gaussian.Iterated.PolynomialDomain Gaussian.Iterated.FiniteSums
  Gaussian.Iterated.SuffixAlgebra Joint.Definitions
  Gaussian.Iterated.ParameterDifferentiation Gaussian.Covariance.Definitions
  Analysis.FiniteSumAlgebra Gaussian.Covariance.LinearImages
  Gaussian.Covariance.InterpolationCoefficients
  Gaussian.Covariance.PathDomains.
Import ListNotations.
Open Scope R_scope.

(* A polynomial bound of a finite sum with one constant for every term. *)
Lemma finite_polynomial_bound_sum_uniform d I (F : nat -> list R -> R) C p :
  0 <= C ->
  (forall i, In i I -> finite_polynomial_bound d C p (F i)) ->
  finite_polynomial_bound d (INR (List.length I) * C) p
    (fun xs => finite_sum (fun i => F i xs) I).
Proof.
  intros HC HF; split.
  - apply Rmult_le_pos; [apply pos_INR|exact HC].
  - intros xs Hxs.
    rewrite Rmult_assoc.
    apply finite_sum_bound; intros i Hi.
    exact (proj2 (HF i Hi) xs Hxs).
Qed.
