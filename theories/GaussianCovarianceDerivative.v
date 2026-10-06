(* The derivative of Gaussian interpolation between two covariances. Let
   Z(t) = gaussian_covariance_path K p q P Q t zs be the interpolation
   sqrt t * P xs + sqrt (1 - t) * Q ys, where xs and ys are the first p and
   the last q coordinates of zs. Let f be a continuous function of K
   coordinates whose first and second partial derivatives Df and D2f are
   continuous and, like f, polynomially bounded. For 0 < t < 1, the
   derivative of t |-> E f(Z(t)) is one half of the pairing of
   P P^T - Q Q^T with the expectations E [D2f a b (Z(t))]
   (gaussian_covariance_derivative_clause).

   Z(t, zs) is the linear image of zs by the coefficients coef t, with
   velocity dcoef t and acceleration ddcoef t (GaussianCovariancePath). The
   derivative passes under the expectation by
   finite_gaussian_parameter_differentiation (FiniteGaussianParameter),
   whose hypotheses come from the chain rule and from polynomial bounds
   uniform on a closed subinterval of (0, 1) (gc_expectation_derive). The
   expectation of the velocity sum_c Df c (Z) * sum_k dcoef c k z_k is
   computed with the Stein identity gaussian_iterated_coordinate_first_stein:
   the derivative of Df c (Z(t, zs)) in z_k is sum_b D2f c b (Z) * coef b k,
   and sum_k dcoef c k * coef b k = (1/2) ((P P^T)_cb - (Q Q^T)_cb)
   (gc_velocity_expectation). MathComp is loaded, so %coq_nat marks
   Stdlib's arithmetic on nat. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateTopology
  GaussianCoordinatePolynomialContinuity GaussianCoordinateWeightDefinitions
  GaussianCoordinateWeights GaussianCoordinateDerivativeDefinitions
  GaussianCoordinateStein GaussianCoordinateSteinDomains GaussianFiniteSums
  GaussianCoordinateSuffixAlgebra JointDefinitions FiniteGaussianParameter
  GaussianCovarianceDefinitions GaussianCovarianceSums GaussianCovarianceLinear
  GaussianCovariancePath GaussianCovarianceDomains.
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
