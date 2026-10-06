(* Integrability of a test function composed with a linear image. Let g be
   a jointly continuous, polynomially bounded function of K coordinates.
   Composed with the image gaussian_covariance_image K p P, the endpoint of
   the Gaussian interpolation, it stays jointly continuous and polynomially
   bounded, with a constant that depends on a bound M on the entries of P
   (gaussian_covariance_image_regular). So the composition satisfies
   gaussian_covariance_domain (gaussian_covariance_image_domain), by
   gaussian_coordinate_polynomial_domain. The image is a linear image of
   the coordinates (Gaussian.InterpolationCoefficients), and
   Gaussian.CovarianceLinearImages bounds such compositions. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import Soft.Definitions
  Gaussian.IteratedExpectationDefinitions
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinatePolynomialDomain Gaussian.CovarianceDefinitions
  Analysis.FiniteSumAlgebra Gaussian.CovarianceLinearImages
  Gaussian.InterpolationCoefficients.
Import ListNotations.
Open Scope R_scope.

(* Regularity of g composed with an endpoint image. *)
Theorem gaussian_covariance_image_regular K p P M (g : list R -> R) C r :
  0 <= M ->
  (forall a k, (a < K)%coq_nat -> (k < p)%coq_nat -> Rabs (P a k) <= M) ->
  finite_joint_continuous K g -> finite_polynomial_bound K C r g ->
  finite_joint_continuous p (fun xs => g (gaussian_covariance_image K p P xs)) /\
  finite_polynomial_bound p (C * (1 + M * INR p) ^ (r * K)%coq_nat) (r * K)%coq_nat
    (fun xs => g (gaussian_covariance_image K p P xs)).
Proof.
  intros HM HP Hg Hb.
  rewrite gaussian_covariance_image_linear; split.
  - apply linear_image_continuous_comp; exact Hg.
  - apply (linear_image_polynomial_bound_comp _ _ _ M _ _ _ HM HP Hb).
Qed.

Theorem gaussian_covariance_image_domain K p P (g : list R -> R) C r :
  finite_joint_continuous K g -> finite_polynomial_bound K C r g ->
  gaussian_covariance_domain p (fun xs => g (gaussian_covariance_image K p P xs)).
Proof.
  intros Hg Hb.
  destruct (finite_matrix_bound P K p) as [M [HM HP]].
  destruct (gaussian_covariance_image_regular K p P M g C r HM HP Hg Hb) as [Hc Hpb].
  exact (gaussian_coordinate_polynomial_domain _ _ _ _ Hc Hpb).
Qed.
