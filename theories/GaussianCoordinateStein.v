(* Gaussian integration by parts in one coordinate, for the iterated
   Gaussian expectation E = gaussian_iterated_expectation (S d) of a
   function of S d coordinates. Let i <= d and write x_i for nth i xs 0.
   - gaussian_iterated_coordinate_first_stein: E [DF] = E [x_i * F] when DF
     is the derivative of F in coordinate i.
   - gaussian_iterated_coordinate_second_stein:
     E [DDF] = E [(x_i * x_i - 1) * F] when DF is the derivative of F and
     DDF that of DF in coordinate i.
   - gaussian_iterated_coordinate_mixed_stein: E [DFiDFj] = E [x_i * x_j * F]
     when i <> j, DFj is the derivative of F in coordinate j and DFiDFj that
     of DFj in coordinate i.
   The hypotheses also bound F and its derivatives by polynomial weights,
   and make F and the derivative integrated on the left continuous. So
   every function integrated is continuous and polynomially bounded, hence
   integrable at each level of E (GaussianCoordinateMarginals).
   The first two identities are Gaussian integration by parts of order one
   and two for the standard Gaussian measure on row vectors
   (gaussian_iterated_coordinate_stein_gauss and
   gaussian_iterated_coordinate_second_stein_gauss of GaussianLawBridge).
   The mixed identity applies the first one twice. *)

From Stdlib Require Import Reals List Lia.
From EllipsoidFitting Require Import GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateWeights GaussianCoordinatePolynomialContinuity
  GaussianCoordinateDerivativeDefinitions GaussianCoordinateDerivatives
  GaussianLawBridge.
Import ListNotations.
Open Scope R_scope.

Theorem gaussian_iterated_coordinate_first_stein d i F DF C p D q :
  (i <= d)%nat ->
  finite_joint_continuous (S d) F -> finite_joint_continuous (S d) DF ->
  finite_polynomial_bound (S d) C p F -> finite_polynomial_bound (S d) D q DF ->
  finite_coordinate_derivative (S d) i F DF ->
  gaussian_iterated_expectation (S d) DF =
  gaussian_iterated_expectation (S d) (fun xs => nth i xs 0 * F xs).
Proof.
  intro Hi; apply gaussian_iterated_coordinate_stein_gauss; lia.
Qed.

Theorem gaussian_iterated_coordinate_second_stein d i F DF DDF C p D q E r :
  (i <= d)%nat ->
  finite_joint_continuous (S d) F -> finite_joint_continuous (S d) DDF ->
  finite_polynomial_bound (S d) C p F -> finite_polynomial_bound (S d) D q DF ->
  finite_polynomial_bound (S d) E r DDF ->
  finite_coordinate_derivative (S d) i F DF ->
  finite_coordinate_derivative (S d) i DF DDF ->
  gaussian_iterated_expectation (S d) DDF =
  gaussian_iterated_expectation (S d) (fun xs => (nth i xs 0*nth i xs 0-1)*F xs).
Proof.
  intro Hi; apply gaussian_iterated_coordinate_second_stein_gauss; lia.
Qed.

Theorem gaussian_iterated_coordinate_mixed_stein d i j F DFj DFiDFj C p D q E r :
  (i <= d)%nat -> (j <= d)%nat -> i <> j ->
  finite_joint_continuous (S d) F -> finite_joint_continuous (S d) DFj ->
  finite_joint_continuous (S d) DFiDFj ->
  finite_polynomial_bound (S d) C p F -> finite_polynomial_bound (S d) D q DFj ->
  finite_polynomial_bound (S d) E r DFiDFj ->
  finite_coordinate_derivative (S d) j F DFj ->
  finite_coordinate_derivative (S d) i DFj DFiDFj ->
  gaussian_iterated_expectation (S d) DFiDFj =
  gaussian_iterated_expectation (S d) (fun xs => nth i xs 0*nth j xs 0*F xs).
Proof.
  intros Hi Hj Hij HCF HCj HCij HF HFj HFij HDj HDij.
  transitivity (gaussian_iterated_expectation (S d) (fun xs => nth i xs 0*DFj xs)).
  - exact (gaussian_iterated_coordinate_first_stein d i DFj DFiDFj D q E r
      Hi HCj HCij HFj HFij HDij).
  - transitivity (gaussian_iterated_expectation (S d) (fun xs => nth j xs 0*(nth i xs 0*F xs))).
    + apply (gaussian_iterated_coordinate_first_stein d j
        (fun xs => nth i xs 0*F xs) (fun xs => nth i xs 0*DFj xs) C (S p) D (S q) Hj).
      * apply finite_joint_continuous_times_coordinate; [exact HCF|lia].
      * apply finite_joint_continuous_times_coordinate; [exact HCj|lia].
      * apply finite_polynomial_bound_times_coordinate; [exact HF|lia].
      * apply finite_polynomial_bound_times_coordinate; [exact HFj|lia].
      * apply finite_coordinate_derivative_times_other; [congruence|exact HDj].
    + apply gaussian_iterated_expectation_ext; intros xs Hxs; ring.
Qed.
