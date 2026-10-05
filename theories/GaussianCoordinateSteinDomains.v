(* Integrability of a function of d Gaussian coordinates under a polynomial
   bound. gaussian_coordinate_polynomial_domain: if F : list R -> R is
   jointly continuous in d coordinates and, on the lists of length d,
   |F xs| <= C * prod_i (1 + |x_i|) ^ p, then F and |F| are integrable at
   every level of the iterated Gaussian expectation over d coordinates,
   and their iterated expectations are actual integrals
   (gaussian_iterated_has_expectation). The integrals are Lebesgue
   integrals, which require absolute integrability. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions GaussianCoordinateWeights
  GaussianCoordinateMarginals GaussianCoordinatePolynomialContinuity
  GaussianCoordinateDerivativeDefinitions GaussianCoordinateStein.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_coordinate_polynomial_domain d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_integrable d F /\ gaussian_iterated_absolutely_integrable d F /\
  gaussian_iterated_has_expectation d F (gaussian_iterated_expectation d F) /\
  gaussian_iterated_has_expectation d (fun xs => Rabs (F xs))
    (gaussian_iterated_expectation d (fun xs => Rabs (F xs))).
Proof.
  intros HC HB.
  destruct (gaussian_iterated_polynomial_admissible d F C p HC HB)
    as [HI [HA [HV [HAV Hbound]]]].
  repeat split; assumption.
Qed.
