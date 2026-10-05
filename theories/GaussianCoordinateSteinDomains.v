(* Port of theories/GaussianCoordinateSteinDomains.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order
   and its text. The only change to the file is that the import line
   "From Coquelicot Require Import Coquelicot." is dropped: no statement or
   proof here names a Coquelicot notion. The proofs are the original ones,
   word for word.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So (i <= d)%nat is Peano's le, nth is Stdlib's List.nth,
   and the list notations and the operations on R are Stdlib's, as in the
   original. The ported lemmas that the proofs apply write (i < d)%coq_nat
   and List.nth, which elaborate to the same terms.

   The meaning of the statements follows the ported definitions they use.
   finite_joint_continuous (GaussianCoordinateDefinitions) and
   finite_polynomial_bound (GaussianCoordinateWeightDefinitions) have their
   original texts and involve no integral. finite_coordinate_derivative
   (GaussianCoordinateDerivativeDefinitions) says that each coordinate
   section has MathComp's derivative @is_derive R R^o R^o t 1 in place of
   Coquelicot's is_derive; both are the ordinary derivative of a function
   R -> R, so the hypothesis means what it meant.
   gaussian_iterated_integrable, gaussian_iterated_absolutely_integrable,
   gaussian_iterated_has_expectation and gaussian_iterated_expectation
   (GaussianProductDefinitions) now ask at each level for the Lebesgue
   integral over the line against the Gaussian kernel, in place of the
   improper Riemann integral (difference 4 of analysis/README.md). Every
   function in the conclusions is continuous and bounded by a constant times
   a polynomial weight, so it is absolutely integrable against the kernel,
   where the two integrals agree. The conclusions are therefore the Lebesgue
   counterparts of the original ones, under the same hypotheses. That the
   two integrals agree is a mathematical argument and is not proved in
   Rocq. No statement is weakened.

   The proofs use gaussian_iterated_polynomial_admissible (ported
   GaussianCoordinateMarginals), finite_joint_continuous_times_coordinate,
   finite_joint_continuous_times_centered_square and
   finite_joint_continuous_times_two_coordinates (ported
   GaussianCoordinatePolynomialContinuity),
   finite_polynomial_bound_times_coordinate,
   finite_polynomial_bound_times_centered_square and
   finite_polynomial_bound_times_two_coordinates (ported
   GaussianCoordinateWeights), and gaussian_iterated_coordinate_first_stein,
   gaussian_iterated_coordinate_second_stein and
   gaussian_iterated_coordinate_mixed_stein (ported GaussianCoordinateStein).
   Their statements are the original texts, up to the %coq_nat, List.nth and
   derivative notations described above. *)

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
