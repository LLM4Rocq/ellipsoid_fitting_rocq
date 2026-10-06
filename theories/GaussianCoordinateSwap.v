(* Exchanging two adjacent coordinates does not change the iterated Gaussian
   expectation of a continuous function F of polynomial growth
   (gaussian_iterated_swap_adjacent; gaussian_iterated_swap_head is the case
   of the first two coordinates). Both are instances of
   gaussian_iterated_swap_adjacent_gauss of GaussianLawBridge: the iterated
   expectation is an integral against the standard Gaussian measure, which
   is invariant under permutations of the coordinates. *)

From Stdlib Require Import Reals List Lia.
From EllipsoidFitting Require Import GaussianProductDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinatePermutationDefinitions.
From EllipsoidFitting Require GaussianLawBridge.
Open Scope R_scope.

Lemma gaussian_iterated_swap_head n F C p :
  finite_joint_continuous (S (S n)) F ->
  finite_polynomial_bound (S (S n)) C p F ->
  gaussian_iterated_expectation (S (S n)) F =
    gaussian_iterated_expectation (S (S n)) (fun xs => F (swap_adjacent 0 xs)).
Proof.
  intros HC HB.
  apply (GaussianLawBridge.gaussian_iterated_swap_adjacent_gauss (S (S n)) 0 F C p);
    [lia | exact HC | exact HB].
Qed.
