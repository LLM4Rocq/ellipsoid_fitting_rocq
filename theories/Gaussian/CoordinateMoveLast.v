(* Moving a coordinate to the last place does not change an iterated
   Gaussian expectation. If F, a function of d coordinates, is jointly
   continuous and polynomially bounded, and i < d, then
   gaussian_iterated_move_last states
   E [F] = E [fun xs => F (move_coordinate_last i xs)], where
   move_coordinate_last i moves coordinate i to the end of the list.
   The proof is by induction on d. For i > 0 it applies the induction
   hypothesis inside the first integral. For i = 0 it first moves
   coordinate 1 to the end in the same way, then swaps the first two
   coordinates (gaussian_iterated_swap_head, move_coordinate_last_zero_step). *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions Gaussian.Expectation
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  Gaussian.CoordinateWeightDefinitions Gaussian.CoordinateWeights
  Gaussian.CoordinateMarginals Analysis.CoordinatePermutationDefinitions
  Analysis.CoordinatePermutations Analysis.CoordinatePermutationContinuity
  Gaussian.PermutationWeights Gaussian.CoordinateSuffixAlgebra
  Gaussian.CoordinateSwap.
Import ListNotations.
Open Scope R_scope.

Lemma move_coordinate_last_zero_step xs :
  move_coordinate_last 0 xs = move_coordinate_last 1 (swap_adjacent 0 xs).
Proof. destruct xs as [|x [|y xs]]; reflexivity. Qed.

Theorem gaussian_iterated_move_last d i F C p :
  (i < d)%nat -> finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_expectation d F =
    gaussian_iterated_expectation d (fun xs => F (move_coordinate_last i xs)).
Proof.
  revert i F C; induction d as [|d IH]; intros i F C Hi HC HB; [lia|].
  destruct i as [|i].
  - destruct d as [|n].
    + apply gaussian_iterated_expectation_ext; intros xs Hxs.
      destruct xs as [|x [|y xs]]; simpl in Hxs; try discriminate; reflexivity.
    + transitivity (gaussian_iterated_expectation (S (S n))
        (fun xs => F (move_coordinate_last 1 xs))).
      * change (gaussian_expectation (fun x => gaussian_iterated_expectation (S n)
          (fun xs => F (x::xs))) =
          gaussian_expectation (fun x => gaussian_iterated_expectation (S n)
          (fun xs => F (x::move_coordinate_last 0 xs)))).
        apply (f_equal gaussian_expectation); apply functional_extensionality; intro x.
        apply (IH O (fun xs => F (x::xs)) (C*gaussian_coordinate_weight p x)).
        -- lia.
        -- apply finite_joint_continuous_head, HC.
        -- apply finite_polynomial_bound_head, HB.
      * transitivity (gaussian_iterated_expectation (S (S n))
          (fun xs => F (move_coordinate_last 1 (swap_adjacent 0 xs)))).
        -- apply (gaussian_iterated_swap_head n (fun xs => F (move_coordinate_last 1 xs)) C p).
           ++ apply finite_joint_continuous_move_last, HC.
           ++ apply finite_polynomial_bound_move_last, HB.
        -- apply gaussian_iterated_expectation_ext; intros xs Hxs.
           rewrite <- move_coordinate_last_zero_step; reflexivity.
  - change (gaussian_expectation (fun x => gaussian_iterated_expectation d (fun xs => F (x::xs))) =
      gaussian_expectation (fun x => gaussian_iterated_expectation d
        (fun xs => F (x::move_coordinate_last i xs)))).
    apply (f_equal gaussian_expectation); apply functional_extensionality; intro x.
    apply (IH i (fun xs => F (x::xs)) (C*gaussian_coordinate_weight p x)).
    + lia.
    + apply finite_joint_continuous_head, HC.
    + apply finite_polynomial_bound_head, HB.
Qed.
