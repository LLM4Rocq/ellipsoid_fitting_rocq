(* Port of theories/GaussianCoordinateMove.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order,
   and its text. The only change to the file is that the import line
   "From Coquelicot Require Import Coquelicot Compactness." is dropped: no
   statement or proof here names a Coquelicot notion. The proofs are the
   original ones, word for word.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So (i < d)%nat is Peano's lt, and length, the list
   constructors and the operations on R are Stdlib's, as in the original.

   The meaning of the statements follows the ported definitions they use.
   move_coordinate_last and swap_adjacent
   (GaussianCoordinatePermutationDefinitions), finite_joint_continuous
   (GaussianCoordinateDefinitions) and finite_polynomial_bound
   (GaussianCoordinateWeightDefinitions) have their original texts and
   involve no integral, so move_coordinate_last_zero_step says exactly what
   it said. gaussian_iterated_expectation, gaussian_iterated_integrable,
   gaussian_iterated_absolutely_integrable and
   gaussian_iterated_has_expectation (GaussianProductDefinitions) now ask at
   each level for Lebesgue integrability over the line against the Gaussian
   kernel, and take Lebesgue integrals, in place of improper Riemann
   integrals (difference 4 of analysis/README.md). Under the hypotheses of
   gaussian_iterated_move_last and gaussian_iterated_move_last_integrable,
   F and its permuted version are continuous and bounded by a constant times
   a polynomial weight, so every function integrated is absolutely
   integrable against the kernel, where the Lebesgue and the improper
   Riemann values agree. The two theorems are therefore the same statements
   as before, about the same numbers. This agreement is a mathematical
   argument and is not proved in Rocq. No statement is weakened.

   The proofs use gaussian_iterated_expectation_ext (ported GaussianProduct),
   finite_joint_continuous_head and finite_joint_continuous_abs (ported
   GaussianCoordinateTopology), finite_polynomial_bound_head (ported
   GaussianCoordinateSuffixAlgebra), gaussian_iterated_swap_head (ported
   GaussianCoordinateSwap), finite_joint_continuous_move_last (ported
   GaussianPermutationContinuity), finite_polynomial_bound_move_last (ported
   GaussianPermutationWeights), and gaussian_iterated_polynomial_admissible
   and finite_polynomial_bound_abs (ported GaussianCoordinateMarginals),
   whose statements are the original texts. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions GaussianExpectation GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinateWeightDefinitions
  GaussianCoordinateWeights GaussianCoordinateMarginals GaussianCoordinatePermutationDefinitions
  GaussianCoordinatePermutations GaussianPermutationContinuity GaussianPermutationWeights
  GaussianCoordinateSuffixAlgebra GaussianCoordinateSwap.
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
