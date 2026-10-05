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
   The second identity is proved by induction on d - i: swapping two
   adjacent coordinates does not change E (GaussianCoordinateSwap), which
   brings coordinate i to the last place, where GaussianCoordinateLastStein
   applies. The mixed identity applies the first one twice. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateTopology
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights GaussianCoordinateMarginals
  GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations GaussianPermutationContinuity
  GaussianPermutationWeights GaussianCoordinatePolynomialContinuity GaussianCoordinateSwap
  GaussianCoordinateDerivativeDefinitions GaussianCoordinateDerivatives GaussianCoordinateLastStein
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
  intro Hi.
  assert (Hrel : (i+(d-i)=d)%nat) by lia.
  remember (d-i)%nat as k eqn:Hk; clear Hk Hi.
  revert i F DF DDF C D E Hrel.
  induction k as [|k IH]; intros i F DF DDF C D E Hrel HCF HCDDF HF HDF HDDF HD HDD.
  - assert (Hi : i=d) by lia; subst i.
    apply (gaussian_iterated_last_second_stein d F DF DDF C p D q E r); try assumption.
    + exact (finite_coordinate_derivative_last d F DF HD).
    + exact (finite_coordinate_derivative_last d DF DDF HDD).
  - assert (Hi : (S i < S d)%nat) by lia.
    transitivity (gaussian_iterated_expectation (S d) (fun xs => DDF (swap_adjacent i xs))).
    + exact (gaussian_iterated_swap_adjacent (S d) i DDF E r Hi HCDDF HDDF).
    + transitivity (gaussian_iterated_expectation (S d)
        (fun xs => (nth (S i) xs 0*nth (S i) xs 0-1)*F (swap_adjacent i xs))).
      * apply (IH (S i) (fun xs => F (swap_adjacent i xs))
          (fun xs => DF (swap_adjacent i xs)) (fun xs => DDF (swap_adjacent i xs)) C D E); try lia.
        -- apply finite_joint_continuous_swap_adjacent; exact HCF.
        -- apply finite_joint_continuous_swap_adjacent; exact HCDDF.
        -- apply finite_polynomial_bound_swap_adjacent; exact HF.
        -- apply finite_polynomial_bound_swap_adjacent; exact HDF.
        -- apply finite_polynomial_bound_swap_adjacent; exact HDDF.
        -- apply finite_coordinate_derivative_swap_right; assumption.
        -- apply finite_coordinate_derivative_swap_right; assumption.
      * symmetry.
        pose proof (gaussian_iterated_swap_adjacent (S d) i
          (fun xs => (nth i xs 0*nth i xs 0-1)*F xs) C (S (S p)) Hi
          (finite_joint_continuous_times_centered_square (S d) F i HCF ltac:(lia))
          (finite_polynomial_bound_times_centered_square (S d) C p F i HF ltac:(lia))) as H.
        etransitivity; [exact H|].
        apply gaussian_iterated_expectation_ext; intros xs Hxs.
        rewrite swap_adjacent_nth_left by lia; reflexivity.
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
