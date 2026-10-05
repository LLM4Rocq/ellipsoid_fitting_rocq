(* Port of theories/GaussianCoordinateStein.v from Coquelicot to
   MathComp-Analysis.

   Every theorem keeps its name, its arguments in the same order, and its
   text. The only change to the file is that the import line
   "From Coquelicot Require Import Coquelicot." is dropped: no statement or
   proof here names a Coquelicot notion. The proofs are the original ones,
   word for word.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So (i <= d)%nat and (S i < S d)%nat are Peano's le and
   lt, nth is Stdlib's List.nth, and length and the operations on R are
   Stdlib's, as in the original. The ported lemmas that the proofs apply
   write (i < d)%coq_nat and List.nth, which elaborate to the same terms.

   The meaning of the statements follows the ported definitions they use.
   finite_joint_continuous (GaussianCoordinateDefinitions) and
   finite_polynomial_bound (GaussianCoordinateWeightDefinitions) have their
   original texts and involve no integral. finite_coordinate_derivative
   (GaussianCoordinateDerivativeDefinitions) now says that each coordinate
   section has MathComp's derivative @is_derive R R^o R^o t 1 in place of
   Coquelicot's is_derive; both are the ordinary derivative of a function
   R -> R (AnalysisBridge.is_derive_Reals), so the hypothesis means what it
   meant. gaussian_iterated_expectation (GaussianProductDefinitions) now
   takes at each level the Lebesgue integral over the line against the
   Gaussian kernel, in place of the improper Riemann integral (difference 4
   of analysis/README.md). Under the hypotheses of the three theorems, every
   function integrated (DF, DDF, DFiDFj, and F multiplied by a coordinate,
   by a product of two coordinates or by a centered square) is continuous
   and bounded by a constant times a polynomial weight, so it is absolutely
   integrable against the kernel, where the Lebesgue and the improper
   Riemann values agree. The three identities are therefore the same
   statements as before, about the same numbers. This agreement is a
   mathematical argument and is not proved in Rocq. No statement is
   weakened.

   The proofs use gaussian_iterated_last_first_stein and
   gaussian_iterated_last_second_stein (ported GaussianCoordinateLastStein),
   gaussian_iterated_swap_adjacent (ported GaussianCoordinateSwap),
   finite_coordinate_derivative_last, finite_coordinate_derivative_swap_right
   and finite_coordinate_derivative_times_other (ported
   GaussianCoordinateDerivatives), finite_joint_continuous_swap_adjacent
   (ported GaussianPermutationContinuity),
   finite_polynomial_bound_swap_adjacent (ported GaussianPermutationWeights),
   finite_joint_continuous_times_coordinate and
   finite_joint_continuous_times_centered_square (ported
   GaussianCoordinatePolynomialContinuity),
   finite_polynomial_bound_times_coordinate and
   finite_polynomial_bound_times_centered_square (ported
   GaussianCoordinateWeights), swap_adjacent_nth_left
   (GaussianCoordinatePermutations, copied unchanged) and
   gaussian_iterated_expectation_ext (ported GaussianProduct). Their
   statements are the original texts, up to the %coq_nat, List.nth and
   derivative notations described above. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateTopology
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights GaussianCoordinateMarginals
  GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations GaussianPermutationContinuity
  GaussianPermutationWeights GaussianCoordinatePolynomialContinuity GaussianCoordinateSwap
  GaussianCoordinateDerivativeDefinitions GaussianCoordinateDerivatives GaussianCoordinateLastStein.
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
  intro Hi.
  assert (Hrel : (i+(d-i)=d)%nat) by lia.
  remember (d-i)%nat as k eqn:Hk; clear Hk Hi.
  revert i F DF C D Hrel.
  induction k as [|k IH]; intros i F DF C D Hrel HCF HCDF HF HDF HD.
  - assert (Hi : i=d) by lia; subst i.
    apply (gaussian_iterated_last_first_stein d F DF C p D q); try assumption.
    exact (finite_coordinate_derivative_last d F DF HD).
  - assert (Hi : (S i < S d)%nat) by lia.
    transitivity (gaussian_iterated_expectation (S d) (fun xs => DF (swap_adjacent i xs))).
    + exact (gaussian_iterated_swap_adjacent (S d) i DF D q Hi HCDF HDF).
    + transitivity (gaussian_iterated_expectation (S d)
        (fun xs => nth (S i) xs 0 * F (swap_adjacent i xs))).
      * apply (IH (S i) (fun xs => F (swap_adjacent i xs))
          (fun xs => DF (swap_adjacent i xs)) C D); try lia.
        -- apply finite_joint_continuous_swap_adjacent; exact HCF.
        -- apply finite_joint_continuous_swap_adjacent; exact HCDF.
        -- apply finite_polynomial_bound_swap_adjacent; exact HF.
        -- apply finite_polynomial_bound_swap_adjacent; exact HDF.
        -- apply finite_coordinate_derivative_swap_right; assumption.
      * symmetry.
        pose proof (gaussian_iterated_swap_adjacent (S d) i
          (fun xs => nth i xs 0 * F xs) C (S p) Hi
          (finite_joint_continuous_times_coordinate (S d) F i HCF ltac:(lia))
          (finite_polynomial_bound_times_coordinate (S d) C p F i HF ltac:(lia))) as H.
        etransitivity; [exact H|].
        apply gaussian_iterated_expectation_ext; intros xs Hxs.
        rewrite swap_adjacent_nth_left by lia; reflexivity.
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
