(* Port of theories/GaussianCoordinateSwap.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order,
   and its text. The changes to the file are these.
   - The import line "From Coquelicot Require Import Coquelicot
     Compactness." is dropped, and AnalysisBridge is loaded with Require
     only, not imported. No MathComp notation is opened here, so the
     statements are parsed as in the original: (S i < d)%nat is Peano's lt,
     and ++, length and the operations on R are Stdlib's.
   - In the proof of gaussian_iterated_swap_head, the ported
     gaussian_fubini_separable asks for MathComp's pointwise continuity
     {for x, continuous g} of the scaled weight (difference 5 of
     analysis/README.md), and gaussian_coordinate_weight_continuous now
     gives that form for the weight. Coquelicot's proof used
     (@continuous_mult R_UniformSpace R_AbsRing) and continuous_const. The
     port goes through Stdlib's continuity_pt with
     AnalysisBridge.continuity_pt_filterlim (continuity_pt f x is
     equivalent to {for x, continuous f}), and uses Stdlib's
     continuity_pt_mult and continuity_pt_const. This keeps MathComp's
     notations out of the file. Without the MathComp imports, R is not
     inferred as a topologicalType, so the bridge's continuous_mult cannot
     be applied to R directly.
   Every other line of the proofs is the original one.

   The meaning of the statements follows the ported definitions they use.
   finite_joint_continuous (GaussianCoordinateDefinitions),
   finite_polynomial_bound (GaussianCoordinateWeightDefinitions) and
   swap_adjacent (GaussianCoordinatePermutationDefinitions) have their
   original texts and involve no integral. gaussian_iterated_expectation,
   gaussian_iterated_integrable, gaussian_iterated_absolutely_integrable
   and gaussian_iterated_has_expectation (GaussianProductDefinitions) now
   ask at each level for Lebesgue integrability over the line against the
   Gaussian kernel, and take Lebesgue integrals, in place of improper
   Riemann integrals (difference 4 of analysis/README.md). Under the
   hypotheses of these theorems every integrand is continuous and bounded by
   a constant times a polynomial weight, so it is absolutely integrable
   against the kernel, and the Lebesgue and improper Riemann values agree on
   it. No statement is weakened. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require AnalysisBridge.
From EllipsoidFitting Require Import GaussianDefinitions GaussianExpectation GaussianProductDefinitions GaussianProduct
  GaussianFubini GaussianLastDefinitions GaussianLastIntegration GaussianCoordinateDefinitions
  GaussianCoordinateTopology GaussianCoordinateBivariate GaussianCoordinateWeightDefinitions
  GaussianCoordinateWeights GaussianCoordinateMarginals GaussianCoordinatePermutationDefinitions
  GaussianCoordinatePermutations GaussianPermutationContinuity GaussianPermutationWeights
  GaussianCoordinateSuffixAlgebra GaussianCoordinateSuffix.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_iterated_swap_head n F C p :
  finite_joint_continuous (S (S n)) F ->
  finite_polynomial_bound (S (S n)) C p F ->
  gaussian_iterated_expectation (S (S n)) F =
    gaussian_iterated_expectation (S (S n)) (fun xs => F (swap_adjacent 0 xs)).
Proof.
  intros HC HB.
  destruct (gaussian_suffix_marginal_regular 2 n F C p HC HB) as [HH [HK Hb]].
  change (gaussian_iterated_expectation (2+n) F =
    gaussian_iterated_expectation (2+n) (fun xs => F (swap_adjacent 0 xs))).
  rewrite !gaussian_iterated_suffix_expectation.
  change (gaussian_expectation (fun x => gaussian_expectation
    (fun y => gaussian_suffix_marginal n F [x;y])) =
    gaussian_expectation (fun x => gaussian_expectation
    (fun y => gaussian_suffix_marginal n (fun xs => F (swap_adjacent 0 xs)) [x;y]))).
  transitivity (gaussian_expectation (fun y => gaussian_expectation
    (fun x => gaussian_suffix_marginal n F [x;y]))).
  - apply (gaussian_fubini_separable (fun x y => gaussian_suffix_marginal n F [x;y])
      (fun x => (C*gaussian_coordinate_weight_moment p^n)*gaussian_coordinate_weight p x)
      (gaussian_coordinate_weight p)).
    + apply finite_joint_continuous_two_section, HH.
    + intro x; apply AnalysisBridge.continuity_pt_filterlim.
      apply continuity_pt_mult.
      * apply continuity_pt_const; intros u v; reflexivity.
      * apply AnalysisBridge.continuity_pt_filterlim.
        apply gaussian_coordinate_weight_continuous.
    + apply gaussian_coordinate_weight_continuous.
    + intro x; pose proof (gaussian_coordinate_weight_nonnegative p x); nra.
    + apply gaussian_coordinate_weight_nonnegative.
    + apply gaussian_integral_exists_scale; exact (proj1 (gaussian_coordinate_weight_integrable p)).
    + exact (proj1 (gaussian_coordinate_weight_integrable p)).
    + intros x y; specialize (Hb [x;y] eq_refl).
      simpl gaussian_coordinate_product_weight in Hb.
      rewrite Rmult_1_r in Hb; rewrite Rmult_assoc; exact Hb.
  - apply (f_equal gaussian_expectation); apply functional_extensionality; intro x.
    apply (f_equal gaussian_expectation); apply functional_extensionality; intro y.
    symmetry; apply gaussian_suffix_marginal_swap_head.
Qed.

Theorem gaussian_iterated_swap_adjacent d i F C p :
  (S i < d)%nat -> finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_expectation d F =
    gaussian_iterated_expectation d (fun xs => F (swap_adjacent i xs)).
Proof.
  revert i F C; induction d as [|d IH]; intros i F C Hi HC HB; [lia|].
  destruct i as [|i].
  - destruct d as [|n]; [lia|]. apply (gaussian_iterated_swap_head n F C p); assumption.
  - change (gaussian_expectation (fun x => gaussian_iterated_expectation d (fun xs => F (x::xs))) =
      gaussian_expectation (fun x => gaussian_iterated_expectation d
        (fun xs => F (x::swap_adjacent i xs)))).
    apply (f_equal gaussian_expectation); apply functional_extensionality; intro x.
    apply (IH i (fun xs => F (x::xs)) (C*gaussian_coordinate_weight p x)).
    + lia.
    + apply finite_joint_continuous_head, HC.
    + apply finite_polynomial_bound_head, HB.
Qed.

Theorem gaussian_iterated_swap_adjacent_integrable d i F C p :
  (S i < d)%nat -> finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_integrable d F /\ gaussian_iterated_absolutely_integrable d F /\
  gaussian_iterated_has_expectation d F (gaussian_iterated_expectation d F) /\
  gaussian_iterated_has_expectation d (fun xs => Rabs (F xs))
    (gaussian_iterated_expectation d (fun xs => Rabs (F xs))) /\
  gaussian_iterated_integrable d (fun xs => F (swap_adjacent i xs)) /\
  gaussian_iterated_absolutely_integrable d (fun xs => F (swap_adjacent i xs)) /\
  gaussian_iterated_has_expectation d (fun xs => F (swap_adjacent i xs))
    (gaussian_iterated_expectation d F) /\
  gaussian_iterated_has_expectation d (fun xs => Rabs (F (swap_adjacent i xs)))
    (gaussian_iterated_expectation d (fun xs => Rabs (F xs))) /\
  gaussian_iterated_expectation d F =
    gaussian_iterated_expectation d (fun xs => F (swap_adjacent i xs)) /\
  gaussian_iterated_expectation d (fun xs => Rabs (F xs)) =
    gaussian_iterated_expectation d (fun xs => Rabs (F (swap_adjacent i xs))).
Proof.
  intros Hi HC HB.
  destruct (gaussian_iterated_polynomial_admissible d F C p HC HB)
    as [HI [HA [HV [HAV HBV]]]].
  pose proof (finite_joint_continuous_swap_adjacent d i F HC) as HCs.
  pose proof (finite_polynomial_bound_swap_adjacent d C p F i HB) as HBs.
  destruct (gaussian_iterated_polynomial_admissible d _ C p HCs HBs)
    as [HIs [HAs [HVs [HAVs HBVs]]]].
  pose proof (gaussian_iterated_swap_adjacent d i F C p Hi HC HB) as HE.
  pose proof (gaussian_iterated_swap_adjacent d i (fun xs => Rabs (F xs)) C p Hi
    (finite_joint_continuous_abs d F HC) (finite_polynomial_bound_abs d C p F HB)) as HEA.
  rewrite <- HE in HVs; rewrite <- HEA in HAVs.
  repeat split; assumption.
Qed.
