(* Port of the inner module JointEndpointContinuity of
   theories/InterpolationProofs.v, extracted to
   build/agent2/unbundled/JointEndpointContinuity.v, from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order
   and its hypotheses. The arithmetic in every statement is Stdlib's, as in
   the original.

   Statements that change form, without a change of meaning.

   1. Coquelicot's pointwise continuity continuous f a, for f : R -> R,
      becomes MathComp's {for a, continuous f} (difference 5 of
      analysis/README.md), in joint_endpoint_modulus_continuous. Both say
      that f t tends to f a when t tends to a, for the usual topology of R.
      The lemma still holds at every real a and for every K: Stdlib's sqrt
      is continuous on the whole line (it is 0 on the negative reals), as
      Coquelicot's continuous_sqrt said.

   2. Coquelicot's limit within a domain,
        filterlim f (within D (locally a)) (locally l),
      becomes MathComp's
        (f @ within D (nbhs a) --> l)%classic,
      in joint_soft_value_expectation_continuous and in the last two
      conjuncts of joint_soft_value_endpoint_limits, with
      D = fun t => 0<=t<=1. MathComp's within D F is the set of P with
      F (fun x => D x -> P x), which is the text of Coquelicot's within, and
      nbhs a on R is the filter of the balls around a, as Coquelicot's
      locally a. So both say: for every eps > 0 there is delta > 0 with
      Rabs (f t - l) < eps for every t in [0, 1] with Rabs (t - a) < delta.
      These are the texts of clauses 5.3 and 6.3 of
      analysis/challenges/ellipsoid_interpolation_time/Challenge.v.

   joint_soft_value_pair_domain, joint_matrix_at_zero, joint_matrix_at_one,
   joint_soft_value_zero_endpoint and joint_soft_value_one_endpoint keep
   their texts. The Gaussian notions (gaussian_pair_domain,
   gaussian_pair_expectation, gaussian_vector_domain,
   gaussian_vector_expectation) come from the ported definition modules,
   whose texts are the original ones; their meaning follows difference 4 of
   analysis/README.md (Borel measurability and Lebesgue integrability over
   the line at each level of the iteration, in place of improper Riemann
   integrals). Every function whose domain or expectation is asserted here
   is continuous and bounded by a polynomial on the joint vector space, and
   for such functions both readings hold and the values agree.

   Imports. The bundle imported GoeProofs, GaussianCoordinateProofs and
   GaussianVectorProofs, and named the inner modules GaussianProduct,
   GaussianCoordinateMarginals, GaussianVectorDomain and
   GaussianVectorAlgebra through them. This port imports those four ported
   standalone modules directly, in the same order. No name of an inner
   module of GoeProofs is used, so nothing replaces that import. The
   Coquelicot import is dropped, and AnalysisBridge2 gives the MathComp
   notations and the continuity combinators. The Stdlib degree
   Datatypes.S n + Datatypes.S (goe_vector_index n) of the original is
   written with %coq_nat, so that it is Stdlib's Nat.add as in the ported
   JointDefinitions.

   Proofs. The continuity of the modulus uses the continuity combinators of
   AnalysisBridge and MathComp's sqrt_continuous, in place of Coquelicot's
   continuous_mult, continuous_plus, continuous_minus, continuous_Rabs_comp
   and continuous_sqrt. Coquelicot's zero of vector_NormedModule becomes
   MathComp's 0%R. Stdlib's "rewrite A, B" and "rewrite A by tac", which do
   not parse once ssreflect is loaded, are replaced by rewrites with
   explicit arguments. The rest is the original proof. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorDefinitions
  SoftDefinitions MatrixGibbsDefinitions GoeDefinitions GaussianProductDefinitions
  GaussianVectorDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions JointDefinitions JointCoordinates
  GaussianPairExchange GaussianExpectationContinuity TimeDefinitions
  JointTimeCalculus JointLipschitz.
From EllipsoidFitting Require Import GaussianProduct GaussianCoordinateMarginals
  GaussianVectorDomain GaussianVectorAlgebra.
Import ListNotations.
Open Scope R_scope.

Lemma joint_endpoint_modulus_continuous K a :
  {for a, continuous (fun t => K*(Rabs(sqrt t-sqrt a)+Rabs(sqrt(1-t)-sqrt(1-a))))}.
Proof.
  have Hsqrt : continuous sqrt.
  { move=> x; rewrite (funext RsqrtE); exact: sqrt_continuous. }
  apply continuous_mult; [apply continuous_const|].
  apply continuous_plus.
  - apply: (continuous_comp (f := fun t => sqrt t - sqrt a)); [|exact: continuous_Rabs].
    apply continuous_minus; [exact: Hsqrt|apply continuous_const].
  - apply: (continuous_comp (f := fun t => sqrt (1-t) - sqrt (1-a))); [|exact: continuous_Rabs].
    apply continuous_minus; [|apply continuous_const].
    apply: (continuous_comp (f := fun t => 1-t)); [|exact: Hsqrt].
    apply continuous_minus; [apply continuous_const|apply continuous_id].
Qed.

Lemma joint_matrix_at_zero n C x z :
  joint_matrix n C 0 x z=matrix_add n C (goe_matrix n z).
Proof.
  rewrite (joint_matrix_normalized_path n C 0 x z (Rle_refl 0)).
  replace (1-0) with 1 by ring; rewrite sqrt_0 sqrt_1.
  apply matrix_ext; intros i j Hi Hj.
  rewrite !matrix_entry_add !matrix_entry_scale; ring.
Qed.

Lemma joint_matrix_at_one n C x z :
  joint_matrix n C 1 x z=matrix_add n C (joint_quadratic_input n x).
Proof.
  rewrite (joint_matrix_normalized_path n C 1 x z Rle_0_1).
  replace (1-1) with 0 by ring; rewrite sqrt_0 sqrt_1.
  apply matrix_ext; intros i j Hi Hj.
  rewrite !matrix_entry_add !matrix_entry_scale; ring.
Qed.
