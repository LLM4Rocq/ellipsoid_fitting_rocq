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
  JointTimeCalculus JointValueGrowth JointLipschitz.
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

Theorem joint_soft_value_pair_domain n beta gamma offset coeff Y S C t :
  0<beta -> 0<gamma -> Y<>nil -> S<>nil -> 0<=t<=1 ->
  gaussian_pair_domain n (goe_vector_index n)
    (joint_soft_value n beta gamma offset coeff Y S C t).
Proof.
  intros Hb Hg HY HS Ht.
  destruct (joint_soft_value_polynomial_regular n beta gamma offset coeff Y S C Hb Hg HY HS)
    as [K [HK Hregular]].
  exact (proj1 (gaussian_pair_polynomial_exchange n (goe_vector_index n)
    (joint_soft_value n beta gamma offset coeff Y S C t) K 2
    (proj1 (Hregular t)) HK (proj2 (Hregular t) Ht))).
Qed.

Theorem joint_soft_value_expectation_continuous n beta gamma offset coeff Y S C a :
  0<beta -> 0<gamma -> Y<>nil -> S<>nil -> 0<=a<=1 ->
  ((fun t => gaussian_pair_expectation n (goe_vector_index n)
      (joint_soft_value n beta gamma offset coeff Y S C t)) @
    within (fun t => 0<=t<=1) (nbhs a) -->
    gaussian_pair_expectation n (goe_vector_index n)
      (joint_soft_value n beta gamma offset coeff Y S C a))%classic.
Proof.
  intros Hb Hg HY HS Ha.
  destruct (joint_soft_value_polynomial_regular n beta gamma offset coeff Y S C Hb Hg HY HS)
    as [K [HK Hregular]].
  destruct (joint_soft_value_difference_bound n beta gamma offset coeff Y S Hb Hg HY HS)
    as [L [HL Hdifference]].
  unfold gaussian_pair_expectation.
  refine (proj1 (gaussian_iterated_expectation_continuous_modulus_within
    (Datatypes.S n+Datatypes.S(goe_vector_index n))%coq_nat
    (fun t => gaussian_pair_pullback n (goe_vector_index n)
      (joint_soft_value n beta gamma offset coeff Y S C t))
    (fun t => 0<=t<=1) a K 2 2
    (fun t => L*(Rabs(sqrt t-sqrt a)+Rabs(sqrt(1-t)-sqrt(1-a))))
    Ha _ _ _ _ _)).
  - apply joint_polynomial_pullback; [exact HK|exact (proj2 (Hregular a) Ha)].
  - exists 1; split; [lra|].
    intros b Hb' Hnear; apply joint_continuous_pullback; exact (proj1 (Hregular b)).
  - apply joint_endpoint_modulus_continuous.
  - cbv beta.
    replace (sqrt a-sqrt a) with 0 by ring.
    replace (sqrt(1-a)-sqrt(1-a)) with 0 by ring.
    rewrite Rabs_R0. lra.
  - exists 1; split; [lra|].
    intros b Hb' Hnear.
    change (finite_polynomial_bound (Datatypes.S n+Datatypes.S(goe_vector_index n))%coq_nat
      (L*(Rabs(sqrt b-sqrt a)+Rabs(sqrt(1-b)-sqrt(1-a)))) 2
      (gaussian_pair_pullback n (goe_vector_index n) (fun x z =>
        joint_soft_value n beta gamma offset coeff Y S C b x z-
        joint_soft_value n beta gamma offset coeff Y S C a x z))).
    apply joint_polynomial_pullback.
    + pose proof (Rabs_pos (sqrt b-sqrt a));
        pose proof (Rabs_pos (sqrt(1-b)-sqrt(1-a))); nra.
    + intro q; exact (Hdifference C a b q Ha Hb').
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

Theorem joint_soft_value_zero_endpoint n beta gamma offset coeff Y S C :
  0<beta -> 0<gamma -> Y<>nil -> S<>nil ->
  gaussian_vector_domain (goe_vector_index n) (fun z =>
    soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_add n C (goe_matrix n z))) Y S) /\
  gaussian_pair_expectation n (goe_vector_index n)
    (joint_soft_value n beta gamma offset coeff Y S C 0) =
  gaussian_vector_expectation (goe_vector_index n) (fun z =>
    soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_add n C (goe_matrix n z))) Y S).
Proof.
  intros Hb Hg HY HS.
  destruct (joint_soft_value_polynomial_regular n beta gamma offset coeff Y S C Hb Hg HY HS)
    as [K [HK Hregular]].
  destruct (gaussian_pair_polynomial_exchange n (goe_vector_index n)
    (joint_soft_value n beta gamma offset coeff Y S C 0) K 2
    (proj1 (Hregular 0)) HK (proj2 (Hregular 0) ltac:(lra)))
    as [Hpair [Hz [Hx [Houterx [Houterz [Hforward Hreverse]]]]]].
  split.
  - eapply gaussian_vector_domain_ext; [|exact (Hz (0%R : vector_NormedModule n))].
    intro z; unfold joint_soft_value; rewrite joint_matrix_at_zero; reflexivity.
  - rewrite Hreverse.
    apply gaussian_vector_expectation_ext; intro z.
    replace (joint_soft_value n beta gamma offset coeff Y S C 0)
      with (fun (_ : vector n) (z : vector (goe_vector_index n)) => soft_minimax beta gamma
        (matrix_affine_scores n offset coeff (matrix_add n C (goe_matrix n z))) Y S).
    + apply (proj2 (gaussian_vector_constant n _)).
    + apply functional_extensionality; intro x; apply functional_extensionality; intro w.
      unfold joint_soft_value; rewrite joint_matrix_at_zero; reflexivity.
Qed.

Theorem joint_soft_value_one_endpoint n beta gamma offset coeff Y S C :
  0<beta -> 0<gamma -> Y<>nil -> S<>nil ->
  gaussian_vector_domain n (fun x =>
    soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_add n C (joint_quadratic_input n x))) Y S) /\
  gaussian_pair_expectation n (goe_vector_index n)
    (joint_soft_value n beta gamma offset coeff Y S C 1) =
  gaussian_vector_expectation n (fun x =>
    soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_add n C (joint_quadratic_input n x))) Y S).
Proof.
  intros Hb Hg HY HS.
  destruct (joint_soft_value_polynomial_regular n beta gamma offset coeff Y S C Hb Hg HY HS)
    as [K [HK Hregular]].
  destruct (gaussian_pair_polynomial_exchange n (goe_vector_index n)
    (joint_soft_value n beta gamma offset coeff Y S C 1) K 2
    (proj1 (Hregular 1)) HK (proj2 (Hregular 1) ltac:(lra)))
    as [Hpair [Hz [Hx [Houterx [Houterz [Hforward Hreverse]]]]]].
  split.
  - eapply gaussian_vector_domain_ext;
      [|exact (Hx (0%R : vector_NormedModule (goe_vector_index n)))].
    intro x; unfold joint_soft_value; rewrite joint_matrix_at_one; reflexivity.
  - rewrite Hforward.
    apply gaussian_vector_expectation_ext; intro x.
    replace (joint_soft_value n beta gamma offset coeff Y S C 1 x)
      with (fun (_ : vector (goe_vector_index n)) => soft_minimax beta gamma
        (matrix_affine_scores n offset coeff (matrix_add n C (joint_quadratic_input n x))) Y S).
    + apply (proj2 (gaussian_vector_constant (goe_vector_index n) _)).
    + apply functional_extensionality; intro z.
      unfold joint_soft_value; rewrite joint_matrix_at_one; reflexivity.
Qed.

Theorem joint_soft_value_endpoint_limits n beta gamma offset coeff Y S C :
  0<beta -> 0<gamma -> Y<>nil -> S<>nil ->
  gaussian_vector_domain (goe_vector_index n) (fun z =>
    soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_add n C (goe_matrix n z))) Y S) /\
  gaussian_vector_domain n (fun x =>
    soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_add n C (joint_quadratic_input n x))) Y S) /\
  ((fun t => gaussian_pair_expectation n (goe_vector_index n)
      (joint_soft_value n beta gamma offset coeff Y S C t)) @
    within (fun t => 0<=t<=1) (nbhs 0) -->
    gaussian_vector_expectation (goe_vector_index n) (fun z =>
      soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_add n C (goe_matrix n z))) Y S))%classic /\
  ((fun t => gaussian_pair_expectation n (goe_vector_index n)
      (joint_soft_value n beta gamma offset coeff Y S C t)) @
    within (fun t => 0<=t<=1) (nbhs 1) -->
    gaussian_vector_expectation n (fun x =>
      soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_add n C (joint_quadratic_input n x))) Y S))%classic.
Proof.
  intros Hb Hg HY HS.
  destruct (joint_soft_value_zero_endpoint n beta gamma offset coeff Y S C Hb Hg HY HS) as [HD0 HE0].
  destruct (joint_soft_value_one_endpoint n beta gamma offset coeff Y S C Hb Hg HY HS) as [HD1 HE1].
  split; [exact HD0|]; split; [exact HD1|]; split.
  - rewrite <- HE0; apply joint_soft_value_expectation_continuous; try assumption; lra.
  - rewrite <- HE1; apply joint_soft_value_expectation_continuous; try assumption; lra.
Qed.
