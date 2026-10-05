From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace OperatorDefinitions
  TensorDefinitions SecondChaosDefinitions SymmetricDefinitions GradientDefinitions
  MatrixGradient HessianDefinitions MatrixHessian MatrixThirdDefinitions
  ContinuityDefinitions MatrixThirdContinuity CoefficientDefinitions CoefficientMaps
  FiniteGibbsContinuity QuadraticDefinitions QuadraticCalculus QuadraticGrowthProofs
  GaussianMatrixComponents GoeDefinitions GoePairs GoeSynthesis JointDefinitions.
Import GRing.Theory Num.Theory.
Import ListNotations.
Import QuadraticGrowthProofs.QuadraticGrowthContinuity.
Open Scope R_scope.

(* Port of the inner module JointContinuity of theories/InterpolationProofs.v
   (also copied in theories/JointProofs.v), extracted to
   build/agent2/unbundled/JointContinuity.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original imported the bundle GoeProofs and named its inner modules
   GoePairs and GoeSynthesis through it. The port imports these standalone
   ported modules directly. It opens QuadraticGrowthProofs.QuadraticGrowthContinuity,
   as the original did.

   The seven statements keep their names, their arguments in the same order
   and their hypotheses. No item is added. Three changes of form, and none
   of meaning, come from the ported modules this one imports.

   1. Pointwise continuity. Coquelicot's continuous f x, continuity of f at
      the one point x, becomes MathComp's {for x, continuous f}
      (difference 5 of analysis/README.md), in every hypothesis and
      conclusion. The domain E of the first four lemmas, a Coquelicot
      UniformSpace in the original, is any topologicalType here, as in
      FiniteGibbsContinuity and QuadraticGrowthProofs. This generalizes the
      original.

   2. Joint vectors. In joint_matrix_continuous and
      joint_observables_continuous, Coquelicot's
        prod_NormedModule R_AbsRing (vector_NormedModule n)
          (vector_NormedModule (goe_vector_index n))
      becomes
        euclidean_product (vector_NormedModule n)
          (vector_NormedModule (goe_vector_index n))
      of MatrixEuclideanProduct, as in the ported JointDefinitions and the
      restated challenge ellipsoid_joint. Its elements are pairs, and its
      topology is the product topology (euclidean_product_nbhsE), so
      continuity at q means what it meant. The bound variable of each
      function whose continuity is stated is annotated with this type, as in
      group 4 of analysis/challenges/ellipsoid_joint/Challenge.v, so that the
      four conclusions of joint_observables_continuous have the text of the
      four continuity conjuncts of that group, each of which is paired there
      with a growth bound.

   3. The functions of the statements are built from matrix_nested_gradient,
      its derivatives, trace_pair, symmetric_divergence, chaos_contraction,
      quadratic_matrix, goe_matrix and joint_matrix, whose ports keep their
      names, arguments and values.

   In the proofs, filterdiff_continuous with a Frechet derivative becomes
   differentiable_continuous applied to the differentiability that the
   ported is_diff contains, continuous_comp becomes MathComp's
   continuous_comp, continuous_plus becomes continuousD, continuous_scal
   becomes continuousZ, continuous_const becomes cst_continuous,
   continuous_fst and continuous_snd become euclidean_product_fst_continuous
   and euclidean_product_snd_continuous, and continuous_ext becomes
   rewriting the function with funext. As QuadraticGrowthProofs explains,
   the continuity lemmas with an implicit topological domain are applied
   with ssreflect's apply: or with the domain given explicitly. *)

(* The joint vector space, named for the proofs only. *)
Local Notation joint_space n :=
  (euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n))).

Lemma joint_third_evaluation_continuous {E : topologicalType} n
  (T : E -> third_array n) (U V W : E -> matrix n) x :
  {for x, continuous T} -> {for x, continuous U} -> {for x, continuous V} ->
  {for x, continuous W} ->
  {for x, continuous (fun z => third_evaluation n (T z) (U z) (V z) (W z))}.
Proof.
  intros HT HU HV HW; unfold third_evaluation, hessian_evaluation.
  apply: growth_trace_pair_continuous; [|exact HU].
  apply: growth_hessian_action_continuous; [|exact HV].
  apply: growth_third_action_continuous; assumption.
Qed.

Lemma joint_gradient_continuous_base {E : topologicalType}
  n beta gamma offset coeff Y S (A : E -> matrix n) x :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> {for x, continuous A} ->
  {for x, continuous (fun z => matrix_nested_gradient n beta gamma offset coeff Y S (A z))}.
Proof.
  intros Hb Hg HY HS HA.
  apply (@continuous_comp E (matrix n) (matrix n) A
    (matrix_nested_gradient n beta gamma offset coeff Y S) x); [exact HA|].
  have [HD _] := matrix_nested_gradient_frechet n beta gamma offset coeff Y S Hb Hg HY HS (A x).
  exact (differentiable_continuous HD).
Qed.

Lemma joint_divergence_continuous_base {E : topologicalType}
  n beta gamma offset coeff Y S (A : E -> matrix n) x :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> {for x, continuous A} ->
  {for x, continuous (fun z => symmetric_divergence n
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S (A z)))}.
Proof.
  intros Hb Hg HY HS HA.
  (* Coquelicot's continuous_ext: the map is rewritten with goe_basis_divergence. *)
  have -> : (fun z => symmetric_divergence n
      (matrix_nested_gradient_derivative n beta gamma offset coeff Y S (A z))) =
    (fun z => coordinate_sum (goe_vector_index n) (fun k =>
      trace_pair n (goe_basis n k)
        (matrix_nested_gradient_derivative n beta gamma offset coeff Y S (A z) (goe_basis n k)))).
  { apply: funext => z; symmetry; apply goe_basis_divergence. }
  apply: growth_coordinate_sum_continuous; intros k Hk.
  apply: growth_trace_pair_continuous; [apply: cst_continuous|].
  apply (@continuous_comp E (matrix n) (matrix n) A
    (fun M => matrix_nested_gradient_derivative n beta gamma offset coeff Y S M (goe_basis n k)) x);
    [exact HA|].
  have [HD _] := matrix_nested_gradient_second_frechet n beta gamma offset coeff Y S
    (A x) (goe_basis n k) Hb Hg HY HS.
  exact (differentiable_continuous HD).
Qed.

Lemma joint_remainder_continuous_base {E : topologicalType}
  n beta gamma offset coeff Y S (A : E -> matrix n) (X : E -> vector n) x :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> {for x, continuous A} ->
  {for x, continuous X} ->
  {for x, continuous (fun z => chaos_contraction n
    (matrix_nested_third_derivative n beta gamma offset coeff Y S (A z)) (X z))}.
Proof.
  intros Hb Hg HY HS HA HX; unfold chaos_contraction.
  apply: continuous_Rmult_fct; [apply: cst_continuous|].
  apply: growth_coordinate_sum_continuous; intros a Ha.
  apply: growth_coordinate_sum_continuous; intros b Hbb.
  (* Coquelicot's continuous_ext: the map is rewritten with actual_third_evaluation. *)
  have -> : (fun z => matrix_nested_third_derivative n beta gamma offset coeff Y S (A z)
      (chaos_first n (X z) a) (chaos_first n (X z) b) (chaos_second n a b)) =
    (fun z => third_evaluation n
      (matrix_nested_third_coefficients n beta gamma offset coeff Y S (A z))
      (chaos_first n (X z) a) (chaos_first n (X z) b) (chaos_second n a b)).
  { apply: funext => z; symmetry; apply actual_third_evaluation; assumption. }
  apply: joint_third_evaluation_continuous.
  - apply (@continuous_comp E (matrix n) (third_array n) A
      (matrix_nested_third_coefficients n beta gamma offset coeff Y S) x); [exact HA|].
    apply matrix_third_coefficients_continuous; assumption.
  - apply (@continuous_comp E (vector n) (matrix n) X (fun v => chaos_first n v a) x);
      [exact HX|].
    apply matrix_component_chaos_first_continuous.
  - apply (@continuous_comp E (vector n) (matrix n) X (fun v => chaos_first n v b) x);
      [exact HX|].
    apply matrix_component_chaos_first_continuous.
  - apply: cst_continuous.
Qed.

Lemma joint_matrix_continuous n C t
  (q : euclidean_product (vector_NormedModule n)
     (vector_NormedModule (goe_vector_index n))) :
  {for q, continuous (fun z : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) =>
    joint_matrix n C t (fst z) (snd z))}.
Proof.
  unfold joint_matrix, matrix_add, matrix_scale.
  have H1 : {for q, continuous (fun z : joint_space n =>
      quadratic_matrix n (sqrt (t / INR (S n))) C (fst z))}.
  { apply (@continuous_comp (joint_space n) (vector n) (matrix n)
      (fun z : joint_space n => fst z) (quadratic_matrix n (sqrt (t / INR (S n))) C) q).
    - exact (@euclidean_product_fst_continuous (vector_NormedModule n)
        (vector_NormedModule (goe_vector_index n)) q).
    - have [HD _] := quadratic_matrix_frechet n (sqrt (t / INR (S n))) C (fst q).
      exact (differentiable_continuous HD). }
  have H2 : {for q, continuous (fun z : joint_space n => goe_matrix n (snd z))}.
  { apply (@continuous_comp (joint_space n) (vector (goe_vector_index n)) (matrix n)
      (fun z : joint_space n => snd z) (goe_matrix n) q).
    - exact (@euclidean_product_snd_continuous (vector_NormedModule n)
        (vector_NormedModule (goe_vector_index n)) q).
    - exact (@growth_linear_continuous (vector_NormedModule (goe_vector_index n))
        (matrix_NormedModule n) (goe_matrix n) (snd q) (goe_matrix_linear n)). }
  have H3 : {for q, continuous (fun z : joint_space n =>
      (sqrt (1 - t) *: goe_matrix n (snd z) : matrix_NormedModule n)%R)}.
  { exact (@continuousZ R (matrix_NormedModule n) (joint_space n)
      (fun _ => sqrt (1 - t)) (fun z : joint_space n => goe_matrix n (snd z)) q
      (@cst_continuous _ _ (sqrt (1 - t)) q) H2). }
  exact (@continuousD R (matrix_NormedModule n) (joint_space n) _ _ q H1 H3).
Qed.

Lemma joint_quadratic_input_continuous n (x : vector n) :
  {for x, continuous (joint_quadratic_input n)}.
Proof.
  unfold joint_quadratic_input.
  have [HD _] := quadratic_matrix_frechet n (/ sqrt (INR (S n))) (matrix_zero n) x.
  exact (differentiable_continuous HD).
Qed.

Theorem joint_observables_continuous n beta gamma offset coeff Y S C t :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  forall q : euclidean_product (vector_NormedModule n)
    (vector_NormedModule (goe_vector_index n)),
  {for q, continuous (fun z : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) =>
    joint_quadratic_trace n beta gamma offset coeff Y S C t (fst z) (snd z))} /\
  {for q, continuous (fun z : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) =>
    joint_goe_trace n beta gamma offset coeff Y S C t (fst z) (snd z))} /\
  {for q, continuous (fun z : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) =>
    joint_divergence n beta gamma offset coeff Y S C t (fst z) (snd z))} /\
  {for q, continuous (fun z : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) =>
    joint_remainder n beta gamma offset coeff Y S C t (fst z) (snd z))}.
Proof.
  intros Hb Hg HY HS q.
  assert (HA : {for q, continuous (fun z : joint_space n => joint_matrix n C t (fst z) (snd z))})
    by apply joint_matrix_continuous.
  assert (HG : {for q, continuous (fun z : joint_space n =>
    matrix_nested_gradient n beta gamma offset coeff Y S
      (joint_matrix n C t (fst z) (snd z)))}).
  { apply: joint_gradient_continuous_base; assumption. }
  assert (Hfst : {for q, continuous (fun z : joint_space n => fst z)}).
  { exact (@euclidean_product_fst_continuous (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) q). }
  assert (Hsnd : {for q, continuous (fun z : joint_space n => snd z)}).
  { exact (@euclidean_product_snd_continuous (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) q). }
  split.
  - unfold joint_quadratic_trace; apply: growth_trace_pair_continuous; [|exact HG].
    apply (@continuous_comp (joint_space n) (vector n) (matrix n)
      (fun z : joint_space n => fst z) (joint_quadratic_input n) q);
      [exact Hfst|apply joint_quadratic_input_continuous].
  - split.
    + unfold joint_goe_trace; apply: growth_trace_pair_continuous; [|exact HG].
      apply (@continuous_comp (joint_space n) (vector (goe_vector_index n)) (matrix n)
        (fun z : joint_space n => snd z) (goe_matrix n) q); [exact Hsnd|].
      exact (@growth_linear_continuous (vector_NormedModule (goe_vector_index n))
        (matrix_NormedModule n) (goe_matrix n) (snd q) (goe_matrix_linear n)).
    + split.
      * unfold joint_divergence; apply: joint_divergence_continuous_base; assumption.
      * unfold joint_remainder; apply: joint_remainder_continuous_base; assumption.
Qed.
