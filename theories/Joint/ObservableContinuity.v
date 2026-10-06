From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.Trace Matrix.OperatorDefinitions
  Tensor.Definitions Chaos.SecondOrderDefinitions
  Matrix.SymmetricBasisDefinitions Gibbs.NestedGradientDefinitions
  Gibbs.MatrixNestedGradient Gibbs.HessianDefinitions Gibbs.NestedHessian
  Gibbs.MatrixThirdDerivativeDefinitions Matrix.ThirdOrderArrays
  Gibbs.MatrixThirdContinuity Tensor.ThirdArrayContraction
  Matrix.CoefficientMaps Gibbs.Continuity Quadratic.Definitions
  Quadratic.Differentials Quadratic.GradientRegularity
  Quadratic.GradientEntryRegularity Goe.Definitions Goe.IndexPairs
  Goe.MatrixBasis Joint.Definitions.
Import GRing.Theory Num.Theory.
Import ListNotations.
Import Quadratic.GradientRegularity.QuadraticGrowthContinuity.
Open Scope R_scope.

(* Continuity of the four observables of the joint interpolation, as
   functions of a pair (x, z) of a vector x and the coordinates z of a
   symmetric matrix. joint_matrix n C t x z is
   C + sqrt (t / (n+1)) (x x^T - I) + sqrt (1 - t) * goe_matrix n z.
   joint_observables_continuous: joint_quadratic_trace, joint_goe_trace,
   joint_divergence and joint_remainder, built from the nested Gibbs
   gradient and its derivatives at that matrix, are continuous at every
   point of the product space euclidean_product, whose topology is the
   product topology. The lemmas ending in _base give the continuity of each
   building block along a map from any topological space that is
   continuous at the point. *)

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
  (* The map is rewritten with goe_basis_divergence. *)
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
  (* The map is rewritten with actual_third_evaluation. *)
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
