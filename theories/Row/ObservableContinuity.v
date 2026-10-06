From Stdlib Require Import Reals List Lia Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Goe.Definitions Joint.Definitions
  Chaos.SecondOrderDefinitions Analysis.CoordinateContinuityDefinitions
  Gaussian.CoordinateTuples Analysis.CoordinateTopology
  Quadratic.GradientRegularity Quadratic.GradientEntryRegularity
  Joint.ObservableContinuity Goe.MatrixBasis Soft.MinimaxDerivativeDefinitions
  Soft.LowerThirdDefinitions Matrix.BlockInjection Matrix.BlockBasis
  Gibbs.Continuity Soft.BlockPathContinuity Row.ArrayDefinitions
  Row.ObservableDefinitions Row.DecoderRegularity.
Import Quadratic.GradientRegularity.QuadraticGrowthContinuity.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Continuity of the row observables. Let E be a topological space and the
   paths U, A, X, Z be continuous at q. Then the injection of U into block
   i is continuous at q (block_inject_along_continuous). If 0 < gamma and Y
   and S are nonempty, so are the velocity and remainder terms built from
   lower_block_first and lower_block_third along A, X and Z
   (row_velocity_along_continuous, row_remainder_along_continuous). Hence,
   for i <= m, gaussian_row_velocity and gaussian_row_remainder are jointly
   continuous functions of S m * (S n + S (goe_vector_index n)) coordinates
   (gaussian_row_velocity_continuous, gaussian_row_remainder_continuous).

   Continuity at q is MathComp's {for q, continuous f}, for the Euclidean
   and Frobenius norms of vectors, matrices and block arrays. The local
   function inject of gaussian_row_velocity and gaussian_row_remainder is
   block_inject unfolded, so the lemmas along paths apply to them by
   conversion. The statements write (i <= m)%coq_nat, Stdlib's le, and the
   dimension with %coq_nat; there the inner sum elaborates to ssrnat's
   addn, which is convertible with Nat.add. *)

Lemma block_inject_along_continuous {E : topologicalType} n m i (U : E -> matrix n) q :
  {for q, continuous U} -> {for q, continuous (fun x => block_inject n m i (U x))}.
Proof.
  intro HU.
  apply (@continuous_comp E (matrix n) (block_array n m) U (block_inject n m i) q); [exact HU|].
  exact (@growth_linear_continuous (matrix_NormedModule n) (block_NormedModule n m)
    (block_inject n m i) (U q) (block_inject_linear n m i)).
Qed.

Lemma row_velocity_along_continuous {E : topologicalType} n m beta gamma y B Y S t i
    (A : E -> block_array n m) (X : E -> vector n) (Z : E -> vector (goe_vector_index n)) q :
  0<gamma -> Y<>[] -> S<>[] -> {for q, continuous A} -> {for q, continuous X} ->
  {for q, continuous Z} ->
  {for q, continuous (fun u =>
    lower_block_first n m beta gamma y B Y S (A u)
      (block_inject n m i (joint_quadratic_input n (X u))) / (2*sqrt t) -
    lower_block_first n m beta gamma y B Y S (A u)
      (block_inject n m i (goe_matrix n (Z u))) / (2*sqrt (1-t)))}.
Proof.
  intros Hg HY HS HA HX HZ; apply continuous_Rminus_fct;
    apply continuous_Rmult_fct; try apply: cst_continuous;
    apply block_first_along_continuous; try assumption; apply block_inject_along_continuous.
  - apply (@continuous_comp E (vector n) (matrix n) X (joint_quadratic_input n) q);
      [exact HX|apply joint_quadratic_input_continuous].
  - apply (@continuous_comp E (vector (goe_vector_index n)) (matrix n) Z (goe_matrix n) q);
      [exact HZ|].
    exact (@growth_linear_continuous (vector_NormedModule (goe_vector_index n))
      (matrix_NormedModule n) (goe_matrix n) (Z q) (goe_matrix_linear n)).
Qed.

Lemma row_remainder_along_continuous {E : topologicalType} n m beta gamma y B Y S i
    (A : E -> block_array n m) (X : E -> vector n) q :
  0<gamma -> Y<>[] -> S<>[] -> {for q, continuous A} -> {for q, continuous X} ->
  {for q, continuous (fun u => chaos_contraction n (fun U V W =>
    lower_block_third n m beta gamma y B Y S (A u)
      (block_inject n m i U) (block_inject n m i V) (block_inject n m i W)) (X u))}.
Proof.
  intros Hg HY HS HA HX; unfold chaos_contraction.
  apply continuous_Rmult_fct; [apply: cst_continuous|].
  apply growth_coordinate_sum_continuous; intros a Ha.
  apply growth_coordinate_sum_continuous; intros b Hb.
  apply block_third_along_continuous; try assumption.
  - apply block_inject_along_continuous.
    apply (@continuous_comp E (vector n) (matrix n) X (fun v => chaos_first n v a) q);
      [exact HX|apply matrix_component_chaos_first_continuous].
  - apply block_inject_along_continuous.
    apply (@continuous_comp E (vector n) (matrix n) X (fun v => chaos_first n v b) q);
      [exact HX|apply matrix_component_chaos_first_continuous].
  - apply: cst_continuous.
Qed.

Theorem gaussian_row_velocity_continuous n m beta gamma y B Y S t i :
  0<gamma -> Y<>[] -> S<>[] -> (i<=m)%coq_nat ->
  finite_joint_continuous (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
    (gaussian_row_velocity n m beta gamma y B Y S t i).
Proof.
  intros Hg HY HS Hi; apply finite_joint_continuous_filter; intro q.
  unfold gaussian_row_velocity.
  apply (@row_velocity_along_continuous
    (coordinates_uniform_space (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat)
    n m beta gamma y B Y S t i
    (fun w => gaussian_row_array n m t (coordinates_to_list _ w))
    (fun w => fst (gaussian_row_pair n i (coordinates_to_list _ w)))
    (fun w => snd (gaussian_row_pair n i (coordinates_to_list _ w))) q); try assumption.
  - apply gaussian_row_array_continuous.
  - apply (@continuous_comp
      (coordinates_uniform_space (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat)
      (euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n)))
      (vector n)
      (fun w => gaussian_row_pair n i (coordinates_to_list _ w)) fst q).
    + apply gaussian_row_pair_continuous; exact Hi.
    + apply euclidean_product_fst_continuous.
  - apply (@continuous_comp
      (coordinates_uniform_space (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat)
      (euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n)))
      (vector (goe_vector_index n))
      (fun w => gaussian_row_pair n i (coordinates_to_list _ w)) snd q).
    + apply gaussian_row_pair_continuous; exact Hi.
    + apply euclidean_product_snd_continuous.
Qed.

Theorem gaussian_row_remainder_continuous n m beta gamma y B Y S t i :
  0<gamma -> Y<>[] -> S<>[] -> (i<=m)%coq_nat ->
  finite_joint_continuous (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
    (gaussian_row_remainder n m beta gamma y B Y S t i).
Proof.
  intros Hg HY HS Hi; apply finite_joint_continuous_filter; intro q.
  unfold gaussian_row_remainder.
  apply (@row_remainder_along_continuous
    (coordinates_uniform_space (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat)
    n m beta gamma y B Y S i
    (fun w => gaussian_row_array n m t (coordinates_to_list _ w))
    (fun w => fst (gaussian_row_pair n i (coordinates_to_list _ w))) q); try assumption.
  - apply gaussian_row_array_continuous.
  - apply (@continuous_comp
      (coordinates_uniform_space (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat)
      (euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n)))
      (vector n)
      (fun w => gaussian_row_pair n i (coordinates_to_list _ w)) fst q).
    + apply gaussian_row_pair_continuous; exact Hi.
    + apply euclidean_product_fst_continuous.
Qed.
