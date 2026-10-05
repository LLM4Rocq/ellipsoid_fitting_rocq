From Stdlib Require Import Reals List Lia Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions GoeDefinitions JointDefinitions
  SecondChaosDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateBasics GaussianCoordinateTopology
  QuadraticGrowthProofs GaussianMatrixComponents JointContinuity GoeSynthesis
  LowerDefinitions FullThirdDefinitions
  BlockOperatorDefinitions BlockBasis FiniteGibbsContinuity BlockAlongContinuity
  RowArrayDefinitions RowObservableDefinitions RowDecoderRegularity.
Import QuadraticGrowthProofs.QuadraticGrowthContinuity.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/RowObservableContinuity.v from Coquelicot to
   MathComp-Analysis.

   Imports. The original imported the bundles GaussianCoordinateProofs,
   InterpolationFoundations and InterpolationProofs, and opened six of their
   inner modules: GaussianCoordinateBasics and GaussianCoordinateTopology
   (from GaussianCoordinateProofs), QuadraticGrowthProofs.QuadraticGrowthContinuity
   and GaussianMatrixComponents (from InterpolationFoundations), JointContinuity
   (from InterpolationProofs.JointProofs) and GoeSynthesis (from
   InterpolationProofs.JointProofs.GoeProofs). The port imports these
   standalone ported modules directly. QuadraticGrowthContinuity stays an
   inner module of the ported QuadraticGrowthProofs, and is opened through
   it. The other imports are those of the original.

   Every lemma and theorem keeps its name and its arguments, in the same
   order. No item is added. The statements change form in the following
   ways, the ways of the ported modules this one uses. None changes meaning.

   1. Pointwise continuity. Coquelicot's continuous f q, continuity of f at
      the one point q, becomes MathComp's {for q, continuous f} (difference 5
      of analysis/README.md), in the hypotheses on the paths U, A, X, Z and
      in the conclusions of block_inject_along_continuous,
      row_velocity_along_continuous and row_remainder_along_continuous. The
      paths take values in matrix n, vector n, vector (goe_vector_index n)
      and block_array n m, whose ported norms are Coquelicot's Euclidean and
      Frobenius norms (MatrixDefinitions, OperatorDefinitions,
      LowerDefinitions), so their topologies are those of the original. The
      codomain R of the two real-valued conclusions carries the topology of
      Rstruct_topology, the topology of the absolute value, as in Coquelicot.

   2. The domain. E, a Coquelicot UniformSpace in the original, is here any
      topologicalType, as in the ported BlockAlongContinuity and
      QuadraticGrowthProofs, whose lemmas these proofs apply. Every uniform
      space of MathComp-Analysis is a topological space, and the statements
      speak only of continuity at one point, so this generalizes the
      original.

   3. Naturals. With ssreflect loaded, (i <= m)%nat means ssrnat's boolean
      leq, and + and * on nat mean ssrnat's addn and muln. The original means
      Stdlib's Peano order le, Nat.add and Nat.mul, so
      gaussian_row_velocity_continuous and gaussian_row_remainder_continuous
      write (i <= m)%coq_nat and
      (S m * (S n + S (goe_vector_index n)))%coq_nat, as the ported
      RowDecoderRegularity does. The order is Stdlib's le, as in the
      original. The dimension elaborates to
      Nat.mul (S m) (addn (S n) (S (goe_vector_index n))), the term of
      RowDecoderRegularity: Nat.mul reads its arguments in nat_scope, so the
      inner sum is ssrnat's addn. In MathComp 2.6 addn is defined as Nat.add,
      so the term is convertible with the original one and denotes the same
      number. finite_joint_continuous is the definition of the ported
      GaussianCoordinateDefinitions, whose text is the original one.

   The proofs follow the original. Coquelicot's continuous_comp becomes
   MathComp's continuous_comp, with the spaces given explicitly where the
   domain is a concrete type. continuous_const becomes cst_continuous,
   continuous_fst and continuous_snd on joint vectors become
   euclidean_product_fst_continuous and euclidean_product_snd_continuous of
   MatrixEuclideanProduct, and growth_linear_continuous is applied to the
   ported block_inject_linear and goe_matrix_linear, which state
   Coquelicot's is_linear as the conjunction of MathComp's linear and the
   norm bound. The local function inject of gaussian_row_velocity and
   gaussian_row_remainder is, token for token, block_inject of the ported
   BlockOperatorDefinitions, so the two lemmas along paths apply to the
   unfolded definitions by conversion, as in the original.

   Assumptions. Print Assumptions lists the seven axioms of
   analysis/README.md for block_inject_along_continuous, and the seven and
   Classical_Prop.classic for the four other items. Their statements
   mention lower_block_first or lower_block_third, which are built from
   soft_max and so from Stdlib's Rpower.ln; no proof here calls classic. *)

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
