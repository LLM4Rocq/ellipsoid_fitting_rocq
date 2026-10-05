From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import LowerDefinitions BlockOperatorDefinitions BlockOperatorRepresentation
  BlockOperatorNormedDefinitions BlockOperatorSpaces BlockOperatorCalculus BlockC3Definitions.
Open Scope R_scope.

(* Port of theories/BlockC3Assembly.v from Coquelicot to MathComp-Analysis.

   The six theorems keep their names and their arguments, in the same order.
   No item is added. The statements change form in the ways of the ports of
   BlockOperatorSpaces, BlockOperatorCalculus and BlockC3Definitions, which
   this module imports.

   1. Linear maps. Coquelicot's is_linear l becomes the conjunction
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity and of Coquelicot's norm bound, as in
      BlockOperatorDefinitions and BlockOperatorSpaces. This is the predicate
      of bounded_block_map, so block_operator_linearity_from_evaluations
      still proves the side condition of an exist into bounded_block_map, as
      BlockGibbsC3 uses it. Coquelicot's NormedModule R_AbsRing becomes
      normedModType R.

   2. Frechet derivatives. Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis (README, difference 2), as in
      BlockOperatorCalculus and BlockC3Definitions. In block_C3_from_evaluations
      the scalar map F keeps its type block_array n m -> R and is written
      (F : block_array n m -> R^o) inside is_diff, as in block_operator_C3.
      The evaluations block_first_evaluation n m (D1 x) U and
      block_second_evaluation n m (D2 x) U V already have type R^o.

   3. Pointwise continuity. Coquelicot's continuous f A, continuity of f at
      the one point A, becomes {for A, continuous f} (README, difference 5).
      The domain E, a Coquelicot UniformSpace in the original, is here any
      topologicalType, as in BlockOperatorCalculus. Every uniform space of
      MathComp-Analysis is a topological space, so this generalizes the
      original.

   4. Norms. The operator spaces carry the norms that
      BlockOperatorNormedDefinitions transports from the coefficients, as in
      the original, so the linearity bound means the same, constants
      included, and the neighbourhoods, and so derivatives and continuity,
      are those of the original.

   Proofs. They follow the original. The original proved
   block_operator_family_eta with Stdlib's functional_extensionality. The
   port uses funext of MathComp's boolp, which rests on
   boolp.functional_extensionality_dep, one of the seven axioms of the
   README, as the ports of BlockOperatorRepresentation and
   BlockOperatorCalculus do. No proof uses Classical_Prop.classic.

   Using these lemmas. The continuity lemmas quantify over a
   topologicalType E. At a concrete E, such as block_array n m in
   block_C3_from_evaluations, plain apply cannot find the topology of E, so
   the proof uses ssreflect's apply:, as the ports of FiniteGibbsContinuity
   and MatrixThirdContinuity advise. *)

Theorem block_operator_family_eta {E : Type} n m (V : normedModType R)
    (f : E -> bounded_block_NormedModule n m V) :
  block_operator_family n m V (fun x W => block_operator_apply n m V (f x) W)
    (fun x => block_operator_apply_linear n m V (f x)) = f.
Proof.
  apply funext; intros x; apply bounded_block_map_ext; intros W; reflexivity.
Qed.

Theorem block_operator_linearity_from_evaluations {E : normedModType R} n m (V : normedModType R)
    (f : E -> bounded_block_NormedModule n m V) :
  (forall W, linear (fun x => block_operator_apply n m V (f x) W) /\
    exists M : R, 0 < M /\
      forall x : E, (`|block_operator_apply n m V (f x) W|)%R <= M * (`|x|)%R) ->
  linear f /\ exists M : R, 0 < M /\ forall x : E, (`|f x|)%R <= M * (`|x|)%R.
Proof.
  intros H; pose proof (block_operator_family_linear n m V
    (fun x W => block_operator_apply n m V (f x) W)
    (fun x => block_operator_apply_linear n m V (f x)) H) as HL.
  rewrite block_operator_family_eta in HL; exact HL.
Qed.

Theorem block_operator_frechet_from_evaluations {E : normedModType R} n m (V : normedModType R)
    (f D : E -> bounded_block_NormedModule n m V) (A : E) :
  (forall W, is_diff A (fun x => block_operator_apply n m V (f x) W)
    (fun U => block_operator_apply n m V (D U) W)) ->
  is_diff A f D.
Proof.
  intros H; pose proof (block_operator_family_frechet n m V
    (fun x W => block_operator_apply n m V (f x) W)
    (fun x => block_operator_apply_linear n m V (f x)) A
    (fun U W => block_operator_apply n m V (D U) W)
    (fun U => block_operator_apply_linear n m V (D U)) H) as HD.
  rewrite !block_operator_family_eta in HD; exact HD.
Qed.

Theorem block_operator_continuous_from_evaluations {E : topologicalType} n m (V : normedModType R)
    (f : E -> bounded_block_NormedModule n m V) (A : E) :
  (forall W, {for A, continuous (fun x => block_operator_apply n m V (f x) W)}) ->
  {for A, continuous f}.
Proof.
  intros H; pose proof (block_operator_family_continuous n m V
    (fun x W => block_operator_apply n m V (f x) W)
    (fun x => block_operator_apply_linear n m V (f x)) A H) as HC.
  rewrite block_operator_family_eta in HC; exact HC.
Qed.

Theorem block_third_operator_continuous_from_evaluations {E : topologicalType} n m
    (D3 : E -> block_third_operator_space n m) (A : E) :
  (forall U V W, {for A, continuous (fun x => block_third_evaluation n m (D3 x) U V W)}) ->
  {for A, continuous D3}.
Proof.
  intros H; apply block_operator_continuous_from_evaluations; intros W.
  apply block_operator_continuous_from_evaluations; intros V.
  apply block_operator_continuous_from_evaluations; intros U; apply H.
Qed.

Theorem block_C3_from_evaluations n m (F : block_array n m -> R)
    (D1 : block_array n m -> block_first_operator_space n m)
    (D2 : block_array n m -> block_second_operator_space n m)
    (D3 : block_array n m -> block_third_operator_space n m) :
  (forall A, is_diff A (F : block_array n m -> R^o) (block_first_evaluation n m (D1 A))) ->
  (forall A U, is_diff A (fun x => block_first_evaluation n m (D1 x) U)
    (fun V => block_second_evaluation n m (D2 A) U V)) ->
  (forall A U V, is_diff A (fun x => block_second_evaluation n m (D2 x) U V)
    (fun W => block_third_evaluation n m (D3 A) U V W)) ->
  (forall A U V W, {for A, continuous (fun x => block_third_evaluation n m (D3 x) U V W)}) ->
  block_operator_C3 n m F D1 D2 D3.
Proof.
  intros H1 H2 H3 HC A; split; [apply H1|].
  split.
  - apply block_operator_frechet_from_evaluations; intros U; apply H2.
  - split.
    + apply block_operator_frechet_from_evaluations; intros V.
      apply block_operator_frechet_from_evaluations; intros U; apply H3.
    + apply: block_third_operator_continuous_from_evaluations; intros; apply HC.
Qed.
