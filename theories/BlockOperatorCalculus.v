From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixAssembly MatrixThirdContinuity
  GradientDefinitions LowerDefinitions OperatorSpaceDefinitions OperatorRepresentation
  OperatorNormedDefinitions OperatorSpaces BlockOperatorDefinitions BlockBasis
  BlockOperatorRepresentation BlockOperatorNormedDefinitions BlockOperatorSpaces.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/BlockOperatorCalculus.v from Coquelicot to
   MathComp-Analysis.

   The four theorems keep their names and their arguments, in the same
   order. No item is added. The statements change form in the ways of the
   ports of MatrixAssembly, MatrixThirdContinuity, OperatorSpaces and
   BlockOperatorSpaces, which this module imports.

   1. Linear maps. Coquelicot's is_linear l becomes the conjunction
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity and of Coquelicot's norm bound, as in
      OperatorSpaceDefinitions and BlockOperatorDefinitions. This is the
      predicate of bounded_matrix_map and bounded_block_map, so the proof
      arguments Hf and HD have the type that operator_family and
      block_operator_family expect, as in the original.

   2. Frechet derivatives. Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis, as in the port of MatrixAssembly:
      f is differentiable at A and its differential 'd f A is l. Both say
      that f (A + H) = f A + l H + o(H), with l linear and continuous.
      Coquelicot's NormedModule R_AbsRing becomes normedModType R.

   3. Pointwise continuity. Coquelicot's continuous f A, continuity of f at
      the one point A, becomes MathComp's {for A, continuous f}
      (difference 5 of analysis/README.md). The domain E, a Coquelicot
      UniformSpace in the original, is here any topologicalType, as in the
      port of MatrixThirdContinuity. Every uniform space of MathComp-Analysis
      is a topological space, so this generalizes the original.

   4. Norms. The codomains bounded_matrix_NormedModule n V and
      bounded_block_NormedModule n m V carry the structures that
      OperatorNormedDefinitions and BlockOperatorNormedDefinitions transport
      from the coefficients, as in the original. Their neighbourhoods are
      those of the original, so derivatives and continuity mean the same.

   Proofs. They follow the original: the coefficients of the family are
   differentiable (or continuous) entry by entry, by tuple_build_frechet of
   MatrixAssembly (or tuple_build_continuous of MatrixThirdContinuity), and
   the family is the decoding of its coefficients. Coquelicot's
   filterdiff_ext becomes rewriting the function with funext of MathComp's
   boolp. filterdiff_comp' becomes is_diff_comp, which states the composite
   as g \o f and dg \o df. filterdiff_linear applied to operator_decode_linear
   becomes matrix_linear_is_diff of MatrixCoordinates, and
   filterdiff_continuous becomes matrix_linear_continuous of
   MatrixCoordinates. continuous_ext and continuous_comp become funext and
   MathComp's continuous_comp. The original imported Stdlib's
   FunctionalExtensionality without using it, since Coquelicot's
   filterdiff_ext and continuous_ext take pointwise equalities. The port
   drops that import and uses boolp.funext, which rests on
   boolp.functional_extensionality_dep, one of the seven axioms of the
   README. No proof uses Classical_Prop.classic. The port imports
   MatrixCoordinates, which the original did not import, for
   matrix_linear_comp, matrix_linear_is_diff and matrix_linear_continuous.

   Using these lemmas. The statements quantify over E, so an importer that
   applies them at a concrete E may need ssreflect's apply: or E given
   explicitly, as for the lemmas of MatrixThirdContinuity. *)

Theorem matrix_operator_family_frechet {E : normedModType R} n (V : normedModType R)
    (f : E -> matrix n -> V)
    (Hf : forall x, linear (f x) /\
      exists M : R, 0 < M /\ forall W : matrix n, (`|f x W|)%R <= M * (`|W|)%R)
    (A : E)
    (D : E -> matrix n -> V)
    (HD : forall U, linear (D U) /\
      exists M : R, 0 < M /\ forall W : matrix n, (`|D U W|)%R <= M * (`|W|)%R) :
  (forall W, is_diff A (fun x => f x W) (fun U => D U W)) ->
  is_diff A (operator_family n V f Hf) (operator_family n V D HD).
Proof.
  intros HF.
  assert (HE : is_diff A (fun x => operator_encode n V (operator_family n V f Hf x))
    (fun U => operator_encode n V (operator_family n V D HD U))).
  { unfold operator_encode, operator_family, operator_apply; simpl.
    apply tuple_build_frechet; intros i Hi; apply tuple_build_frechet; intros j Hj; apply HF. }
  have Hf' : operator_family n V f Hf =
    (operator_decode n V : operator_coefficients n V -> bounded_matrix_NormedModule n V)
      \o (fun x => operator_encode n V (operator_family n V f Hf x)).
  { apply funext; intros x; symmetry; apply operator_decode_encode. }
  have HD' : operator_family n V D HD =
    (operator_decode n V : operator_coefficients n V -> bounded_matrix_NormedModule n V)
      \o (fun U => operator_encode n V (operator_family n V D HD U)).
  { apply funext; intros U; symmetry; apply operator_decode_encode. }
  rewrite Hf' HD'.
  exact (@is_diff_comp R E (operator_coefficients n V) (bounded_matrix_NormedModule n V)
    _ _ _ _ A HE (matrix_linear_is_diff _ _ (operator_decode_linear n V))).
Qed.

Theorem matrix_operator_family_continuous {E : topologicalType} n (V : normedModType R)
    (f : E -> matrix n -> V)
    (Hf : forall x, linear (f x) /\
      exists M : R, 0 < M /\ forall W : matrix n, (`|f x W|)%R <= M * (`|W|)%R)
    (A : E) :
  (forall W, {for A, continuous (fun x => f x W)}) ->
  {for A, continuous (operator_family n V f Hf)}.
Proof.
  intros HF.
  assert (HE : {for A, continuous (fun x => operator_encode n V (operator_family n V f Hf x))}).
  { unfold operator_encode, operator_family, operator_apply; simpl.
    apply tuple_build_continuous; intros i Hi.
    apply tuple_build_continuous; intros j Hj; apply HF. }
  have Hf' : operator_family n V f Hf =
    (operator_decode n V : operator_coefficients n V -> bounded_matrix_NormedModule n V)
      \o (fun x => operator_encode n V (operator_family n V f Hf x)).
  { apply funext; intros x; symmetry; apply operator_decode_encode. }
  rewrite Hf'.
  apply: continuous_comp; [exact HE|].
  apply (matrix_linear_continuous
    (operator_decode n V : operator_coefficients n V -> bounded_matrix_NormedModule n V)).
  apply operator_decode_linear.
Qed.

Theorem block_operator_family_frechet {E : normedModType R} n m (V : normedModType R)
    (f : E -> block_array n m -> V)
    (Hf : forall x, linear (f x) /\
      exists M : R, 0 < M /\ forall W : block_array n m, (`|f x W|)%R <= M * (`|W|)%R)
    (A : E)
    (D : E -> block_array n m -> V)
    (HD : forall U, linear (D U) /\
      exists M : R, 0 < M /\ forall W : block_array n m, (`|D U W|)%R <= M * (`|W|)%R) :
  (forall W, is_diff A (fun x => f x W) (fun U => D U W)) ->
  is_diff A (block_operator_family n m V f Hf) (block_operator_family n m V D HD).
Proof.
  intros HF.
  assert (HE : is_diff A
    (fun x => block_operator_encode n m V (block_operator_family n m V f Hf x))
    (fun U => block_operator_encode n m V (block_operator_family n m V D HD U))).
  { unfold block_operator_encode; apply tuple_build_frechet; intros i Hi.
    change (is_diff A
      (operator_family n V (fun x M => f x (block_inject n m i M))
        (fun x => matrix_linear_comp (block_inject n m i) (f x)
          (block_inject_linear n m i) (Hf x)))
      (operator_family n V (fun U M => D U (block_inject n m i M))
        (fun U => matrix_linear_comp (block_inject n m i) (D U)
          (block_inject_linear n m i) (HD U)))).
    apply matrix_operator_family_frechet; intros; apply HF. }
  have Hf' : block_operator_family n m V f Hf =
    (block_operator_decode n m V :
      block_operator_coefficients n m V -> bounded_block_NormedModule n m V)
      \o (fun x => block_operator_encode n m V (block_operator_family n m V f Hf x)).
  { apply funext; intros x; symmetry; apply block_operator_decode_encode. }
  have HD' : block_operator_family n m V D HD =
    (block_operator_decode n m V :
      block_operator_coefficients n m V -> bounded_block_NormedModule n m V)
      \o (fun U => block_operator_encode n m V (block_operator_family n m V D HD U)).
  { apply funext; intros U; symmetry; apply block_operator_decode_encode. }
  rewrite Hf' HD'.
  exact (@is_diff_comp R E (block_operator_coefficients n m V) (bounded_block_NormedModule n m V)
    _ _ _ _ A HE (matrix_linear_is_diff _ _ (block_operator_decode_linear n m V))).
Qed.

Theorem block_operator_family_continuous {E : topologicalType} n m (V : normedModType R)
    (f : E -> block_array n m -> V)
    (Hf : forall x, linear (f x) /\
      exists M : R, 0 < M /\ forall W : block_array n m, (`|f x W|)%R <= M * (`|W|)%R)
    (A : E) :
  (forall W, {for A, continuous (fun x => f x W)}) ->
  {for A, continuous (block_operator_family n m V f Hf)}.
Proof.
  intros HF.
  assert (HE : {for A, continuous
    (fun x => block_operator_encode n m V (block_operator_family n m V f Hf x))}).
  { unfold block_operator_encode; apply tuple_build_continuous; intros i Hi.
    change ({for A, continuous
      (operator_family n V (fun x M => f x (block_inject n m i M))
        (fun x => matrix_linear_comp (block_inject n m i) (f x)
          (block_inject_linear n m i) (Hf x)))}).
    apply matrix_operator_family_continuous; intros; apply HF. }
  have Hf' : block_operator_family n m V f Hf =
    (block_operator_decode n m V :
      block_operator_coefficients n m V -> bounded_block_NormedModule n m V)
      \o (fun x => block_operator_encode n m V (block_operator_family n m V f Hf x)).
  { apply funext; intros x; symmetry; apply block_operator_decode_encode. }
  rewrite Hf'.
  apply: continuous_comp; [exact HE|].
  apply (matrix_linear_continuous
    (block_operator_decode n m V :
      block_operator_coefficients n m V -> bounded_block_NormedModule n m V)).
  apply block_operator_decode_linear.
Qed.
