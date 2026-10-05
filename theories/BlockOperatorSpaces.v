From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorBounds LowerDefinitions
  CoefficientDefinitions CoefficientMaps CoefficientBounds NormedTransport
  OperatorSpaceDefinitions OperatorNormedDefinitions OperatorSpaces
  BlockOperatorDefinitions BlockBasis BlockOperatorRepresentation BlockOperatorNormedDefinitions.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/BlockOperatorSpaces.v from Coquelicot to
   MathComp-Analysis. It follows the port of OperatorSpaces, which does the
   same for bounded_matrix_NormedModule n V.

   Every definition and theorem of the original keeps its name and its
   arguments, in the same order. No item is added. The statements change
   form in the ways of the ports of MatrixCoordinates, CoefficientMaps,
   OperatorSpaces, BlockOperatorDefinitions and
   BlockOperatorNormedDefinitions.

   1. Linear maps. Coquelicot's is_linear l is a record with three fields,
        l (plus x y) = plus (l x) (l y),
        l (scal k x) = scal k (l x),
        exists M, 0 < M /\ forall x, norm (l x) <= M * norm x.
      As in BlockOperatorDefinitions and OperatorSpaces, the port states it
      as the conjunction
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity, which is equivalent to the first
      two fields, and of Coquelicot's norm bound. The bound uses Stdlib's 0,
      <, <= and * around MathComp's norms. This is the predicate of
      bounded_block_map, so the proof argument Hf of block_operator_family
      has the type it had in the original, up to this translation, and
      exist _ (f x) (Hf x) is an element of bounded_block_map n m V as
      before.

   2. Coquelicot's NormedModule R_AbsRing becomes normedModType R, and its
      norm becomes MathComp's `|_|, written (`|_|)%R. On
      bounded_block_NormedModule n m V the operations and the norm are those
      that BlockOperatorNormedDefinitions transports from
      block_operator_coefficients n m V, as in the original: the norm of L is
      the norm of block_operator_encode n m V L.

   3. Norms and constants. block_operator_coefficients n m V carries the
      Euclidean norm of its m + 1 operators, each measured with the norm of
      bounded_matrix_NormedModule n V, and block_array n m the Euclidean norm
      of its m + 1 blocks, each measured with the Frobenius norm
      (MatrixDefinitions keeps Coquelicot's product norm). So
      block_operator_apply_product_bound means the same as in the original,
      constant INR (S m) * INR (S n)^2 included.

   4. Proofs. Coquelicot's is_linear_comp becomes matrix_linear_comp of
      MatrixCoordinates. The original rewrote functions with Coquelicot's
      is_linear_ext in block_operator_evaluation_linear and
      block_operator_family_linear. The port rewrites them with funext of
      MathComp's boolp, as the port of OperatorSpaces does. It rests on
      boolp.functional_extensionality_dep, one of the seven axioms of the
      README. No proof uses Classical_Prop.classic. *)

Theorem block_operator_encode_linear n m V :
  linear (block_operator_encode n m V :
    bounded_block_NormedModule n m V -> block_operator_coefficients n m V) /\
  exists M : R, 0 < M /\
    forall L : bounded_block_NormedModule n m V,
      (`|block_operator_encode n m V L|)%R <= M * (`|L|)%R.
Proof. apply transport_encode_linear. Qed.

Theorem block_operator_decode_linear n m V :
  linear (block_operator_decode n m V :
    block_operator_coefficients n m V -> bounded_block_NormedModule n m V) /\
  exists M : R, 0 < M /\
    forall C : block_operator_coefficients n m V,
      (`|block_operator_decode n m V C : bounded_block_NormedModule n m V|)%R <= M * (`|C|)%R.
Proof. apply transport_decode_linear. Qed.

Theorem block_operator_apply_encode n m V (L : bounded_block_map n m V) W :
  block_coefficient_apply n m V (block_operator_encode n m V L) W = block_operator_apply n m V L W.
Proof.
  change (block_operator_apply n m V (block_operator_decode n m V (block_operator_encode n m V L)) W =
    block_operator_apply n m V L W); rewrite block_operator_decode_encode; reflexivity.
Qed.

Theorem block_coefficient_apply_linear_coefficients n m V W :
  linear (fun C : block_operator_coefficients n m V => block_coefficient_apply n m V C W) /\
  exists M : R, 0 < M /\
    forall C : block_operator_coefficients n m V,
      (`|block_coefficient_apply n m V C W|)%R <= M * (`|C|)%R.
Proof.
  unfold block_coefficient_apply.
  apply (module_coordinate_sum_linear m (fun i (C : block_operator_coefficients n m V) =>
    operator_apply n V (block_operator_component n m V C i) (block_entry n m W i))).
  intros i Hi.
  apply (matrix_linear_comp
    (fun C : block_operator_coefficients n m V => block_operator_component n m V C i)
    (fun L : bounded_matrix_NormedModule n V => operator_apply n V L (block_entry n m W i))).
  - apply tuple_entry_linear.
  - apply operator_evaluation_linear.
Qed.

Theorem block_operator_evaluation_linear n m V W :
  linear (fun L : bounded_block_NormedModule n m V => block_operator_apply n m V L W) /\
  exists M : R, 0 < M /\
    forall L : bounded_block_NormedModule n m V,
      (`|block_operator_apply n m V L W|)%R <= M * (`|L|)%R.
Proof.
  destruct (matrix_linear_comp
    (block_operator_encode n m V :
      bounded_block_NormedModule n m V -> block_operator_coefficients n m V)
    (fun C => block_coefficient_apply n m V C W)
    (block_operator_encode_linear n m V)
    (block_coefficient_apply_linear_coefficients n m V W)) as [HL [M [HM HB]]].
  split.
  - have -> : (fun L : bounded_block_NormedModule n m V => block_operator_apply n m V L W) =
      (fun L : bounded_block_NormedModule n m V =>
        block_coefficient_apply n m V (block_operator_encode n m V L) W).
    { apply funext; intros L; symmetry; apply block_operator_apply_encode. }
    exact HL.
  - exists M; split; [exact HM|]; intros L.
    rewrite -block_operator_apply_encode; apply HB.
Qed.

Theorem block_operator_apply_linear n m V (L : bounded_block_NormedModule n m V) :
  linear (block_operator_apply n m V L) /\
  exists M : R, 0 < M /\
    forall W : block_array n m, (`|block_operator_apply n m V L W|)%R <= M * (`|W|)%R.
Proof. exact (proj2_sig L). Qed.

Theorem block_operator_norm_encode n m V (L : bounded_block_NormedModule n m V) :
  (`|L|)%R = (`|block_operator_encode n m V L|)%R.
Proof. reflexivity. Qed.

Theorem block_operator_norm_decode n m V (C : block_operator_coefficients n m V) :
  (`|block_operator_decode n m V C : bounded_block_NormedModule n m V|)%R = (`|C|)%R.
Proof.
  change ((`|block_operator_encode n m V (block_operator_decode n m V C)|)%R = (`|C|)%R).
  rewrite block_operator_encode_decode; reflexivity.
Qed.

Theorem block_operator_apply_product_bound n m V (L : bounded_block_NormedModule n m V) W :
  (`|block_operator_apply n m V L W|)%R <=
    INR (S m) * INR (S n)^2 * (`|L|)%R * (`|W|)%R.
Proof.
  rewrite -block_operator_apply_encode.
  unfold block_coefficient_apply.
  assert (HL : 0 <= (`|block_operator_encode n m V L|)%R) by (apply/RleP; apply normr_ge0).
  assert (HW : 0 <= (`|W|)%R) by (apply/RleP; apply normr_ge0).
  eapply Rle_trans.
  - apply (module_coordinate_sum_norm_bound V m _
      (INR (S n)^2 * (`|block_operator_encode n m V L|)%R * (`|W|)%R)).
    + apply Rmult_le_pos; [apply Rmult_le_pos; [apply pow2_ge_0|exact HL]|exact HW].
    + intros i Hi.
      eapply Rle_trans; [apply operator_apply_product_bound|].
      apply Rmult_le_compat.
      * apply Rmult_le_pos; [apply pow2_ge_0|apply/RleP; apply normr_ge0].
      * apply/RleP; apply normr_ge0.
      * apply Rmult_le_compat_l; [apply pow2_ge_0|apply tuple_entry_norm_bound].
      * apply tuple_entry_norm_bound.
  - change (INR (S m) * (INR (S n)^2 * (`|L|)%R * (`|W|)%R) <=
      INR (S m) * INR (S n)^2 * (`|L|)%R * (`|W|)%R); right; ring.
Qed.

Definition block_operator_family {E : Type} n m (V : normedModType R)
    (f : E -> block_array n m -> V)
    (Hf : forall x, linear (f x) /\
      exists M : R, 0 < M /\ forall W : block_array n m, (`|f x W|)%R <= M * (`|W|)%R)
    (x : E) : bounded_block_NormedModule n m V :=
  exist _ (f x) (Hf x).

Theorem block_operator_family_linear {E : normedModType R} n m (V : normedModType R)
    (f : E -> block_array n m -> V)
    (Hf : forall x, linear (f x) /\
      exists M : R, 0 < M /\ forall W : block_array n m, (`|f x W|)%R <= M * (`|W|)%R) :
  (forall W, linear (fun x => f x W) /\
    exists M : R, 0 < M /\ forall x : E, (`|f x W|)%R <= M * (`|x|)%R) ->
  linear (block_operator_family n m V f Hf) /\
  exists M : R, 0 < M /\
    forall x : E, (`|block_operator_family n m V f Hf x|)%R <= M * (`|x|)%R.
Proof.
  intros H.
  assert (HE : linear (fun x => block_operator_encode n m V (block_operator_family n m V f Hf x)) /\
    exists M : R, 0 < M /\
      forall x : E,
        (`|block_operator_encode n m V (block_operator_family n m V f Hf x)|)%R <= M * (`|x|)%R).
  { unfold block_operator_encode.
    refine (tuple_build_linear m _ _); intros i Hi.
    change (linear (operator_family n V
      (fun x M => f x (block_inject n m i M))
      (fun x => matrix_linear_comp (block_inject n m i) (f x)
        (block_inject_linear n m i) (Hf x))) /\
      exists M : R, 0 < M /\
        forall x : E, (`|operator_family n V
          (fun x M => f x (block_inject n m i M))
          (fun x => matrix_linear_comp (block_inject n m i) (f x)
            (block_inject_linear n m i) (Hf x)) x|)%R <= M * (`|x|)%R).
    apply operator_family_linear; intros; apply H. }
  have HQ : block_operator_family n m V f Hf =
    (fun x => block_operator_decode n m V
      (block_operator_encode n m V (block_operator_family n m V f Hf x))).
  { apply funext; intros x; symmetry; apply block_operator_decode_encode. }
  rewrite HQ; apply (matrix_linear_comp
    (fun x => block_operator_encode n m V (block_operator_family n m V f Hf x))
    (block_operator_decode n m V :
      block_operator_coefficients n m V -> bounded_block_NormedModule n m V));
    [exact HE|apply block_operator_decode_linear].
Qed.
