From Stdlib Require Import Reals Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates LowerDefinitions
  CoefficientDefinitions CoefficientMaps OperatorSpaceDefinitions OperatorRepresentation
  OperatorNormedDefinitions OperatorSpaces BlockOperatorDefinitions BlockBasis.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/BlockOperatorRepresentation.v from Coquelicot to
   MathComp-Analysis.

   Every definition and theorem of the original keeps its name and its
   arguments, in the same order. No item is added. The statements change
   form in the ways of the ports of MatrixCoordinates, CoefficientMaps,
   OperatorRepresentation, OperatorSpaces, BlockOperatorDefinitions and
   BlockBasis.

   1. Linear maps. Coquelicot's is_linear f is a record with three fields,
        f (plus x y) = plus (f x) (f y),
        f (scal k x) = scal k (f x),
        exists M, 0 < M /\ forall x, norm (f x) <= M * norm x.
      As in BlockOperatorDefinitions, the port states it as the conjunction
        linear f /\
        exists M : R, 0 < M /\ forall x, (`|f x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity, which is equivalent to the first two
      fields, and of Coquelicot's norm bound. The bound uses Stdlib's 0, <,
      <= and * around MathComp's norms. This is the predicate of
      bounded_block_map in BlockOperatorDefinitions and of bounded_matrix_map
      in OperatorSpaceDefinitions. So block_operator_restrict n m V L i packs
      the same map M |-> L (block_inject n m i M) as in the original, and
      block_operator_decode n m V C packs block_coefficient_apply n m V C with
      the proof block_coefficient_apply_linear n m V C, as in the original.
      The norms are those of MatrixDefinitions and LowerDefinitions: the
      Frobenius norm on matrix n and the Euclidean norm of the m + 1 blocks on
      block_array n m, as in Coquelicot, so block_coefficient_apply_linear
      means the same as in the original, constants included.

   2. The carrier of bounded_matrix_NormedModule n V is bounded_matrix_map n V
      (OperatorNormedDefinitions), as in the original, so an element built
      with exist has that type by conversion, and the components of a block of
      coefficients are applied with operator_apply as in the original.

   3. Order on indices. With ssreflect loaded, (j <= m)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so
      block_coefficient_apply_inject writes (j <= m)%coq_nat, which is
      Stdlib's le.

   4. Proofs. Coquelicot's is_linear_comp becomes matrix_linear_comp of
      MatrixCoordinates. Coquelicot's scal_one and scal_zero_l become
      MathComp's scale1r and scale0r, and linear_zero becomes MathComp's
      linear0, applied to operator_apply n V L packed as a {linear _ -> _}
      inside the proof. The scalars 1 and 0 of the intermediate sum in
      block_coefficient_apply_inject are written inside %R, as in
      module_coordinate_sum_select of OperatorRepresentation. Through Rstruct
      they are Stdlib's R1 and R0.

   5. Axioms. The original proved bounded_block_map_ext with Stdlib's
      functional_extensionality and Classical_Prop.proof_irrelevance. The port
      uses funext and Prop_irrelevance of MathComp's boolp instead, as the
      port of OperatorRepresentation does. They rest on
      boolp.functional_extensionality_dep and
      boolp.propositional_extensionality, two of the seven axioms of the
      README, so the module does not need Classical_Prop.classic. *)

Theorem bounded_block_map_ext n m V (L M : bounded_block_map n m V) :
  (forall W, block_operator_apply n m V L W = block_operator_apply n m V M W) -> L = M.
Proof.
  destruct L as [f Hf], M as [g Hg]; intros H.
  assert (f = g) by (apply funext; exact H).
  subst; f_equal; apply Prop_irrelevance.
Qed.

Definition block_operator_restrict n m V (L : bounded_block_map n m V) (i : nat) : bounded_matrix_NormedModule n V.
Proof.
  refine (exist _ (fun M => block_operator_apply n m V L (block_inject n m i M)) _).
  apply (matrix_linear_comp (block_inject n m i) (block_operator_apply n m V L)).
  - apply block_inject_linear.
  - exact (proj2_sig L).
Defined.

Definition block_operator_encode n m V (L : bounded_block_map n m V) : block_operator_coefficients n m V :=
  tuple_build (bounded_matrix_NormedModule n V) m (block_operator_restrict n m V L).

Definition block_coefficient_apply n m V (C : block_operator_coefficients n m V) (W : block_array n m) : V :=
  module_coordinate_sum V m (fun i => operator_apply n V (block_operator_component n m V C i)
    (block_entry n m W i)).

Theorem block_coefficient_apply_linear n m V C :
  linear (block_coefficient_apply n m V C) /\
  exists M : R, 0 < M /\
    forall W : block_array n m, (`|block_coefficient_apply n m V C W|)%R <= M * (`|W|)%R.
Proof.
  unfold block_coefficient_apply.
  apply (module_coordinate_sum_linear m (fun i (W : block_array n m) =>
    operator_apply n V (block_operator_component n m V C i) (block_entry n m W i))).
  intros i Hi.
  apply (matrix_linear_comp (fun W : block_array n m => block_entry n m W i)
    (operator_apply n V (block_operator_component n m V C i))).
  - apply block_entry_linear.
  - apply operator_apply_linear.
Qed.

Definition block_operator_decode n m V (C : block_operator_coefficients n m V) : bounded_block_map n m V :=
  exist _ (block_coefficient_apply n m V C) (block_coefficient_apply_linear n m V C).

Theorem block_operator_decode_encode n m V (L : bounded_block_map n m V) :
  block_operator_decode n m V (block_operator_encode n m V L) = L.
Proof.
  apply bounded_block_map_ext; intros W.
  change (module_coordinate_sum V m (fun i => operator_apply n V
    (block_operator_component n m V (block_operator_encode n m V L) i)
    (block_entry n m W i)) = block_operator_apply n m V L W).
  transitivity (module_coordinate_sum V m (fun i => block_operator_apply n m V L
    (block_inject n m i (block_entry n m W i)))).
  - apply module_coordinate_sum_ext; intros i Hi.
    unfold block_operator_component, block_operator_encode.
    rewrite (tuple_entry_build (bounded_matrix_NormedModule n V) m i
      (block_operator_restrict n m V L) Hi).
    reflexivity.
  - exact (eq_trans (esym (@linear_module_coordinate_sum (block_NormedModule n m) V m
      (fun i => block_inject n m i (block_entry n m W i))
      (block_operator_apply n m V L) (proj2_sig L)))
      (f_equal (block_operator_apply n m V L) (block_sum_injections n m W))).
Qed.

Theorem block_coefficient_apply_inject n m V C j (M : matrix n) :
  (j <= m)%coq_nat ->
  block_coefficient_apply n m V C (block_inject n m j M) =
  operator_apply n V (block_operator_component n m V C j) M.
Proof.
  intros Hj; unfold block_coefficient_apply.
  transitivity (module_coordinate_sum V m (fun i => ((if Nat.eqb i j then 1 else 0) *:
    operator_apply n V (block_operator_component n m V C i) M)%R)).
  - apply module_coordinate_sum_ext; intros i Hi.
    rewrite (block_entry_inject n m j i M Hi); destruct (Nat.eqb i j).
    + by rewrite scale1r.
    + pose F : {linear matrix_NormedModule n -> V} :=
        HB.pack (operator_apply n V (block_operator_component n m V C i))
          (GRing.isLinear.Build R (matrix_NormedModule n) V *:%R
            (operator_apply n V (block_operator_component n m V C i))
            (proj1 (operator_apply_linear n V (block_operator_component n m V C i)))).
      rewrite scale0r; exact (linear0 F).
  - exact (module_coordinate_sum_select V m j
      (fun i => operator_apply n V (block_operator_component n m V C i) M) Hj).
Qed.

Theorem block_operator_encode_decode n m V (C : block_operator_coefficients n m V) :
  block_operator_encode n m V (block_operator_decode n m V C) = C.
Proof.
  apply tuple_ext; intros i Hi; unfold block_operator_encode.
  rewrite (tuple_entry_build (bounded_matrix_NormedModule n V) m i
    (block_operator_restrict n m V (block_operator_decode n m V C)) Hi).
  apply bounded_matrix_map_ext; intros M; apply block_coefficient_apply_inject; assumption.
Qed.
