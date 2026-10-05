From Stdlib Require Import Reals Lia Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorBounds LowerDefinitions
  CoefficientDefinitions CoefficientMaps OperatorRepresentation BlockOperatorDefinitions.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/BlockBasis.v from Coquelicot to MathComp-Analysis.

   Every theorem of the original keeps its name and its arguments, in the
   same order. The statements change form in the ways of the ports of
   MatrixCoordinates, CoefficientMaps and OperatorRepresentation.

   1. Linear maps. Coquelicot's is_linear l is a record with three fields:
      l (plus x y) = plus (l x) (l y), l (scal k x) = scal k (l x), and
      exists M, 0 < M /\ forall x, norm (l x) <= M * norm x.
      As in MatrixCoordinates, CoefficientMaps and BlockOperatorDefinitions,
      the port states it as the conjunction
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity, which is equivalent to the first two
      fields, and of Coquelicot's norm bound. The bound uses Stdlib's 0, <,
      <= and * around MathComp's norms. The norms are those of
      MatrixDefinitions and LowerDefinitions: the Frobenius norm on matrix n
      and the Euclidean norm of the m + 1 blocks on block_array n m, as in
      Coquelicot. So block_entry_linear and block_inject_linear mean the same
      as in the original, constants included.

   2. Coquelicot's zero of matrix_NormedModule n becomes MathComp's 0 of that
      space, written 0%R, as in block_inject of BlockOperatorDefinitions. It
      is the matrix whose entries are all 0, as before.

   3. Order on indices. With ssreflect loaded, (j <= m)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so
      block_entry_inject writes (j <= m)%coq_nat, which is Stdlib's le.

   4. Proofs. Coquelicot's is_linear_id and is_linear_zero are proved in
      place, with the bound constant 1. Coquelicot's scal_one and
      scal_zero_l become MathComp's scale1r and scale0r. The scalars 1 and 0
      of the intermediate sum in block_sum_injections are written inside %R,
      as in module_coordinate_sum_select of OperatorRepresentation.

   The port adds one item, marked below: a Hierarchy Builder instance that
   declares block_inject n m i a linear map, as MatrixCoordinates does for
   tuple_entry and OperatorBounds for matrix_action. It has no name of its
   own and changes no statement. *)

(* Declaring block_inject n m i a linear map makes HB report canonical
   projections that duplicate existing ones. Rocq ignores the duplicates; the
   warning is silenced in this file only. *)
Local Set Warnings "-redundant-canonical-projection".

Theorem block_entry_linear n m i :
  linear (fun W : block_array n m => block_entry n m W i) /\
  exists M : R, 0 < M /\
    forall W : block_array n m, (`|block_entry n m W i|)%R <= M * (`|W|)%R.
Proof. apply tuple_entry_linear. Qed.

Theorem block_inject_linear n m i :
  linear (block_inject n m i) /\
  exists M : R, 0 < M /\
    forall x : matrix n, (`|block_inject n m i x|)%R <= M * (`|x|)%R.
Proof.
  unfold block_inject.
  apply (tuple_build_linear m
    (fun j (x : matrix n) => if Nat.eqb j i then x else 0%R)).
  intros j Hj; destruct (Nat.eqb j i).
  - split.
    + intros a u v; reflexivity.
    + exists 1; split; [lra|]; intros x; lra.
  - split.
    + intros a u v; by rewrite scaler0 addr0.
    + exists 1; split; [lra|]; intros x; rewrite normr0 Rmult_1_l.
      apply/RleP; apply normr_ge0.
Qed.

(* Added by the port. block_inject n m i is a {linear _ -> _} of MathComp, so
   that linearD, linearZ, linear0 and the other lemmas about linear maps
   apply to it directly, in place of Coquelicot's linear_plus, linear_scal
   and linear_zero. The instance changes no statement. *)
HB.instance Definition _ n m i :=
  GRing.isLinear.Build R (matrix_NormedModule n) (block_NormedModule n m) *:%R
    (block_inject n m i) (proj1 (block_inject_linear n m i)).

Theorem block_entry_inject n m i j (M : matrix n) :
  (j <= m)%coq_nat ->
  block_entry n m (block_inject n m i M) j = if Nat.eqb j i then M else 0%R.
Proof.
  intros Hj; unfold block_entry, block_inject.
  exact (tuple_entry_build (matrix_NormedModule n) m j
    (fun k => if Nat.eqb k i then M else 0%R) Hj).
Qed.

Theorem block_sum_injections n m (W : block_array n m) :
  module_coordinate_sum (block_NormedModule n m) m
    (fun i => block_inject n m i (block_entry n m W i)) = W.
Proof.
  apply tuple_ext; intros j Hj.
  change ((fun B : block_array n m => block_entry n m B j)
    (module_coordinate_sum (block_NormedModule n m) m
      (fun i => block_inject n m i (block_entry n m W i))) = block_entry n m W j).
  etransitivity.
  - exact (@linear_module_coordinate_sum (block_NormedModule n m) (matrix_NormedModule n) m
      (fun i => block_inject n m i (block_entry n m W i))
      (fun B => block_entry n m B j) (block_entry_linear n m j)).
  - transitivity (module_coordinate_sum (matrix_NormedModule n) m
      (fun i => ((if Nat.eqb i j then 1 else 0) *: block_entry n m W i)%R)).
    + apply module_coordinate_sum_ext; intros i Hi.
      rewrite (block_entry_inject n m i j _ Hj) (Nat.eqb_sym j i).
      destruct (Nat.eqb i j); [by rewrite scale1r | by rewrite scale0r].
    + exact (module_coordinate_sum_select (matrix_NormedModule n) m j
        (block_entry n m W) Hj).
Qed.
