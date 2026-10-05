From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions LowerDefinitions OperatorNormedDefinitions.
Open Scope R_scope.

(* Port of theories/BlockOperatorDefinitions.v from Coquelicot to
   MathComp-Analysis.

   Coquelicot's NormedModule R_AbsRing becomes normedModType R, as in the
   ports of MatrixDefinitions, LowerDefinitions and OperatorSpaceDefinitions.
   block_array n m and the nested tuples of block_operator_coefficients n m V
   are those of MatrixDefinitions and LowerDefinitions, so they keep
   Coquelicot's product norm. A block array carries the Euclidean norm of its
   m + 1 blocks, each measured with the Frobenius norm, and the norm of a
   block of coefficients is the Euclidean norm of its m + 1 operators, each
   measured with the norm of bounded_matrix_NormedModule n V, as in the
   original.

   In block_inject, Coquelicot's zero of matrix_NormedModule n becomes
   MathComp's 0 of that space, written 0%R. It is the matrix whose entries
   are all 0, as before.

   One statement changes form: the predicate of bounded_block_map.
   Coquelicot's is_linear f is a record with three fields,
     f (plus x y) = plus (f x) (f y),
     f (scal k x) = scal k (f x),
     exists M, 0 < M /\ forall x, norm (f x) <= M * norm x.
   MathComp's linear f is the algebraic part only, which is equivalent to the
   first two fields. MathComp has no predicate for the third field, the bound
   that makes f continuous (README, difference 2). As in bounded_matrix_map
   of OperatorSpaceDefinitions, the port states Coquelicot's is_linear f as
   the conjunction
     linear f /\
     exists M : R, 0 < M /\ forall x, (`|f x|)%R <= M * (`|x|)%R.
   The bound uses Stdlib's 0, <, <= and * around MathComp's norms. The norm
   of x : block_array n m is the Euclidean norm of LowerDefinitions and the
   norm of f x is that of V, so the bound means the same as in the original,
   constants included. bounded_block_map n m V therefore has the same
   elements as in the original: the linear maps from block_array n m to V
   with a norm bound, which are the continuous linear maps.

   The other definitions keep the text of the original. The module declares
   no structure on bounded_block_map n m V. The port of
   BlockOperatorNormedDefinitions copies the transported normed module
   structure onto it, as OperatorNormedDefinitions does for
   bounded_matrix_map n V, and that copy needs the type to carry no other
   instance. The original opened no scope. The port opens R_scope after the
   MathComp imports, as the other ported definitions modules do, so that 0,
   <, <= and * in the bound are Stdlib's. *)

Definition block_inject n m i (M : matrix n) : block_array n m :=
  tuple_build (matrix_NormedModule n) m (fun j => if Nat.eqb j i then M else 0%R).

Definition block_operator_coefficients n m (V : normedModType R) : normedModType R :=
  tuple_NormedModule (bounded_matrix_NormedModule n V) m.

Definition bounded_block_map n m (V : normedModType R) : Type :=
  { f : block_array n m -> V | linear f /\
      exists M : R, 0 < M /\ forall x : block_array n m, (`|f x|)%R <= M * (`|x|)%R }.

Definition block_operator_apply n m V (L : bounded_block_map n m V) (W : block_array n m) : V :=
  proj1_sig L W.

Definition block_operator_component n m V (C : block_operator_coefficients n m V) i :=
  tuple_entry (bounded_matrix_NormedModule n V) m i C.
