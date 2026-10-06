From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions LowerDefinitions.
Open Scope R_scope.

(* Injection of a matrix into a block array. block_inject n m i M is the
   element of block_array n m (LowerDefinitions), with blocks 0, ..., m,
   whose block i is M and whose other blocks are 0. It is 0 when i > m. *)

Definition block_inject n m i (M : matrix n) : block_array n m :=
  tuple_build (matrix_NormedModule n) m (fun j => if Nat.eqb j i then M else 0%R).
