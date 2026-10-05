From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import MatrixDefinitions SoftMatrixDefinitions.

(* One block of a family of matrices. soft_matrix_block_replace n A i M is
   the family A with block i replaced by M. soft_matrix_row_offset gives
   the scores soft_matrix_scores of SoftMatrixDefinitions of the family A
   with block i replaced by the zero matrix: the part of the scores that
   does not depend on block i. *)

Definition soft_matrix_block_replace n (A : nat -> matrix n) i
    (M : matrix n) : nat -> matrix n :=
  fun j => if Nat.eq_dec j i then M else A j.

Definition soft_matrix_row_offset n y B I (A : nat -> matrix n) i : nat -> nat -> R :=
  soft_matrix_scores n y B I (soft_matrix_block_replace n A i (matrix_zero n)).
