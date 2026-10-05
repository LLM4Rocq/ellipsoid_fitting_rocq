From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import MatrixDefinitions SoftMatrixDefinitions.

(* Port of theories/RowSliceDefinitions.v from Coquelicot to
   MathComp-Analysis. The original did not import Coquelicot. Its only
   Coquelicot content came through matrix n and matrix_zero of
   MatrixDefinitions and through soft_matrix_scores of SoftMatrixDefinitions.
   Their ports keep the same names and arguments. matrix_zero is now
   MathComp's 0 on the nested tuples, which is the zero matrix, as
   Coquelicot's zero was. So the text below is the original's. MathComp is
   not imported here, so the test Nat.eq_dec j i is Stdlib's, as before. *)

Definition soft_matrix_block_replace n (A : nat -> matrix n) i
    (M : matrix n) : nat -> matrix n :=
  fun j => if Nat.eq_dec j i then M else A j.

Definition soft_matrix_row_offset n y B I (A : nat -> matrix n) i : nat -> nat -> R :=
  soft_matrix_scores n y B I (soft_matrix_block_replace n A i (matrix_zero n)).
