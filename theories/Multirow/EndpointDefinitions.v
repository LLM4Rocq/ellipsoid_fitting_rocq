From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.VectorListDefinitions Goe.Definitions Joint.Definitions
  Soft.MinimaxDerivativeDefinitions Row.CoordinateDefinitions.

(* The two endpoints of the multirow interpolation, as functions of a list
   of coordinates with no unused coordinate. The dimension is d = S n and
   there are N = S m rows; block i is read from the i-th chunk of the list
   (row_chunk), so blocks are in row order.
   - multirow_goe_array: N GOE matrices goe_matrix n, from
     N * S (goe_vector_index n) coordinates.
   - multirow_quadratic_array: N matrices joint_quadratic_input n x, from
     N * S n coordinates.
   multirow_goe_value and multirow_quadratic_value are lower_block_phi at
   these block arrays. *)
Definition multirow_goe_array n m (zs : list R) : block_array n m :=
  tuple_build (matrix_NormedModule n) m (fun i =>
    goe_matrix n (vector_of_list (goe_vector_index n)
      (row_chunk (S (goe_vector_index n)) i zs))).

Definition multirow_quadratic_array n m (xs : list R) : block_array n m :=
  tuple_build (matrix_NormedModule n) m (fun i =>
    joint_quadratic_input n (vector_of_list n (row_chunk (S n) i xs))).

Definition multirow_goe_value n m beta gamma y B Y S (zs : list R) : R :=
  lower_block_phi n m beta gamma y B Y S (multirow_goe_array n m zs).

Definition multirow_quadratic_value n m beta gamma y B Y S (xs : list R) : R :=
  lower_block_phi n m beta gamma y B Y S (multirow_quadratic_array n m xs).
