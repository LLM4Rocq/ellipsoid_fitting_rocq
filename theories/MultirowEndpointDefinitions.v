From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import MatrixDefinitions VectorCoordinateDefinitions
  GoeDefinitions JointDefinitions LowerDefinitions RowCoordinateDefinitions.

(* Pure endpoints, with no unused coordinates. Dimension d = S n, rows N = S m.
   The GOE input has N * S (goe_vector_index n) scalar coordinates;
   the quadratic input has N * S n. Blocks are in row order. *)
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
