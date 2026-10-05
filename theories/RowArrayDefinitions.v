From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import MatrixDefinitions GoeDefinitions JointDefinitions RowCoordinateDefinitions.

(* Port of theories/RowArrayDefinitions.v from Coquelicot to MathComp-Analysis.

   The original imports Coquelicot but writes no Coquelicot notion itself: it
   uses tuple_build and matrix_NormedModule of MatrixDefinitions, and
   joint_vector_of_list, goe_vector_index, joint_matrix, matrix_zero and
   row_chunk of the other imported modules. Their ports keep the names,
   arguments and nested-pair representation, so the three definitions below
   keep the text of the original. The only change is the removed Coquelicot
   import. The array is now a tuple of the normed module matrix_NormedModule n
   of the port, whose norm is still the Euclidean norm of the nested tuples,
   so the norm of gaussian_row_array n m t xs is the same as before. *)

Definition gaussian_row_pair n i (xs : list R) :=
  joint_vector_of_list n (goe_vector_index n)
    (row_chunk (S n+S(goe_vector_index n)) i xs).

Definition gaussian_row_matrix n t i (xs : list R) : matrix n :=
  joint_matrix n (matrix_zero n) t
    (fst (gaussian_row_pair n i xs)) (snd (gaussian_row_pair n i xs)).

Definition gaussian_row_array n m t (xs : list R) :=
  tuple_build (matrix_NormedModule n) m (fun i=>gaussian_row_matrix n t i xs).
