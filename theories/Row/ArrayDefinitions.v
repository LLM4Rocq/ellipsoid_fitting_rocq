From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Matrix.Definitions Goe.Definitions
  Joint.Definitions Row.CoordinateDefinitions.

(* The interpolation path on all rows at once. The list xs is read in
   chunks of S n + S (goe_vector_index n) coordinates (row_chunk), and
   gaussian_row_pair n i xs is the pair (x_i, z_i) of vectors read from
   chunk i. gaussian_row_matrix n t i xs is joint_matrix n 0 t x_i z_i, that
   is sqrt (t / (n + 1)) (x_i x_i^T - I) + sqrt (1 - t) goe_matrix n z_i,
   and gaussian_row_array n m t xs is the block array of the S m row
   matrices. Its norm, from the nested tuples of Matrix.Definitions, is the
   Euclidean norm of all its entries. *)

Definition gaussian_row_pair n i (xs : list R) :=
  joint_vector_of_list n (goe_vector_index n)
    (row_chunk (S n+S(goe_vector_index n)) i xs).

Definition gaussian_row_matrix n t i (xs : list R) : matrix n :=
  joint_matrix n (matrix_zero n) t
    (fst (gaussian_row_pair n i xs)) (snd (gaussian_row_pair n i xs)).

Definition gaussian_row_array n m t (xs : list R) :=
  tuple_build (matrix_NormedModule n) m (fun i=>gaussian_row_matrix n t i xs).
