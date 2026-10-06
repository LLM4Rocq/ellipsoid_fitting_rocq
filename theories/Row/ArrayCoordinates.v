From Stdlib Require Import Reals List FunctionalExtensionality.
From EllipsoidFitting Require Import Matrix.Definitions Goe.Definitions
  Joint.Definitions Matrix.EntriesAndLinearMaps Joint.ListCoordinates
  Row.CoordinateDefinitions Row.Coordinates Row.Replacement Row.JointDecoding
  Row.ArrayDefinitions Soft.MatrixDefinitions Soft.BlockSliceDefinitions.

(* The rows of a list built by row_assemble, where each row of length
   S n + S (goe_vector_index n) holds a joint vector (x, z). When row i is
   the joint vector xz and the other rows come from background:
   - gaussian_row_pair_assemble: the pair read from row i is xz;
   - gaussian_row_pair_other_independent and
     gaussian_row_matrix_other_independent: the pairs and the matrices of
     the other rows do not depend on xz;
   - gaussian_row_zeroed_array_independent and
     gaussian_row_offset_independent: neither do the array of row matrices
     with block i replaced by zero, nor the offset soft_matrix_row_offset of
     row i. *)

Theorem gaussian_row_pair_assemble n N i background xz :
  length background = ((N-1)*(S n+S(goe_vector_index n)))%nat -> (i<N)%nat ->
  gaussian_row_pair n i (row_assemble N (S n+S(goe_vector_index n)) i background
    (joint_vector_to_list n (goe_vector_index n) xz)) = xz.
Proof. apply row_joint_decode_assemble. Qed.

Theorem gaussian_row_pair_other_independent n N i j background xz xz' :
  length background = ((N-1)*(S n+S(goe_vector_index n)))%nat -> (i<N)%nat -> j<>i ->
  gaussian_row_pair n j (row_assemble N (S n+S(goe_vector_index n)) i background
    (joint_vector_to_list n (goe_vector_index n) xz)) =
  gaussian_row_pair n j (row_assemble N (S n+S(goe_vector_index n)) i background
    (joint_vector_to_list n (goe_vector_index n) xz')).
Proof. apply row_joint_decode_other_independent. Qed.

Theorem gaussian_row_matrix_other_independent n N t i j background xz xz' :
  length background = ((N-1)*(S n+S(goe_vector_index n)))%nat -> (i<N)%nat -> j<>i ->
  gaussian_row_matrix n t j (row_assemble N (S n+S(goe_vector_index n)) i background
    (joint_vector_to_list n (goe_vector_index n) xz)) =
  gaussian_row_matrix n t j (row_assemble N (S n+S(goe_vector_index n)) i background
    (joint_vector_to_list n (goe_vector_index n) xz')).
Proof.
  intros HB Hi Hj; unfold gaussian_row_matrix.
  rewrite (gaussian_row_pair_other_independent n N i j background xz xz' HB Hi Hj); reflexivity.
Qed.

Theorem gaussian_row_zeroed_array_independent n N t i background xz xz' :
  length background = ((N-1)*(S n+S(goe_vector_index n)))%nat -> (i<N)%nat ->
  soft_matrix_block_replace n
    (fun j=>gaussian_row_matrix n t j
      (row_assemble N (S n+S(goe_vector_index n)) i background
        (joint_vector_to_list n (goe_vector_index n) xz))) i (matrix_zero n) =
  soft_matrix_block_replace n
    (fun j=>gaussian_row_matrix n t j
      (row_assemble N (S n+S(goe_vector_index n)) i background
        (joint_vector_to_list n (goe_vector_index n) xz'))) i (matrix_zero n).
Proof.
  intros HB Hi; apply functional_extensionality; intros j; unfold soft_matrix_block_replace.
  destruct (Nat.eq_dec j i); [reflexivity|].
  apply gaussian_row_matrix_other_independent; assumption.
Qed.

Theorem gaussian_row_offset_independent n N t y B I i background xz xz' :
  length background = ((N-1)*(S n+S(goe_vector_index n)))%nat -> (i<N)%nat ->
  soft_matrix_row_offset n y B I
    (fun j=>gaussian_row_matrix n t j
      (row_assemble N (S n+S(goe_vector_index n)) i background
        (joint_vector_to_list n (goe_vector_index n) xz))) i =
  soft_matrix_row_offset n y B I
    (fun j=>gaussian_row_matrix n t j
      (row_assemble N (S n+S(goe_vector_index n)) i background
        (joint_vector_to_list n (goe_vector_index n) xz'))) i.
Proof.
  intros HB Hi; unfold soft_matrix_row_offset.
  rewrite (gaussian_row_zeroed_array_independent n N t i background xz xz' HB Hi); reflexivity.
Qed.
