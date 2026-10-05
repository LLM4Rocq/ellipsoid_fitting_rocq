From Stdlib Require Import Reals List FunctionalExtensionality.
From EllipsoidFitting Require Import MatrixDefinitions GoeDefinitions JointDefinitions
  MatrixCoordinates JointCoordinates
  RowCoordinateDefinitions RowCoordinates RowReplacement RowVectorCoordinates RowArrayDefinitions
  SoftMatrixDefinitions RowSliceDefinitions.

(* Port of theories/RowArrayCoordinates.v from Coquelicot to
   MathComp-Analysis.

   The original imported Coquelicot, which it did not use itself, and the
   bundles InterpolationFoundations and InterpolationProofs, from which it
   took the inner modules MatrixCoordinates
   (Import InterpolationFoundations.MatrixCoordinates) and JointCoordinates
   (Import InterpolationProofs.JointProofs.JointCoordinates). The port drops
   Coquelicot and the bundles, and imports the standalone ported modules
   MatrixCoordinates and JointCoordinates directly. These are the only
   changes: every theorem keeps its name, its arguments in the same order,
   its statement word for word and its proof.

   The statements say the same thing as before.
   - This module loads no MathComp library itself, so the notations are
     Stdlib's, as in the original: (i<N)%nat and (i<=m)%nat are Peano's lt
     and le, and + , * and - on nat are Nat.add, Nat.mul and Nat.sub. The
     hypothesis (i<=m)%nat of gaussian_row_array_entry is therefore the
     (i <= n)%coq_nat of the ported tuple_entry_build, which is Peano's le.
   - The joint vectors xz and xz' are elements of
     euclidean_product (vector_NormedModule n)
       (vector_NormedModule (goe_vector_index n))
     of the ported JointDefinitions, whose elements are the same pairs as
     Coquelicot's prod_NormedModule; their type is inferred from
     joint_vector_to_list, as in the original.
   - The array of gaussian_row_array is a tuple of the ported normed module
     matrix_NormedModule n; tuple_build and tuple_entry keep their
     definitions by recursion on the nested pairs, and matrix_zero n is the
     zero of that module, as Coquelicot's zero was.
   - joint_matrix, gaussian_row_pair, gaussian_row_matrix, row_assemble,
     row_background, soft_matrix_block_replace and soft_matrix_row_offset
     keep the texts of their originals in their ported modules.

   Assumptions. Print Assumptions on each theorem lists the seven axioms of
   analysis/README.md and no other. They come from the ported modules this
   one imports. *)

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
