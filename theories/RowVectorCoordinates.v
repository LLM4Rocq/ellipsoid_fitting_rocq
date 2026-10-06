From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions JointDefinitions
  JointCoordinates RowCoordinateDefinitions RowCoordinates RowReplacement.

(* Decoding a joint vector from a row of a list of N rows.
   row_assemble N K i background row places row at position i, the
   coordinates of background filling the N - 1 other rows, and
   row_chunk K i reads row i back.
   - row_joint_decode_assemble: placing the coordinates of a joint vector
     xz at row i and decoding row i gives xz back.
   - row_joint_decode_other_independent: the decoding of any other row j
     does not depend on the joint vector placed at row i. *)

Theorem row_joint_decode_assemble m n N i background xz :
  length background = ((N-1)*(S m+S n))%nat -> (i<N)%nat ->
  joint_vector_of_list m n
    (row_chunk (S m+S n) i
      (row_assemble N (S m+S n) i background (joint_vector_to_list m n xz))) = xz.
Proof.
  intros HB Hi; rewrite row_chunk_assemble by
    (try assumption; apply joint_vector_to_list_length).
  apply joint_vector_of_to_list.
Qed.

Theorem row_joint_decode_other_independent m n N i j background xz xz' :
  length background = ((N-1)*(S m+S n))%nat -> (i<N)%nat -> j<>i ->
  joint_vector_of_list m n
    (row_chunk (S m+S n) j
      (row_assemble N (S m+S n) i background (joint_vector_to_list m n xz))) =
  joint_vector_of_list m n
    (row_chunk (S m+S n) j
      (row_assemble N (S m+S n) i background (joint_vector_to_list m n xz'))).
Proof.
  intros HB Hi Hj; f_equal; apply row_chunk_other_independent;
    try assumption; apply joint_vector_to_list_length.
Qed.
