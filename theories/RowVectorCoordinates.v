From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions JointDefinitions
  JointCoordinates RowCoordinateDefinitions RowCoordinates RowReplacement.

(* Port of theories/RowVectorCoordinates.v from Coquelicot to
   MathComp-Analysis.

   The original imported Coquelicot, which it did not use itself, and the
   bundle InterpolationProofs, from which it took the inner module
   JointCoordinates (Import InterpolationProofs.JointProofs.JointCoordinates).
   The port drops Coquelicot and imports the standalone ported module
   JointCoordinates directly. These are the only changes: every theorem keeps
   its name, its arguments in the same order, its statement word for word and
   its proof.

   The statements say the same thing as before. The joint vector xz is now an
   element of euclidean_product (vector_NormedModule m) (vector_NormedModule n)
   of the ported JointDefinitions, whose elements are the same pairs as
   Coquelicot's prod_NormedModule; its type is inferred from
   joint_vector_to_list, as in the original. joint_vector_of_list,
   joint_vector_to_list, row_chunk, row_assemble and row_background keep their
   definitions in their ports.

   This module loads no MathComp library itself, so the notations are Stdlib's
   as in the original: (i<N)%nat is Peano's lt, and + , * and - on nat are
   Nat.add, Nat.mul and Nat.sub. They agree with the (S m + S n)%coq_nat of
   the ported JointCoordinates, which denotes Nat.add. Stdlib's rewrite
   ... by, used in the first proof, is available because ssreflect's rewrite
   is not loaded here.

   Assumptions. Print Assumptions on each theorem lists the seven axioms of
   analysis/README.md and no other. They come from the ported modules this
   one imports (the type euclidean_product and the lemmas of
   JointCoordinates). *)

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

Theorem row_joint_reencode_chunk m n N i xs :
  length xs = (N*(S m+S n))%nat -> (i<N)%nat ->
  joint_vector_to_list m n
    (joint_vector_of_list m n (row_chunk (S m+S n) i xs)) = row_chunk (S m+S n) i xs.
Proof.
  intros HL Hi; apply joint_vector_to_of_list.
  apply row_chunk_length with (N:=N); assumption.
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

Theorem row_joint_decode_replacement_other m n N i j xs xz :
  length xs = (N*(S m+S n))%nat -> (i<N)%nat -> j<>i ->
  joint_vector_of_list m n
    (row_chunk (S m+S n) j
      (row_assemble N (S m+S n) i (row_background N (S m+S n) i xs)
        (joint_vector_to_list m n xz))) =
  joint_vector_of_list m n (row_chunk (S m+S n) j xs).
Proof.
  intros HL Hi Hj; f_equal; apply row_chunk_replacement_other;
    try assumption; apply joint_vector_to_list_length.
Qed.
