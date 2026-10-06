From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import normedtype.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Matrix.VectorListDefinitions Joint.Definitions
  Goe.Definitions Gaussian.IteratedExpectationDefinitions
  Row.CoordinateDefinitions Row.Coordinates Row.ArrayDefinitions
  Row.PrefixDefinitions Radius.Definitions Radius.InterleavedRows.
Open Scope R_scope.

(* The squared radius of a row as a squared norm. Row i of a list xs is
   read as the joint vector gaussian_row_pair n i xs = (x_i, z_i), with
   x_i of S n coordinates. gaussian_row_first_norm_squared: |x_i|^2 is the
   sum of the squares of the first S n coordinates of row i, by
   vector_of_list_sum_squares. So the maximum radius of the rows is at
   least every |x_i|^2 and equal to one of them
   (gaussian_interleaved_maximum_norm_characterization). The norm of a
   vector is the Euclidean norm. *)

Lemma vector_of_list_sum_squares n xs :
  length xs=S n -> `|vector_of_list n xs|%R^2 = gaussian_sum_squares xs.
Proof.
  revert xs; induction n as [|n IH]; intros xs HL.
  - destruct xs as [|a xs]; [discriminate|]; destruct xs; [|discriminate].
    change (Rabs a ^2 = a*a+0).
    destruct (Rcase_abs a); [rewrite Rabs_left|rewrite Rabs_right]; nra.
  - destruct xs as [|a xs]; [discriminate|].
    change (sqrt(Rabs a^2+`|vector_of_list n xs|%R^2)^2 = a*a+gaussian_sum_squares xs).
    rewrite pow2_sqrt by nra.
    rewrite IH by (simpl in HL; lia).
    destruct (Rcase_abs a); [rewrite Rabs_left|rewrite Rabs_right]; nra.
Qed.

Theorem gaussian_row_first_norm_squared n N i xs :
  length xs=(N*(S n+S(goe_vector_index n)))%nat -> (i<N)%nat ->
  `|fst (gaussian_row_pair n i xs)|%R^2 =
    gaussian_sum_squares (firstn (S n) (row_chunk (S n+S(goe_vector_index n)) i xs)).
Proof.
  intros HL Hi; unfold gaussian_row_pair, joint_vector_of_list; cbn [fst].
  apply vector_of_list_sum_squares; rewrite length_firstn.
  rewrite (row_chunk_length N _ i xs HL Hi), Nat.min_l by lia; reflexivity.
Qed.

Theorem gaussian_interleaved_maximum_norm_characterization n N xs :
  length xs=(N*(S n+S(goe_vector_index n)))%nat -> (0<N)%nat ->
  (forall i, (i<N)%nat -> `|fst(gaussian_row_pair n i xs)|%R^2 <=
    gaussian_maximum_radius N (S n) (row_prefixes N (S n) (S(goe_vector_index n)) xs)) /\
  (exists i, (i<N)%nat /\
    gaussian_maximum_radius N (S n) (row_prefixes N (S n) (S(goe_vector_index n)) xs) =
    `|fst(gaussian_row_pair n i xs)|%R^2).
Proof.
  intros HL HN; split.
  - intros i Hi; rewrite (gaussian_row_first_norm_squared n N i xs HL Hi).
    apply gaussian_interleaved_maximum_ge_row; assumption.
  - destruct (gaussian_interleaved_maximum_attained N (S n) (S(goe_vector_index n)) xs HL HN)
      as [i [Hi HE]].
    exists i; split; [exact Hi|].
    rewrite (gaussian_row_first_norm_squared n N i xs HL Hi); exact HE.
Qed.
