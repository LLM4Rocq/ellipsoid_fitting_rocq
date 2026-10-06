From Stdlib Require Import List Arith Lia.
From EllipsoidFitting Require Import Row.CoordinateDefinitions.
Import ListNotations.

(* Lengths and rows of lists of N rows of length K. row_chunk_length: each
   row has length K. row_assemble_rotation: row_assemble is a rotation of
   background ++ row. row_chunk_assemble: row i of
   row_assemble N K i background row is row. row_three_parts splits a list
   into the rows before row i, row i, and the rows after it. *)

Lemma row_index_lengths N K i : (i < N)%nat ->
  N*K = i*K + K + (N-1-i)*K /\
  (N-1)*K = (N-1-i)*K + i*K.
Proof. intros Hi; assert (H : N = i+1+(N-1-i)) by lia; nia. Qed.

Theorem row_chunk_length {A : Type} N K i (xs : list A) :
  length xs = N*K -> (i < N)%nat -> length (row_chunk K i xs) = K.
Proof.
  intros Hlen Hi; unfold row_chunk; rewrite length_firstn, length_skipn, Hlen.
  apply Nat.min_l; pose proof (row_index_lengths N K i Hi); lia.
Qed.

Theorem row_assemble_rotation {A : Type} N K i (background row : list A) :
  length background = (N-1)*K -> (i < N)%nat ->
  row_assemble N K i background row =
    skipn ((N-1-i)*K) (background++row) ++ firstn ((N-1-i)*K) (background++row).
Proof.
  intros Hlen Hi; unfold row_assemble.
  rewrite skipn_app, firstn_app.
  assert (Hsub : (N-1-i)*K-length background = 0).
  { rewrite Hlen; pose proof (row_index_lengths N K i Hi); lia. }
  rewrite Hsub; simpl; rewrite app_nil_r, app_assoc; reflexivity.
Qed.

Lemma row_before_length {A : Type} N K i (background : list A) :
  length background = (N-1)*K -> (i < N)%nat ->
  length (skipn ((N-1-i)*K) background) = i*K.
Proof.
  intros HB Hi; rewrite length_skipn, HB.
  pose proof (row_index_lengths N K i Hi); lia.
Qed.

Lemma row_chunk_middle {A : Type} K i (before row after : list A) :
  length before = i*K -> length row = K ->
  row_chunk K i (before++row++after) = row.
Proof.
  intros HB HR; unfold row_chunk; rewrite skipn_app, <- HB, skipn_all, Nat.sub_diag.
  simpl; rewrite firstn_app, <- HR, firstn_all, Nat.sub_diag; simpl; apply app_nil_r.
Qed.

Theorem row_chunk_assemble {A : Type} N K i (background row : list A) :
  length background = (N-1)*K -> length row = K -> (i < N)%nat ->
  row_chunk K i (row_assemble N K i background row) = row.
Proof.
  intros HB HR Hi; unfold row_assemble; apply row_chunk_middle; [|exact HR].
  apply row_before_length; assumption.
Qed.

Lemma row_three_parts {A : Type} K i (xs : list A) :
  firstn (i*K) xs ++ row_chunk K i xs ++ skipn ((S i)*K) xs = xs.
Proof.
  unfold row_chunk; replace ((S i)*K) with (K+i*K) by nia.
  rewrite <- skipn_skipn, firstn_skipn, firstn_skipn; reflexivity.
Qed.
