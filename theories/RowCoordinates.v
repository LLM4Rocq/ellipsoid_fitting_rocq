From Stdlib Require Import List Arith Lia.
From EllipsoidFitting Require Import RowCoordinateDefinitions.
Import ListNotations.

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

Theorem row_background_length {A : Type} N K i (xs : list A) :
  length xs = N*K -> (i < N)%nat -> length (row_background N K i xs) = (N-1)*K.
Proof.
  intros Hlen Hi; unfold row_background; rewrite length_app, length_skipn, length_firstn, Hlen.
  pose proof (row_index_lengths N K i Hi) as [Ha Hb].
  rewrite Nat.min_l by lia; nia.
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

Theorem row_assemble_length {A : Type} N K i (background row : list A) :
  length background = (N-1)*K -> length row = K -> (i < N)%nat ->
  length (row_assemble N K i background row) = N*K.
Proof.
  intros HB HR Hi; unfold row_assemble.
  rewrite !length_app, length_skipn, length_firstn, HB, HR.
  pose proof (row_index_lengths N K i Hi) as [Ha Hb].
  rewrite Nat.min_l by lia; lia.
Qed.

Lemma row_before_length {A : Type} N K i (background : list A) :
  length background = (N-1)*K -> (i < N)%nat ->
  length (skipn ((N-1-i)*K) background) = i*K.
Proof.
  intros HB Hi; rewrite length_skipn, HB.
  pose proof (row_index_lengths N K i Hi); lia.
Qed.

Lemma row_after_length {A : Type} N K i (background : list A) :
  length background = (N-1)*K -> (i < N)%nat ->
  length (firstn ((N-1-i)*K) background) = (N-1-i)*K.
Proof.
  intros HB Hi; rewrite length_firstn, HB; apply Nat.min_l.
  pose proof (row_index_lengths N K i Hi); lia.
Qed.

Lemma row_prefix_middle {A : Type} K i (before row after : list A) :
  length before = i*K -> firstn (i*K) (before++row++after) = before.
Proof.
  intros HB; rewrite firstn_app, <- HB, firstn_all, Nat.sub_diag; simpl; apply app_nil_r.
Qed.

Lemma row_chunk_middle {A : Type} K i (before row after : list A) :
  length before = i*K -> length row = K ->
  row_chunk K i (before++row++after) = row.
Proof.
  intros HB HR; unfold row_chunk; rewrite skipn_app, <- HB, skipn_all, Nat.sub_diag.
  simpl; rewrite firstn_app, <- HR, firstn_all, Nat.sub_diag; simpl; apply app_nil_r.
Qed.

Lemma row_suffix_middle {A : Type} K i (before row after : list A) :
  length before = i*K -> length row = K ->
  skipn ((S i)*K) (before++row++after) = after.
Proof.
  intros HB HR; replace ((S i)*K) with (length before + length row) by nia.
  rewrite skipn_app, skipn_all2 by lia.
  replace (length before+length row-length before) with (length row) by lia.
  simpl; rewrite skipn_app, skipn_all, Nat.sub_diag; reflexivity.
Qed.

Theorem row_chunk_assemble {A : Type} N K i (background row : list A) :
  length background = (N-1)*K -> length row = K -> (i < N)%nat ->
  row_chunk K i (row_assemble N K i background row) = row.
Proof.
  intros HB HR Hi; unfold row_assemble; apply row_chunk_middle; [|exact HR].
  apply row_before_length; assumption.
Qed.

Theorem row_background_assemble {A : Type} N K i (background row : list A) :
  length background = (N-1)*K -> length row = K -> (i < N)%nat ->
  row_background N K i (row_assemble N K i background row) = background.
Proof.
  intros HB HR Hi; unfold row_background, row_assemble.
  rewrite row_prefix_middle by (apply row_before_length; assumption).
  rewrite row_suffix_middle by (try assumption; apply row_before_length; assumption).
  apply firstn_skipn.
Qed.

Lemma row_three_parts {A : Type} K i (xs : list A) :
  firstn (i*K) xs ++ row_chunk K i xs ++ skipn ((S i)*K) xs = xs.
Proof.
  unfold row_chunk; replace ((S i)*K) with (K+i*K) by nia.
  rewrite <- skipn_skipn, firstn_skipn, firstn_skipn; reflexivity.
Qed.

Theorem row_assemble_extracted {A : Type} N K i (xs : list A) :
  length xs = N*K -> (i < N)%nat ->
  row_assemble N K i (row_background N K i xs) (row_chunk K i xs) = xs.
Proof.
  intros HL Hi.
  assert (HA : length (skipn ((S i)*K) xs) = (N-1-i)*K).
  { rewrite length_skipn, HL; pose proof (row_index_lengths N K i Hi); nia. }
  unfold row_assemble, row_background.
  rewrite skipn_app, firstn_app, <- HA, skipn_all, firstn_all, Nat.sub_diag.
  simpl; rewrite app_nil_r; apply row_three_parts.
Qed.
