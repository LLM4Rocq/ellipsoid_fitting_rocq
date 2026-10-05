From Stdlib Require Import List Arith Lia.
From EllipsoidFitting Require Import RowCoordinateDefinitions RowCoordinates.
Import ListNotations.

Lemma row_chunk_before_middle {A : Type} K i j (before row after : list A) :
  length before = i*K -> (j<i)%nat ->
  row_chunk K j (before++row++after) = row_chunk K j before.
Proof.
  intros HB Hj; unfold row_chunk; rewrite skipn_app, firstn_app.
  assert (Hsub : K-length(skipn (j*K) before)=0).
  { rewrite length_skipn, HB; nia. }
  rewrite Hsub; simpl; apply app_nil_r.
Qed.

Lemma row_chunk_after_middle {A : Type} K i j (before row after : list A) :
  length before = i*K -> length row = K -> (i<j)%nat ->
  row_chunk K j (before++row++after) = row_chunk K (j-i-1) after.
Proof.
  intros HB HR Hj; unfold row_chunk; rewrite skipn_app.
  rewrite (skipn_all2 (n:=j*K) before) by nia; simpl.
  rewrite skipn_app, (skipn_all2 (n:=j*K-length before) row) by nia; simpl.
  replace (j*K-length before-length row) with ((j-i-1)*K) by nia; reflexivity.
Qed.

Theorem row_chunk_other_independent {A : Type} N K i j (background row row' : list A) :
  length background = (N-1)*K -> length row=K -> length row'=K ->
  (i<N)%nat -> j<>i ->
  row_chunk K j (row_assemble N K i background row) =
  row_chunk K j (row_assemble N K i background row').
Proof.
  intros HB HR HR' Hi Hne; unfold row_assemble.
  destruct (Nat.lt_trichotomy j i) as [Hlt|[Heq|Hgt]]; [|contradiction|].
  - rewrite !row_chunk_before_middle with (i:=i) by (try assumption; apply row_before_length; assumption).
    reflexivity.
  - rewrite !row_chunk_after_middle with (i:=i) by (try assumption; apply row_before_length; assumption).
    reflexivity.
Qed.
