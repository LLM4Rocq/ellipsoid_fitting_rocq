From Stdlib Require Import List Arith Lia.
From EllipsoidFitting Require Import RowCoordinateDefinitions RowCoordinates.
Import ListNotations.

Lemma row_chunk_nth {A : Type} K i j (xs : list A) (default : A) :
  (j<K)%nat -> nth j (row_chunk K i xs) default = nth (i*K+j) xs default.
Proof.
  intros Hj; unfold row_chunk; rewrite nth_firstn, nth_skipn.
  assert (H : (j <? K)=true) by (apply Nat.ltb_lt; exact Hj).
  rewrite H; reflexivity.
Qed.

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

Theorem row_chunk_replacement_same {A : Type} N K i (xs row : list A) :
  length xs=N*K -> length row=K -> (i<N)%nat ->
  row_chunk K i (row_assemble N K i (row_background N K i xs) row) = row.
Proof.
  intros HL HR Hi; apply row_chunk_assemble; try assumption.
  apply row_background_length; assumption.
Qed.

Theorem row_chunk_replacement_other {A : Type} N K i j (xs row : list A) :
  length xs=N*K -> length row=K -> (i<N)%nat -> j<>i ->
  row_chunk K j (row_assemble N K i (row_background N K i xs) row) = row_chunk K j xs.
Proof.
  intros HL HR Hi Hj.
  transitivity (row_chunk K j (row_assemble N K i (row_background N K i xs) (row_chunk K i xs))).
  - apply row_chunk_other_independent; try assumption.
    + apply row_background_length; assumption.
    + apply row_chunk_length with (N:=N); assumption.
  - rewrite row_assemble_extracted by assumption; reflexivity.
Qed.

Theorem row_background_replacement {A : Type} N K i (xs row : list A) :
  length xs=N*K -> length row=K -> (i<N)%nat ->
  row_background N K i (row_assemble N K i (row_background N K i xs) row) =
    row_background N K i xs.
Proof.
  intros HL HR Hi; apply row_background_assemble; try assumption.
  apply row_background_length; assumption.
Qed.

Theorem row_replacement_twice {A : Type} N K i (xs row row' : list A) :
  length xs=N*K -> length row=K -> (i<N)%nat ->
  row_assemble N K i (row_background N K i
    (row_assemble N K i (row_background N K i xs) row)) row' =
  row_assemble N K i (row_background N K i xs) row'.
Proof. intros; rewrite row_background_replacement by assumption; reflexivity. Qed.

Theorem row_assemble_injective {A : Type} N K i (background background' row row' : list A) :
  length background=(N-1)*K -> length background'=(N-1)*K ->
  length row=K -> length row'=K -> (i<N)%nat ->
  row_assemble N K i background row = row_assemble N K i background' row' ->
  background=background' /\ row=row'.
Proof.
  intros HB HB' HR HR' Hi HE; split.
  - apply (f_equal (row_background N K i)) in HE.
    rewrite !row_background_assemble in HE by assumption; exact HE.
  - apply (f_equal (row_chunk K i)) in HE.
    rewrite !row_chunk_assemble in HE by assumption; exact HE.
Qed.
