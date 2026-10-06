From Stdlib Require Import List Arith Lia.
From EllipsoidFitting Require Import Row.CoordinateDefinitions Row.Coordinates
  Row.Replacement Row.PrefixDefinitions.
Import ListNotations.

(* Properties of row_prefixes N d D, which keeps the first d entries of
   each of N rows of length d + D: the result has length N * d, its row i
   is the first d entries of row i of the input (row_prefixes_row_chunk),
   it can be computed one block at a time (row_prefixes_first_block), and
   it preserves a coordinatewise relation between two lists
   (row_prefixes_forall2). *)

Theorem row_prefixes_length {A : Type} N d D (xs : list A) :
  length xs=N*(d+D) -> length(row_prefixes N d D xs)=N*d.
Proof.
  revert xs; induction N as [|N IH]; intros xs HL; [reflexivity|].
  simpl; rewrite length_app, IH.
  - rewrite length_firstn, HL, Nat.min_l by lia; reflexivity.
  - rewrite length_skipn, HL; nia.
Qed.

Theorem row_prefixes_first_block {A : Type} N d D (front ignored tail : list A) :
  length front=d -> length ignored=D ->
  row_prefixes (S N) d D (front++ignored++tail) = front++row_prefixes N d D tail.
Proof.
  intros HF HI; simpl row_prefixes; rewrite firstn_app, HF, Nat.sub_diag.
  rewrite firstn_all2 by lia; simpl; rewrite app_nil_r.
  rewrite skipn_app, HF, (skipn_all2 (n:=d+D) front) by lia; simpl.
  replace (d+D-d)%nat with D by lia; rewrite skipn_app, HI, Nat.sub_diag.
  rewrite skipn_all2 by lia; reflexivity.
Qed.

Theorem row_prefixes_row_chunk {A : Type} N d D i (xs : list A) :
  length xs=N*(d+D) -> (i<N)%nat ->
  row_chunk d i (row_prefixes N d D xs) = firstn d (row_chunk (d+D) i xs).
Proof.
  revert i xs; induction N as [|N IH]; intros i xs HL Hi; [lia|].
  destruct i as [|i].
  - unfold row_chunk; simpl row_prefixes; simpl skipn.
    rewrite firstn_app, length_firstn, HL, Nat.min_l by lia.
    rewrite Nat.sub_diag; simpl; rewrite app_nil_r, !firstn_firstn.
    rewrite !Nat.min_l by lia; reflexivity.
  - simpl row_prefixes; unfold row_chunk at 1.
    rewrite Nat.mul_succ_l, skipn_app, (skipn_all2 (n:=i*d+d) (firstn d xs)).
    2:{ rewrite length_firstn; pose proof(Nat.le_min_l d (length xs)); lia. }
    rewrite length_firstn, HL, Nat.min_l by lia.
    replace (i*d+d-d)%nat with (i*d)%nat by lia; simpl.
    change (row_chunk d i (row_prefixes N d D (skipn (d+D) xs)) = firstn d (row_chunk (d+D) (S i) xs)).
    rewrite IH by (try lia; rewrite length_skipn, HL; nia).
    unfold row_chunk; rewrite skipn_skipn, Nat.mul_succ_l.
    replace (i*(d+D)+(d+D))%nat with ((d+D)+i*(d+D))%nat by lia; reflexivity.
Qed.

Theorem row_prefixes_forall2 {A B : Type} (P : A->B->Prop) N d D xs ys :
  Forall2 P xs ys -> Forall2 P (row_prefixes N d D xs) (row_prefixes N d D ys).
Proof.
  revert xs ys; induction N; intros xs ys H; simpl; [constructor|].
  apply Forall2_app.
  - clear IHN; revert xs ys H; induction d; intros xs ys H; simpl; [constructor|].
    destruct H; simpl; constructor; auto.
  - apply IHN; clear IHN; revert xs ys H; induction (d+D)%nat; intros xs ys H; simpl; [exact H|].
    destruct H; simpl; [constructor|apply IHn; exact H0].
Qed.
