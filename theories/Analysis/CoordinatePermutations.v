From Stdlib Require Import Reals List Permutation Lia.
From EllipsoidFitting Require Import Analysis.CoordinatePermutationDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Properties of swap_adjacent, replace_coordinate and move_coordinate_last.
   They preserve the length; swap_adjacent and move_coordinate_last are
   permutations of the list. The lemmas on nth give the coordinates of the
   result, and move_coordinate_last_prefix writes move_coordinate_last i xs
   as the coordinates before i, then those after i, then coordinate i. The
   Forall2 lemmas carry a coordinatewise relation between two lists through
   these operations. *)

Lemma swap_adjacent_length i xs : length (swap_adjacent i xs) = length xs.
Proof.
  revert xs; induction i; intros [|x [|y zs]]; simpl; auto.
Qed.

Lemma swap_adjacent_permutation i xs : Permutation (swap_adjacent i xs) xs.
Proof.
  revert xs; induction i; intros [|x [|y zs]]; simpl; try apply Permutation_refl.
  - apply perm_swap.
  - apply perm_skip, IHi.
  - apply perm_skip, IHi.
Qed.

Lemma replace_coordinate_length i value xs :
  length (replace_coordinate i value xs) = length xs.
Proof. revert xs; induction i; intros [|x xs]; simpl; auto. Qed.

Lemma replace_coordinate_nth_same i value xs :
  (i < length xs)%nat -> nth i (replace_coordinate i value xs) 0 = value.
Proof.
  revert xs; induction i; intros [|x xs] H; simpl in *; try lia; auto.
  apply IHi; lia.
Qed.

Lemma replace_coordinate_nth_other i j value xs :
  i <> j -> nth j (replace_coordinate i value xs) 0 = nth j xs 0.
Proof.
  revert j xs; induction i; intros j [|x xs] H; destruct j; simpl in *; try congruence.
  apply IHi; congruence.
Qed.

Lemma replace_coordinate_twice i x y xs :
  replace_coordinate i x (replace_coordinate i y xs) = replace_coordinate i x xs.
Proof. revert xs; induction i; intros [|z xs]; simpl; auto; rewrite IHi; reflexivity. Qed.

Lemma replace_coordinate_self i xs : replace_coordinate i (nth i xs 0) xs = xs.
Proof. revert xs; induction i; intros [|x xs]; simpl; auto; rewrite IHi; reflexivity. Qed.

Lemma move_coordinate_last_length i xs :
  length (move_coordinate_last i xs) = length xs.
Proof.
  revert xs; induction i; intros [|x xs]; simpl; try reflexivity.
  - rewrite length_app; simpl; lia.
  - rewrite IHi; reflexivity.
Qed.

Lemma move_coordinate_last_permutation i xs :
  Permutation (move_coordinate_last i xs) xs.
Proof.
  revert xs; induction i; intros [|x xs]; simpl; try apply Permutation_refl.
  - change (Permutation (xs ++ [x]) ([x] ++ xs)); apply Permutation_app_comm.
  - apply perm_skip, IHi.
Qed.

Lemma coordinate_forall2_nth (rel : R -> R -> Prop) xs ys :
  List.Forall2 rel xs ys -> forall i, (i < length xs)%nat ->
    rel (nth i xs 0) (nth i ys 0).
Proof.
  intros H; induction H; intros [|i] Hi; simpl in *; try lia; auto.
  apply IHForall2; lia.
Qed.

Lemma coordinate_nth_forall2 (rel : R -> R -> Prop) xs ys :
  length xs = length ys ->
  (forall i, (i < length xs)%nat -> rel (nth i xs 0) (nth i ys 0)) ->
  List.Forall2 rel xs ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] HL H; simpl in *; try discriminate.
  - constructor.
  - constructor.
    + apply (H O); lia.
    + apply IH; [lia|]. intros i Hi; apply (H (S i)); lia.
Qed.

Lemma swap_adjacent_forall2 (rel : R -> R -> Prop) i xs ys :
  List.Forall2 rel xs ys ->
  List.Forall2 rel (swap_adjacent i xs) (swap_adjacent i ys).
Proof.
  revert xs ys; induction i; intros xs ys H.
  - destruct H as [|x y xs ys Hxy Htail]; [constructor|].
    destruct Htail as [|x' y' xs ys Hxy' Htail]; simpl; repeat constructor; assumption.
  - destruct H as [|x y xs ys Hxy Htail]; simpl; constructor; auto.
Qed.

Lemma move_coordinate_last_forall2 (rel : R -> R -> Prop) i xs ys :
  List.Forall2 rel xs ys ->
  List.Forall2 rel (move_coordinate_last i xs) (move_coordinate_last i ys).
Proof.
  revert xs ys; induction i; intros xs ys H;
    destruct H; simpl; try constructor; auto.
  apply Forall2_app; [assumption|repeat constructor; assumption].
Qed.
