From Stdlib Require Import Reals List Permutation Lia.
From EllipsoidFitting Require Import GaussianCoordinatePermutationDefinitions.
Import ListNotations.
Open Scope R_scope.

Lemma swap_adjacent_length i xs : length (swap_adjacent i xs) = length xs.
Proof.
  revert xs; induction i; intros [|x [|y zs]]; simpl; auto.
Qed.

Lemma swap_adjacent_involution i xs :
  swap_adjacent i (swap_adjacent i xs) = xs.
Proof.
  revert xs; induction i; intros [|x [|y zs]]; simpl; auto.
  all: rewrite IHi; reflexivity.
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

Lemma replace_coordinate_out_of_range i x xs :
  (length xs <= i)%nat -> replace_coordinate i x xs = xs.
Proof.
  revert xs; induction i; intros [|y xs] H; simpl in *; try reflexivity; try lia.
  rewrite IHi; [reflexivity|lia].
Qed.

Lemma replace_coordinate_commute i j x y xs :
  i <> j -> replace_coordinate i x (replace_coordinate j y xs) =
    replace_coordinate j y (replace_coordinate i x xs).
Proof.
  revert j xs; induction i; intros [|j] [|z xs] H; simpl; try reflexivity; try congruence.
  rewrite IHi; [reflexivity|congruence].
Qed.

Lemma coordinate_prefix_decomposition i xs :
  (i < length xs)%nat ->
  xs = firstn i xs ++ nth i xs 0 :: skipn (S i) xs.
Proof.
  revert xs; induction i; intros [|x xs] H; simpl in *; try lia; try reflexivity.
  f_equal; apply IHi; lia.
Qed.

Lemma replace_coordinate_prefix i value xs :
  (i < length xs)%nat -> replace_coordinate i value xs =
    firstn i xs ++ value :: skipn (S i) xs.
Proof.
  revert xs; induction i; intros [|x xs] H; simpl in *; try lia; try reflexivity.
  f_equal; apply IHi; lia.
Qed.

Lemma swap_adjacent_prefix i xs :
  (S i < length xs)%nat -> swap_adjacent i xs =
    firstn i xs ++ nth (S i) xs 0 :: nth i xs 0 :: skipn (S (S i)) xs.
Proof.
  revert xs; induction i; intros [|x [|y xs]] H; simpl in *; try lia; try reflexivity.
  f_equal; apply (IHi (y :: xs)); simpl; lia.
Qed.

Lemma swap_adjacent_nth_left i xs :
  (S i < length xs)%nat -> nth i (swap_adjacent i xs) 0 = nth (S i) xs 0.
Proof.
  revert xs; induction i; intros [|x [|y xs]] H; simpl in *; try lia; try reflexivity.
  apply (IHi (y :: xs)); simpl; lia.
Qed.

Lemma swap_adjacent_nth_right i xs :
  (S i < length xs)%nat -> nth (S i) (swap_adjacent i xs) 0 = nth i xs 0.
Proof.
  revert xs; induction i; intros [|x [|y xs]] H; simpl in *; try lia; try reflexivity.
  apply (IHi (y :: xs)); simpl; lia.
Qed.

Lemma swap_adjacent_nth_other i j xs :
  j <> i -> j <> S i -> nth j (swap_adjacent i xs) 0 = nth j xs 0.
Proof.
  revert j xs; induction i; intros j [|x [|y xs]] H H'; simpl; try reflexivity.
  - destruct j as [|[|j]]; simpl; congruence.
  - destruct j; simpl; [reflexivity|apply IHi; congruence].
  - destruct j; simpl; [reflexivity|apply IHi; congruence].
Qed.

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

Lemma move_coordinate_last_prefix i xs :
  (i < length xs)%nat -> move_coordinate_last i xs =
    firstn i xs ++ skipn (S i) xs ++ [nth i xs 0].
Proof.
  revert xs; induction i; intros [|x xs] H; simpl in *; try lia; try reflexivity.
  f_equal; apply IHi; lia.
Qed.

Lemma move_coordinate_last_out_of_range i xs :
  (length xs <= i)%nat -> move_coordinate_last i xs = xs.
Proof.
  revert xs; induction i; intros [|x xs] H; simpl in *; try lia; try reflexivity.
  rewrite IHi; [reflexivity|lia].
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

Lemma replace_coordinate_forall2 (rel : R -> R -> Prop) i x y xs ys :
  rel x y -> List.Forall2 rel xs ys ->
  List.Forall2 rel (replace_coordinate i x xs) (replace_coordinate i y ys).
Proof.
  intros Hxy; revert xs ys; induction i; intros xs ys H;
    destruct H; simpl; constructor; auto.
Qed.

Lemma move_coordinate_last_forall2 (rel : R -> R -> Prop) i xs ys :
  List.Forall2 rel xs ys ->
  List.Forall2 rel (move_coordinate_last i xs) (move_coordinate_last i ys).
Proof.
  revert xs ys; induction i; intros xs ys H;
    destruct H; simpl; try constructor; auto.
  apply Forall2_app; [assumption|repeat constructor; assumption].
Qed.

Lemma move_coordinate_last_selected i xs :
  (i < length xs)%nat -> last (move_coordinate_last i xs) 0 = nth i xs 0.
Proof.
  intro Hi; rewrite move_coordinate_last_prefix by exact Hi.
  rewrite app_assoc; apply last_last.
Qed.

Lemma move_coordinate_last_nth_selected i xs :
  (i < length xs)%nat ->
  nth (length xs - 1) (move_coordinate_last i xs) 0 = nth i xs 0.
Proof.
  intro Hi; rewrite move_coordinate_last_prefix by exact Hi.
  rewrite app_assoc.
  replace (length xs - 1)%nat with (length (firstn i xs ++ skipn (S i) xs)).
  - apply nth_middle.
  - rewrite length_app, length_firstn, length_skipn, Nat.min_l by lia; lia.
Qed.

Lemma move_coordinate_last_replaced i value xs :
  (i < length xs)%nat -> move_coordinate_last i (replace_coordinate i value xs) =
    firstn i xs ++ skipn (S i) xs ++ [value].
Proof.
  revert xs; induction i; intros [|x xs] Hi; simpl in *; try lia; try reflexivity.
  f_equal; apply IHi; lia.
Qed.

Lemma swap_adjacent_replace_left i value xs :
  (S i < length xs)%nat ->
  swap_adjacent i (replace_coordinate i value xs) =
    replace_coordinate (S i) value (swap_adjacent i xs).
Proof.
  revert xs; induction i; intros [|x [|y xs]] Hi; simpl in *; try lia; try reflexivity.
  f_equal; apply (IHi (y :: xs)); simpl; lia.
Qed.

Lemma swap_adjacent_replace_right i value xs :
  (S i < length xs)%nat ->
  swap_adjacent i (replace_coordinate (S i) value xs) =
    replace_coordinate i value (swap_adjacent i xs).
Proof.
  revert xs; induction i; intros [|x [|y xs]] Hi; simpl in *; try lia; try reflexivity.
  f_equal; apply (IHi (y :: xs)); simpl; lia.
Qed.
