From Stdlib Require Import Reals List Permutation Lia.
From EllipsoidFitting Require Import Analysis.CoordinatePermutationDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Properties of replace_coordinate. It preserves the length; the lemmas
   on nth give the coordinates of replace_coordinate i t xs, and
   replace_coordinate_twice and replace_coordinate_self simplify a repeated
   or a trivial replacement. The Forall2 lemmas (coordinate_forall2_nth,
   coordinate_nth_forall2) relate a coordinatewise relation between two
   lists to the relation between their coordinates. *)

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
