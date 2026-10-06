From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import Analysis.CoordinateContinuityDefinitions
  Gaussian.CoordinateTuples Analysis.CoordinatePermutationDefinitions
  Analysis.CoordinatePermutations.
Import ListNotations.
Open Scope R_scope.

(* Joint continuity of functions of a list of coordinates is preserved by
   rearranging the coordinates. finite_joint_continuous_list_map: composing
   with a map of lists that keeps lengths and coordinatewise closeness keeps
   joint continuity. Its instances are swap_adjacent, move_coordinate_last,
   and fixing a prefix or a suffix of the list. coordinates_close_forall2
   states closeness of two points as closeness of their coordinate lists. *)

Lemma coordinates_close_forall2 d e (z w : Tn d R) :
  close_n d e z w <-> List.Forall2 (fun x y => Rabs (x-y)<e)
    (coordinates_to_list d z) (coordinates_to_list d w).
Proof.
  split; intro H.
  - apply coordinate_nth_forall2.
    + rewrite !coordinates_to_list_length; reflexivity.
    + intros i Hi; rewrite coordinates_to_list_length in Hi.
      apply coordinates_close_iff; assumption.
  - apply coordinates_close_iff; intros i Hi.
    apply (coordinate_forall2_nth _ _ _ H); rewrite coordinates_to_list_length; exact Hi.
Qed.

Lemma coordinate_forall2_close_center (e : posreal) xs :
  List.Forall2 (fun x y => Rabs (x-y)<e) xs xs.
Proof.
  induction xs; constructor; auto.
  rewrite Rminus_diag_eq, Rabs_R0; [apply cond_pos|reflexivity].
Qed.

Lemma finite_joint_continuous_list_map d k (transform : list R -> list R) F :
  (forall xs, length xs = d -> length (transform xs) = k) ->
  (forall (e : posreal) xs ys, length xs = d -> length ys = d ->
    List.Forall2 (fun x y => Rabs (x-y)<e) xs ys ->
    List.Forall2 (fun x y => Rabs (x-y)<e) (transform xs) (transform ys)) ->
  finite_joint_continuous k F ->
  finite_joint_continuous d (fun xs => F (transform xs)).
Proof.
  intros HL HP HF z eps.
  pose proof (HL (coordinates_to_list d z) (coordinates_to_list_length d z)) as Hz.
  destruct (HF (coordinates_of_list k (transform (coordinates_to_list d z))) eps)
    as [delta HD].
  exists delta; intros w Hclose.
  pose proof (HL (coordinates_to_list d w) (coordinates_to_list_length d w)) as Hw.
  assert (Htrans : close_n k delta
    (coordinates_of_list k (transform (coordinates_to_list d w)))
    (coordinates_of_list k (transform (coordinates_to_list d z)))).
  { apply coordinates_close_forall2.
    rewrite !coordinates_list_roundtrip by assumption.
    apply HP; try apply coordinates_to_list_length.
    apply coordinates_close_forall2; exact Hclose. }
  specialize (HD _ Htrans).
  rewrite !coordinates_list_roundtrip in HD by assumption; exact HD.
Qed.

Lemma finite_joint_continuous_swap_adjacent d i F :
  finite_joint_continuous d F ->
  finite_joint_continuous d (fun xs => F (swap_adjacent i xs)).
Proof.
  apply finite_joint_continuous_list_map.
  - intros xs HL; rewrite swap_adjacent_length; exact HL.
  - intros e xs ys Hx Hy H; apply swap_adjacent_forall2, H.
Qed.

Lemma finite_joint_continuous_move_last d i F :
  finite_joint_continuous d F ->
  finite_joint_continuous d (fun xs => F (move_coordinate_last i xs)).
Proof.
  apply finite_joint_continuous_list_map.
  - intros xs HL; rewrite move_coordinate_last_length; exact HL.
  - intros e xs ys Hx Hy H; apply move_coordinate_last_forall2, H.
Qed.

Lemma finite_joint_continuous_prefix d prefix F :
  finite_joint_continuous (length prefix + d) F ->
  finite_joint_continuous d (fun xs => F (prefix ++ xs)).
Proof.
  apply finite_joint_continuous_list_map.
  - intros xs HL; rewrite length_app, HL; reflexivity.
  - intros e xs ys Hx Hy H; apply Forall2_app; [apply coordinate_forall2_close_center|exact H].
Qed.

Lemma finite_joint_continuous_suffix d suffix F :
  finite_joint_continuous (d + length suffix) F ->
  finite_joint_continuous d (fun xs => F (xs ++ suffix)).
Proof.
  apply finite_joint_continuous_list_map.
  - intros xs HL; rewrite length_app, HL; reflexivity.
  - intros e xs ys Hx Hy H; apply Forall2_app; [exact H|apply coordinate_forall2_close_center].
Qed.
