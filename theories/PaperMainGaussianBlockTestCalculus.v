(* First and second coordinate blocks for smooth Gaussian product tests. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2
  GaussianCoordinateDefinitions GaussianCoordinateBasics GaussianCoordinateTopology
  GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations
  GaussianCoordinateDerivativeDefinitions GaussianCovarianceSums.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gaussian_block_lengths d (xs : list R) :
  List.length xs = Nat.add d d ->
  List.length (List.firstn d xs) = d /\ List.length (List.skipn d xs) = d.
Proof.
intros Hxs; rewrite firstn_length length_skipn Hxs; split; lia.
Qed.

Lemma paper_main_gaussian_firstn_replace d a t xs :
  List.firstn d (replace_coordinate a t xs) =
  if Nat.ltb a d then replace_coordinate a t (List.firstn d xs) else List.firstn d xs.
Proof.
revert a xs; induction d as [|d IH]; intros [|a] [|x xs]; simpl; try reflexivity.
- destruct (Nat.ltb (S a) (S d)); reflexivity.
- change (Nat.ltb (S a) (S d)) with (Nat.ltb a d).
  rewrite IH; destruct (Nat.ltb a d); reflexivity.
Qed.

Lemma paper_main_gaussian_skipn_replace d a t xs :
  List.skipn d (replace_coordinate a t xs) =
  if Nat.ltb a d then List.skipn d xs else
    replace_coordinate (Nat.sub a d) t (List.skipn d xs).
Proof.
revert a xs; induction d as [|d IH]; intros [|a] [|x xs]; simpl; try reflexivity.
- destruct (Nat.ltb (S a) (S d)); [reflexivity|].
  destruct (Nat.sub a d); reflexivity.
- change (Nat.ltb (S a) (S d)) with (Nat.ltb a d); apply IH.
Qed.

Lemma paper_main_gaussian_left_continuous d f :
  finite_joint_continuous d f ->
  finite_joint_continuous (Nat.add d d) (fun zs => f (List.firstn d zs)).
Proof.
intros Hf z eps.
set (zs := coordinates_to_list (Nat.add d d) z).
assert (Hzs : List.length zs = Nat.add d d) by apply coordinates_to_list_length.
pose proof (proj1 (paper_main_gaussian_block_lengths d zs Hzs)) as Hlenz.
destruct (Hf (coordinates_of_list d (List.firstn d zs)) eps) as [delta Hd].
exists delta; intros w Hw.
set (ws := coordinates_to_list (Nat.add d d) w).
assert (Hws : List.length ws = Nat.add d d) by apply coordinates_to_list_length.
pose proof (proj1 (paper_main_gaussian_block_lengths d ws Hws)) as Hlenw.
specialize (Hd (coordinates_of_list d (List.firstn d ws))).
rewrite (coordinates_list_roundtrip d (List.firstn d ws) Hlenw)
  (coordinates_list_roundtrip d (List.firstn d zs) Hlenz) in Hd.
apply Hd; apply (proj2 (coordinates_close_lists d delta _ _ Hlenw Hlenz)).
intros i Hi; rewrite (nth_firstn_lt ws d i Hi) (nth_firstn_lt zs d i Hi).
exact (proj1 (coordinates_close_iff (Nat.add d d) delta w z) Hw i ltac:(lia)).
Qed.

Lemma paper_main_gaussian_right_continuous d f :
  finite_joint_continuous d f ->
  finite_joint_continuous (Nat.add d d) (fun zs => f (List.skipn d zs)).
Proof.
intros Hf z eps.
set (zs := coordinates_to_list (Nat.add d d) z).
assert (Hzs : List.length zs = Nat.add d d) by apply coordinates_to_list_length.
pose proof (proj2 (paper_main_gaussian_block_lengths d zs Hzs)) as Hlenz.
destruct (Hf (coordinates_of_list d (List.skipn d zs)) eps) as [delta Hd].
exists delta; intros w Hw.
set (ws := coordinates_to_list (Nat.add d d) w).
assert (Hws : List.length ws = Nat.add d d) by apply coordinates_to_list_length.
pose proof (proj2 (paper_main_gaussian_block_lengths d ws Hws)) as Hlenw.
specialize (Hd (coordinates_of_list d (List.skipn d ws))).
rewrite (coordinates_list_roundtrip d (List.skipn d ws) Hlenw)
  (coordinates_list_roundtrip d (List.skipn d zs) Hlenz) in Hd.
apply Hd; apply (proj2 (coordinates_close_lists d delta _ _ Hlenw Hlenz)).
intros i Hi; rewrite !nth_skipn_add.
exact (proj1 (coordinates_close_iff (Nat.add d d) delta w z) Hw (Nat.add d i) ltac:(lia)).
Qed.

Lemma paper_main_gaussian_left_derivative d a f Df :
  Nat.lt a d -> finite_coordinate_derivative d a f Df ->
  finite_coordinate_derivative (Nat.add d d) a
    (fun zs => f (List.firstn d zs)) (fun zs => Df (List.firstn d zs)).
Proof.
intros Ha HD zs Hzs.
pose proof (HD (List.firstn d zs) (proj1 (paper_main_gaussian_block_lengths d zs Hzs))) as H.
rewrite (nth_firstn_lt zs d a Ha) in H.
apply (is_derive_ext (fun t => f (replace_coordinate a t (List.firstn d zs)))); [|exact H].
intros t; rewrite paper_main_gaussian_firstn_replace.
assert (E : Nat.ltb a d = true) by (apply Nat.ltb_lt; exact Ha).
rewrite E; reflexivity.
Qed.

Lemma paper_main_gaussian_left_derivative_zero d a f :
  Nat.le d a ->
  finite_coordinate_derivative (Nat.add d d) a
    (fun zs => f (List.firstn d zs)) (fun _ => 0).
Proof.
intros Ha zs Hzs.
apply (is_derive_ext (fun _ => f (List.firstn d zs))); [|apply is_derive_const].
intros t; rewrite paper_main_gaussian_firstn_replace.
assert (E : Nat.ltb a d = false) by (apply Nat.ltb_ge; exact Ha).
rewrite E; reflexivity.
Qed.

Lemma paper_main_gaussian_right_derivative d a f Df :
  Nat.le d a -> finite_coordinate_derivative d (Nat.sub a d) f Df ->
  finite_coordinate_derivative (Nat.add d d) a
    (fun zs => f (List.skipn d zs)) (fun zs => Df (List.skipn d zs)).
Proof.
intros Ha HD zs Hzs.
pose proof (HD (List.skipn d zs) (proj2 (paper_main_gaussian_block_lengths d zs Hzs))) as H.
rewrite nth_skipn_add in H.
replace (Nat.add d (Nat.sub a d)) with a in H by lia.
apply (is_derive_ext (fun t => f (replace_coordinate (Nat.sub a d) t (List.skipn d zs)))); [|exact H].
intros t; rewrite paper_main_gaussian_skipn_replace.
assert (E : Nat.ltb a d = false) by (apply Nat.ltb_ge; exact Ha).
rewrite E; reflexivity.
Qed.

Lemma paper_main_gaussian_right_derivative_zero d a f :
  Nat.lt a d ->
  finite_coordinate_derivative (Nat.add d d) a
    (fun zs => f (List.skipn d zs)) (fun _ => 0).
Proof.
intros Ha zs Hzs.
apply (is_derive_ext (fun _ => f (List.skipn d zs))); [|apply is_derive_const].
intros t; rewrite paper_main_gaussian_skipn_replace.
assert (E : Nat.ltb a d = true) by (apply Nat.ltb_lt; exact Ha).
rewrite E; reflexivity.
Qed.
