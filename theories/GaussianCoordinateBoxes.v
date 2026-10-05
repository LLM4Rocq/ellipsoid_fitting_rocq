From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianCoordinateDefinitions GaussianCoordinateBasics GaussianCoordinateTopology.
From EllipsoidFitting Require Import GaussianCoordinateCompactness.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/GaussianCoordinateBoxes.v from Coquelicot to
   MathComp-Analysis.

   The original imported Coquelicot and its Compactness library for three
   names only: Tn, close_n and bounded_n. Tn and close_n now come from the
   port of GaussianCoordinateDefinitions, and bounded_n from the helper
   module GaussianCoordinateCompactness, which is imported here in addition
   to the three modules of the original. All three are copies of the
   definitions of Coquelicot.Compactness (Coquelicot 3.4.4), convertible
   with them, so every statement below is the original text, word for word,
   and says the same thing. The proofs are the original ones.

   This module loads no MathComp notation itself: the import of
   GaussianCoordinateTopology loads MathComp-Analysis but does not import
   it here. So nth is Stdlib's List.nth, ++ is Stdlib's app and the
   statements elaborate to the same terms as in the original. A module that
   imports this one after MathComp sees the same constants; it writes
   List.nth and (xs ++ ys)%list where it restates them. *)

Lemma coordinates_list_bounded (xs : list R) :
  exists R, 0 <= R /\ forall x, In x xs -> Rabs x <= R.
Proof.
  induction xs as [|x xs [R [HR Hb]]].
  - exists 0; split; [lra|intros x H; contradiction].
  - exists (Rabs x+R); split; [pose proof (Rabs_pos x); lra|].
    intros y [Hy|Hy].
    + subst y; lra.
    + specialize (Hb y Hy); pose proof (Rabs_pos x); lra.
Qed.

Lemma coordinates_close_enlarged_box d e M (z w : Tn d R) :
  (forall x, In x (coordinates_to_list d z) -> Rabs x <= M) ->
  close_n d e w z ->
  forall y, In y (coordinates_to_list d w) -> Rabs y <= M+e.
Proof.
  intros Hbox Hclose y Hy.
  apply In_nth with (d:=0) in Hy; destruct Hy as [i [Hi Hiy]].
  assert (Hid : (i<d)%nat) by (rewrite coordinates_to_list_length in Hi; exact Hi).
  pose proof (proj1 (coordinates_close_iff d e w z) Hclose i Hid) as Hnear.
  pose proof (Hbox (nth i (coordinates_to_list d z) 0)
    (nth_In (coordinates_to_list d z) 0 ltac:(rewrite coordinates_to_list_length; exact Hid))) as Hz.
  rewrite Hiy in Hnear.
  replace y with ((y-nth i (coordinates_to_list d z) 0)+nth i (coordinates_to_list d z) 0) by ring.
  pose proof (Rabs_triang (y-nth i (coordinates_to_list d z) 0)
    (nth i (coordinates_to_list d z) 0)); lra.
Qed.

Theorem coordinates_box_neighborhood d (z : Tn d R) :
  exists R, 0 <= R /\
  (forall x, In x (coordinates_to_list d z) -> Rabs x <= R) /\
  forall w, close_n d 1 w z -> forall x, In x (coordinates_to_list d w) -> Rabs x <= R.
Proof.
  destruct (coordinates_list_bounded (coordinates_to_list d z)) as [R [HR Hb]].
  exists (R+1); split; [lra|]; split.
  - intros x Hx; specialize (Hb x Hx); lra.
  - intros w Hw; exact (coordinates_close_enlarged_box d 1 R z w Hb Hw).
Qed.

Lemma coordinates_bounded_lists_iff d a b xs :
  length xs = d ->
  (bounded_n d (coordinates_of_list d (repeat a d))
    (coordinates_of_list d (repeat b d)) (coordinates_of_list d xs) <->
   forall x, In x xs -> a <= x <= b).
Proof.
  intro Hlen; revert xs Hlen; induction d as [|d IH]; intros xs Hlen.
  - destruct xs; [simpl; tauto|discriminate].
  - destruct xs as [|x xs]; [discriminate|].
    simpl in Hlen |- *; rewrite IH by lia.
    split.
    + intros [Hx Hs] y [Hy|Hy]; [subst; exact Hx|apply Hs; exact Hy].
    + intro H; split.
      * apply H; left; reflexivity.
      * intros y Hy; apply H; right; exact Hy.
Qed.

Lemma coordinates_close_snoc_iff d e xs ys x y :
  length xs = d -> length ys = d ->
  (close_n (S d) e (coordinates_of_list (S d) (xs++[x]))
    (coordinates_of_list (S d) (ys++[y])) <->
   close_n d e (coordinates_of_list d xs) (coordinates_of_list d ys) /\ Rabs (x-y) < e).
Proof.
  revert xs ys; induction d as [|d IH]; intros xs ys Hx Hy.
  - destruct xs,ys; try discriminate; simpl; tauto.
  - destruct xs as [|u xs],ys as [|v ys]; try discriminate.
    simpl in Hx,Hy.
    change ((Rabs (u-v)<e /\ close_n (S d) e
      (coordinates_of_list (S d) (xs++[x])) (coordinates_of_list (S d) (ys++[y]))) <->
      (Rabs (u-v)<e /\ close_n d e (coordinates_of_list d xs) (coordinates_of_list d ys)) /\ Rabs (x-y)<e).
    rewrite IH by lia; tauto.
Qed.

Lemma coordinates_bounded_snoc_iff d (a b : Tn d R) xs l u x :
  length xs = d ->
  (bounded_n (S d)
    (coordinates_of_list (S d) (coordinates_to_list d a++[l]))
    (coordinates_of_list (S d) (coordinates_to_list d b++[u]))
    (coordinates_of_list (S d) (xs++[x])) <->
   bounded_n d a b (coordinates_of_list d xs) /\ l <= x <= u).
Proof.
  revert a b xs; induction d as [|d IH]; intros a b xs Hlen.
  - destruct a,b,xs; try discriminate; simpl; tauto.
  - destruct a as [a aa],b as [b bb],xs as [|z xs]; try discriminate.
    simpl in Hlen.
    change ((a<=z<=b /\ bounded_n (S d)
      (coordinates_of_list (S d) (coordinates_to_list d aa++[l]))
      (coordinates_of_list (S d) (coordinates_to_list d bb++[u]))
      (coordinates_of_list (S d) (xs++[x]))) <->
      (a<=z<=b /\ bounded_n d aa bb (coordinates_of_list d xs)) /\ l<=x<=u).
    rewrite IH by lia; tauto.
Qed.
