From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CoordinateContinuityDefinitions
  Gaussian.CoordinateTuples Analysis.CoordinateTopology.
From EllipsoidFitting Require Import Analysis.BoxCompactness.
Import ListNotations.
Open Scope R_scope.

(* Bounds on the coordinates of points of R^d near a given point, where a
   point is a nested tuple Tn d R and close_n d e w z says that every
   coordinate of w is within e of that of z.
   - coordinates_list_bounded: the entries of a list are bounded.
   - coordinates_close_enlarged_box: if the coordinates of z are bounded by
     M in absolute value and close_n d e w z, those of w are bounded by
     M + e.
   - coordinates_box_neighborhood: one bound holds for z and for every w
     with close_n d 1 w z. *)

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
