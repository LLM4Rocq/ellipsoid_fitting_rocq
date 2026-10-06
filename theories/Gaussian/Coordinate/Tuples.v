From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CoordinateContinuityDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Points of R ^ d as the nested pairs Tn d R of
   Analysis.CoordinateContinuityDefinitions, and as lists. coordinates_to_list and
   coordinates_of_list are inverse to each other between Tn d R and the
   lists of length d (coordinates_roundtrip, coordinates_list_roundtrip).
   The coordinatewise closeness close_n d e is reflexive for e > 0,
   symmetric, monotone in e and satisfies the triangle inequality;
   coordinates_close_iff and coordinates_close_lists state it coordinate by
   coordinate on lists.

   This module loads no MathComp library, so nth is Stdlib's List.nth
   (MathComp's seq.nth takes its arguments in another order) and (i<d)%nat
   is Peano's lt, which a module that imports MathComp writes
   (i < d)%coq_nat. *)

Lemma coordinates_to_list_length d z : length (coordinates_to_list d z) = d.
Proof. induction d; [reflexivity|destruct z; simpl; rewrite IHd; reflexivity]. Qed.
Lemma coordinates_roundtrip d (z : Tn d R) :
  coordinates_of_list d (coordinates_to_list d z) = z.
Proof.
  induction d; [destruct z; reflexivity|].
  destruct z as [x z]; simpl; rewrite IHd; reflexivity.
Qed.
Lemma coordinates_list_roundtrip d xs :
  length xs = d -> coordinates_to_list d (coordinates_of_list d xs) = xs.
Proof.
  revert xs; induction d; intros xs H.
  - destruct xs; [reflexivity|discriminate].
  - destruct xs as [|x xs]; [discriminate|].
    simpl in *; rewrite IHd; [reflexivity|lia].
Qed.

Lemma coordinates_close_center d e (z : Tn d R) :
  0 < e -> close_n d e z z.
Proof.
  induction d; [exact (fun _ => I)|].
  destruct z as [x z]; simpl; intro He; split; [|apply IHd; exact He].
  rewrite Rminus_diag_eq, Rabs_R0; [exact He|reflexivity].
Qed.
Lemma coordinates_close_sym d e (z w : Tn d R) :
  close_n d e z w -> close_n d e w z.
Proof.
  induction d; [exact (fun _ => I)|].
  destruct z as [x z], w as [y w]; simpl; intros [H0 Hs]; split.
  - rewrite Rabs_minus_sym; exact H0.
  - apply IHd; exact Hs.
Qed.
Lemma coordinates_close_mono d e f (z w : Tn d R) :
  e <= f -> close_n d e z w -> close_n d f z w.
Proof.
  induction d; [exact (fun _ _ => I)|].
  destruct z as [x z], w as [y w]; simpl; intros Hef [H0 Hs]; split.
  - lra.
  - apply IHd; assumption.
Qed.
Lemma coordinates_close_triangle d e f (x y z : Tn d R) :
  close_n d e x y -> close_n d f y z -> close_n d (e+f) x z.
Proof.
  induction d; [exact (fun _ _ => I)|].
  destruct x as [x xs], y as [y ys], z as [z zs]; simpl.
  intros [Hxy Hxys] [Hyz Hyzs]; split; [|eapply IHd; eassumption].
  replace (x-z) with ((x-y)+(y-z)) by ring.
  pose proof (Rabs_triang (x-y) (y-z)); lra.
Qed.

Lemma coordinates_close_iff d e (z w : Tn d R) :
  close_n d e z w <-> forall i, (i<d)%nat ->
    Rabs (nth i (coordinates_to_list d z) 0 - nth i (coordinates_to_list d w) 0) < e.
Proof.
  induction d; [simpl; split; [intros _ i Hi; lia|intros; exact I]|].
  destruct z as [x z], w as [y w]; simpl; split.
  - intros [H0 Hs] [|i] Hi; simpl; [exact H0|].
    apply IHd; [exact Hs|lia].
  - intro H; split.
    + exact (H O ltac:(lia)).
    + apply IHd; intros i Hi; exact (H (S i) ltac:(lia)).
Qed.
Lemma coordinates_close_lists d e xs ys :
  length xs = d -> length ys = d ->
  (close_n d e (coordinates_of_list d xs) (coordinates_of_list d ys) <->
    forall i, (i<d)%nat -> Rabs (nth i xs 0 - nth i ys 0) < e).
Proof.
  intros Hx Hy; rewrite coordinates_close_iff.
  rewrite !coordinates_list_roundtrip by assumption; reflexivity.
Qed.
