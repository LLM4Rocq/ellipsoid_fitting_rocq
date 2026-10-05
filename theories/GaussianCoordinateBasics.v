From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianCoordinateDefinitions.
From EllipsoidFitting Require Import GaussianCoordinateCompactness.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/GaussianCoordinateBasics.v from Coquelicot to
   MathComp-Analysis.

   The original imported Coquelicot and its Compactness library for three
   names only: Tn, close_n and bounded_n. Tn and close_n now come from the
   port of GaussianCoordinateDefinitions, and bounded_n from the helper
   module GaussianCoordinateCompactness. All three are copies of the
   definitions of Coquelicot.Compactness (Coquelicot 3.4.4), convertible
   with them, so every statement below is the original text, word for word,
   and says the same thing. The proofs are the original ones.

   This module loads no MathComp library itself, so nth is Stdlib's List.nth
   and (i<d)%nat is Peano's lt, as in the original. A module that imports
   this one after MathComp sees the same constants: nth here is List.nth
   (MathComp's seq.nth takes its arguments in another order), and the bound
   on i is Peano's lt, which such a module writes (i < d)%coq_nat.
   GaussianCoordinateCompactness depends on MathComp's boolp, but only its
   Fixpoint bounded_n is used here, and that uses no axiom. *)

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

Lemma coordinates_bounded_iff d (a b z : Tn d R) :
  bounded_n d a b z <-> forall i, (i<d)%nat ->
    nth i (coordinates_to_list d a) 0 <= nth i (coordinates_to_list d z) 0 <=
      nth i (coordinates_to_list d b) 0.
Proof.
  induction d; [simpl; split; [intros _ i Hi; lia|intros; exact I]|].
  destruct a as [a aa], b as [b bb], z as [z zz]; simpl; split.
  - intros [H0 Hs] [|i] Hi; simpl; [exact H0|].
    apply IHd; [exact Hs|lia].
  - intro H; split.
    + exact (H O ltac:(lia)).
    + apply IHd; intros i Hi; exact (H (S i) ltac:(lia)).
Qed.
Lemma coordinates_bounded_dec d (a b z : Tn d R) :
  {bounded_n d a b z}+{~bounded_n d a b z}.
Proof.
  induction d; [left; exact I|].
  destruct a as [a aa], b as [b bb], z as [z zz]; simpl.
  destruct (Rle_dec a z), (Rle_dec z b), (IHd aa bb zz);
    [left|right|right|right|right|right|right|right]; tauto.
Qed.
