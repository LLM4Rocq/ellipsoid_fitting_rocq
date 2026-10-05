From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations
  GaussianCoordinateDerivativeDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Coordinate derivatives under changes of coordinates. Here
   finite_coordinate_derivative d i F DF says that DF is the derivative of
   F : list R -> R in coordinate i, at every list of length d.
   - finite_coordinate_derivative_last: for the last of S d coordinates,
     DF (xs ++ [t]) is the derivative of u |-> F (xs ++ [u]) at t, for
     every list xs of length d.
   - finite_coordinate_derivative_swap_right: swapping coordinates i and
     S i turns a derivative in coordinate i into one in coordinate S i.
   - finite_coordinate_derivative_times_other: multiplying F by coordinate
     j <> i multiplies its derivative in coordinate i by coordinate j.
   The derivatives are MathComp's is_derive at t in the direction 1 on R^o,
   the ordinary derivative of a function R -> R. *)

Lemma replace_coordinate_last xs t u :
  replace_coordinate (length xs) u (xs++[t])%list = (xs++[u])%list.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  simpl; rewrite IH; reflexivity.
Qed.

Lemma finite_coordinate_derivative_last d F DF :
  finite_coordinate_derivative (S d) d F DF ->
  forall xs : list R, length xs = d -> forall t : R,
  @is_derive R R^o R^o t 1 (fun u => F (xs++[u])%list) (DF (xs++[t])%list).
Proof.
  intros HD xs Hxs t.
  pose proof (HD (xs++[t])%list ltac:(rewrite length_app; rewrite Hxs; simpl; lia)) as H.
  rewrite <- Hxs in H; rewrite nth_middle in H.
  change (@is_derive R R^o R^o t 1
    (fun u : R => F (replace_coordinate (length xs) u (xs++[t])%list)) (DF (xs++[t])%list)) in H.
  assert (He : (fun u => F (replace_coordinate (length xs) u (xs++[t])%list)) =
    (fun u => F (xs++[u])%list)).
  { apply functional_extensionality; intro u; rewrite replace_coordinate_last; reflexivity. }
  rewrite He in H; exact H.
Qed.

Lemma finite_coordinate_derivative_swap_right d i F DF :
  (S i < d)%coq_nat -> finite_coordinate_derivative d i F DF ->
  finite_coordinate_derivative d (S i)
    (fun xs => F (swap_adjacent i xs)) (fun xs => DF (swap_adjacent i xs)).
Proof.
  intros Hi HD xs Hxs.
  pose proof (HD (swap_adjacent i xs) ltac:(rewrite swap_adjacent_length; exact Hxs)) as H.
  rewrite (swap_adjacent_nth_left i xs ltac:(lia)) in H.
  apply is_derive_ext with (f := fun t => F (replace_coordinate i t (swap_adjacent i xs))).
  - intro t; rewrite (swap_adjacent_replace_right i t xs ltac:(lia)); reflexivity.
  - exact H.
Qed.

Lemma finite_coordinate_derivative_times_other d i j F DF :
  i <> j -> finite_coordinate_derivative d i F DF ->
  finite_coordinate_derivative d i
    (fun xs => List.nth j xs 0 * F xs) (fun xs => List.nth j xs 0 * DF xs).
Proof.
  intros Hij HD xs Hxs.
  apply is_derive_ext with (f := fun t => List.nth j xs 0 * F (replace_coordinate i t xs)).
  - intro t; rewrite (replace_coordinate_nth_other i j t xs Hij); reflexivity.
  - apply is_derive_scal; exact (HD xs Hxs).
Qed.
