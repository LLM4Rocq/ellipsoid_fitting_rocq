From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import Analysis.CoordinatePermutationDefinitions
  Analysis.CoordinatePermutations Gaussian.CoordinateDerivativeDefinitions.
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
