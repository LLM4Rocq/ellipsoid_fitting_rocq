From Stdlib Require Import Reals List.
Import ListNotations.

(* replace_coordinate i value sets coordinate i of a list of coordinates to
   value, and returns the list unchanged when i is out of range. *)

Fixpoint replace_coordinate (i : nat) (value : R) (xs : list R) : list R :=
  match i, xs with
  | O, _ :: zs => value :: zs
  | S j, x :: zs => x :: replace_coordinate j value zs
  | _, _ => xs
  end.
