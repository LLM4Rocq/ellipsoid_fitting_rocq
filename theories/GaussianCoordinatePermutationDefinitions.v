From Stdlib Require Import Reals List.
Import ListNotations.

Fixpoint swap_adjacent (i : nat) (xs : list R) : list R :=
  match i, xs with
  | O, x :: y :: zs => y :: x :: zs
  | S j, x :: zs => x :: swap_adjacent j zs
  | _, _ => xs
  end.

Fixpoint replace_coordinate (i : nat) (value : R) (xs : list R) : list R :=
  match i, xs with
  | O, _ :: zs => value :: zs
  | S j, x :: zs => x :: replace_coordinate j value zs
  | _, _ => xs
  end.

Fixpoint move_coordinate_last (i : nat) (xs : list R) : list R :=
  match i, xs with
  | O, x :: zs => zs ++ [x]
  | S j, x :: zs => x :: move_coordinate_last j zs
  | _, _ => xs
  end.
