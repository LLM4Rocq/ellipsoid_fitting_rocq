From Stdlib Require Import List.

(* row_prefixes N d D xs reads xs as N rows of length d + D and keeps the
   first d entries of each row, in order. *)

Fixpoint row_prefixes {A : Type} (N d D : nat) (xs : list A) : list A :=
  match N with
  | O => nil
  | S k => firstn d xs ++ row_prefixes k d D (skipn (d+D) xs)
  end.
