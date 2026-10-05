From Stdlib Require Import List.

Fixpoint row_prefixes {A : Type} (N d D : nat) (xs : list A) : list A :=
  match N with
  | O => nil
  | S k => firstn d xs ++ row_prefixes k d D (skipn (d+D) xs)
  end.
