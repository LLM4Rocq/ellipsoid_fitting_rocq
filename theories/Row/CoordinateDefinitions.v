From Stdlib Require Import List.

(* A list of N * K coordinates read as N rows of length K. row_chunk K i xs
   is row i. row_assemble N K i background row builds such a list whose
   row i is row, from the N - 1 rows of background: the last i rows of
   background, then row, then the first N - 1 - i rows of background. *)

Definition row_chunk {A : Type} (K i : nat) (xs : list A) : list A :=
  firstn K (skipn (i*K) xs).

Definition row_assemble {A : Type} (N K i : nat) (background row : list A) : list A :=
  skipn ((N-1-i)*K) background ++ row ++ firstn ((N-1-i)*K) background.
