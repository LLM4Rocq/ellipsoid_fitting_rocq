From Stdlib Require Import List.

Definition row_chunk {A : Type} (K i : nat) (xs : list A) : list A :=
  firstn K (skipn (i*K) xs).

Definition row_background {A : Type} (N K i : nat) (xs : list A) : list A :=
  skipn ((S i)*K) xs ++ firstn (i*K) xs.

Definition row_assemble {A : Type} (N K i : nat) (background row : list A) : list A :=
  skipn ((N-1-i)*K) background ++ row ++ firstn ((N-1-i)*K) background.
