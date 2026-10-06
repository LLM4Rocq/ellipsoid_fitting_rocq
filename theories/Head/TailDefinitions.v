From Stdlib Require Import Reals List PeanoNat.
Import ListNotations.
Open Scope R_scope.

(* Definitions for the head and tail decomposition of a vector. energy w A
   is the sum of w over the list A, and outside B A is the list of the
   elements of A that are not in B. squared_energy y A and vector_norm y A
   are the squared Euclidean norm and the Euclidean norm of the coordinates
   of y listed in A. tail_indices n J lists the indices of seq 0 n outside
   the head J. head_tail_constant theta is the constant of the bound
   head_tail_constant theta * d * ln d on the size of the head (Head.TailDecomposition). *)

Fixpoint energy (w : nat -> R) (A : list nat) : R :=
  match A with [] => 0 | i :: A' => w i + energy w A' end.

Definition outside (B A : list nat) : list nat :=
  filter (fun i => if in_dec Nat.eq_dec i B then false else true) A.

(* A vector in R^n is represented by its coordinates on seq 0 n.
   Values outside that finite domain never enter its norm or a conclusion. *)
Definition squared_energy (y : nat -> R) (A : list nat) : R :=
  energy (fun i => y i ^ 2) A.
Definition vector_norm (y : nat -> R) (A : list nat) : R :=
  sqrt (squared_energy y A).
Definition tail_indices (n : nat) (J : list nat) : list nat :=
  outside J (seq 0 n).
Definition head_tail_constant (theta : R) : R := 16 / (theta ^ 2 * ln 2).
