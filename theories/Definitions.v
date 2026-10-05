From Stdlib Require Import Reals List PeanoNat.
Import ListNotations.
Open Scope R_scope.

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
