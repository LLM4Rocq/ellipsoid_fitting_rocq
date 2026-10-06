From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Export Matrix.EuclideanProduct.
Open Scope R_scope.

(* Tuples and square matrices of reals, as nested pairs.

   tuple_NormedModule V n nests euclidean_product of Matrix.EuclideanProduct,
   so its norm is sqrt (`|x_0| ^ 2 + ... + `|x_n| ^ 2), not MathComp's max
   norm: a tuple of reals (V = R^o, the normed module view of R) carries the
   Euclidean norm. matrix n is a tuple of S n rows, each a tuple of S n
   reals, so it carries the Frobenius norm. The balls of these types are
   norm balls, and their topology is the product topology
   (euclidean_product_nbhsE).

   tuple_entry V n i x is the coordinate i of x, and 0 when i > n;
   tuple_build V n f is the tuple of the f i, i <= n. coordinate_sum n f is
   f 0 + ... + f n. matrix_entry n A i j is the entry in row i and column j.
   The zero, sum and scaling of matrices are MathComp's 0, + and *:, which
   are componentwise. matrix_trace n A is the trace of A, and
   trace_pair n B H is the trace of the product B H.

   A pair written for a tuple needs its type, as in
   (a, b) : tuple_NormedModule V 1, to get this norm and not the max norm of
   V * V. *)

(* A tuple indexed by n has S n coordinates. Keeping dimensions positive
   avoids introducing an artificial coordinate into a zero-dimensional space. *)
Fixpoint tuple_NormedModule (V : normedModType R) (n : nat) :
    normedModType R :=
  match n with
  | O => V
  | S k => euclidean_product V (tuple_NormedModule V k)
  end.

Fixpoint tuple_entry (V : normedModType R) (n i : nat) :
    tuple_NormedModule V n -> V :=
  match n with
  | O => match i with O => fun x => x | S _ => fun _ => 0%R end
  | S k =>
    match i with
    | O => fun x => fst x
    | S j => fun x => tuple_entry V k j (snd x)
    end
  end.

Fixpoint tuple_build (V : normedModType R) (n : nat)
    (f : nat -> V) : tuple_NormedModule V n :=
  match n with
  | O => f O
  | S k => (f O, tuple_build V k (fun i => f (S i)))
  end.

Fixpoint coordinate_sum (n : nat) (f : nat -> R) : R :=
  match n with
  | O => f O
  | S k => f O + coordinate_sum k (fun i => f (S i))
  end.

Definition matrix_NormedModule (n : nat) : normedModType R :=
  tuple_NormedModule (tuple_NormedModule R^o n) n.

Definition matrix (n : nat) : Type := matrix_NormedModule n.

Definition matrix_entry (n : nat) (A : matrix n) (i j : nat) : R :=
  tuple_entry R^o n j
    (tuple_entry (tuple_NormedModule R^o n) n i A).

Definition matrix_build (n : nat) (f : nat -> nat -> R) : matrix n :=
  tuple_build (tuple_NormedModule R^o n) n
    (fun i => tuple_build R^o n (f i)).

Definition matrix_zero (n : nat) : matrix n := 0%R.
Definition matrix_add (n : nat) (A B : matrix n) : matrix n := (A + B)%R.
Definition matrix_scale (n : nat) (c : R) (A : matrix n) : matrix n :=
  (c *: A)%R.

Definition matrix_trace (n : nat) (A : matrix n) : R :=
  coordinate_sum n (fun i => matrix_entry n A i i).

Definition trace_pair (n : nat) (B H : matrix n) : R :=
  coordinate_sum n (fun i => coordinate_sum n
    (fun j => matrix_entry n B i j * matrix_entry n H j i)).
