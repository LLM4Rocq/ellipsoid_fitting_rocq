From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Export MatrixEuclideanProduct.
Open Scope R_scope.

(* Port of theories/MatrixDefinitions.v from Coquelicot to MathComp-Analysis.

   Coquelicot's NormedModule R_AbsRing becomes normedModType R, and its
   R_NormedModule becomes R^o. Coquelicot's prod_NormedModule becomes
   euclidean_product of MatrixEuclideanProduct, which keeps Coquelicot's
   product norm sqrt (norm (fst x) ^ 2 + norm (snd x) ^ 2) instead of
   MathComp's max norm. A vector therefore still carries the Euclidean norm
   and a matrix the Frobenius norm. Coquelicot's zero, plus and scal become
   0, + and *: of MathComp, which are componentwise on pairs as before.

   One thing changes: the ball. Coquelicot's ball on a product is the
   conjunction of the component balls, while the ball of euclidean_product is
   the norm ball, ball x e y <-> `|x - y| < e. The uniform structure is
   therefore not Coquelicot's. The neighbourhood filters, and so the
   topology, are the same, as euclidean_product_nbhsE states. Statements
   about norms keep their meaning, and so do statements about continuity and
   derivatives.

   The definitions below keep the names, arguments and nested-pair
   representation of the original. A pair written for a tuple needs its type,
   as in (a, b) : tuple_NormedModule V 1, to get this norm and not the max
   norm of V * V. *)

(* A tuple indexed by n has S n coordinates.  Keeping dimensions positive
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

Definition matrix_mul (n : nat) (A B : matrix n) : matrix n :=
  matrix_build n (fun i j => coordinate_sum n
    (fun k => matrix_entry n A i k * matrix_entry n B k j)).

Definition matrix_trace (n : nat) (A : matrix n) : R :=
  coordinate_sum n (fun i => matrix_entry n A i i).

Definition trace_pair (n : nat) (B H : matrix n) : R :=
  coordinate_sum n (fun i => coordinate_sum n
    (fun j => matrix_entry n B i j * matrix_entry n H j i)).
