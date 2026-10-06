From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Tensor.Definitions.
Open Scope R_scope.

(* Inner and outer products of vectors, and the derivatives of
   x |-> x x^T used in second-order chaos terms. vector_outer n x y is the
   matrix x y^T and chaos_basis n a the a-th coordinate vector.
   chaos_first n x a and chaos_second n a b are the first and second
   partial derivatives of x |-> x x^T in the coordinates a and b, and
   chaos_contraction n T x is half the sum over a and b of
   T (chaos_first n x a) (chaos_first n x b) (chaos_second n a b). *)

Definition vector_inner (n : nat) (x y : vector n) : R :=
  coordinate_sum n (fun i => vector_entry n x i * vector_entry n y i).

Definition vector_outer (n : nat) (x y : vector n) : matrix n :=
  matrix_build n (fun i j => vector_entry n x i * vector_entry n y j).

Definition chaos_basis (n a : nat) : vector n :=
  tuple_build R^o n (fun i => if Nat.eqb i a then 1 else 0).

Definition chaos_first (n : nat) (x : vector n) (a : nat) : matrix n :=
  matrix_add n (vector_outer n (chaos_basis n a) x)
    (vector_outer n x (chaos_basis n a)).

Definition chaos_second (n a b : nat) : matrix n :=
  matrix_add n (vector_outer n (chaos_basis n a) (chaos_basis n b))
    (vector_outer n (chaos_basis n b) (chaos_basis n a)).

Definition chaos_contraction (n : nat)
    (T : matrix n -> matrix n -> matrix n -> R) (x : vector n) : R :=
  / 2 * coordinate_sum n (fun a => coordinate_sum n (fun b =>
    T (chaos_first n x a) (chaos_first n x b) (chaos_second n a b))).
