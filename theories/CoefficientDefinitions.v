From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions HessianDefinitions ContinuityDefinitions.
Open Scope R_scope.

(* Contraction of a third-order array with a matrix.
   module_coordinate_sum V n f is the sum f 0 + ... + f n in a normed
   module V; on R^o it has the value of coordinate_sum n f of
   MatrixDefinitions. coefficient_contract V n F W is the sum over
   i, j <= n of matrix_entry n W j i *: F i j. third_action n T W contracts
   the third array T with W into a Hessian array, and
   third_evaluation n T U V W evaluates that Hessian array at U and V with
   hessian_evaluation. *)

Fixpoint module_coordinate_sum (V : normedModType R) (n : nat) (f : nat -> V) : V :=
  match n with
  | O => f O
  | S k => (f O + module_coordinate_sum V k (fun i => f (S i)))%R
  end.

Definition coefficient_contract (V : normedModType R) n
    (F : nat -> nat -> V) (W : matrix n) : V :=
  module_coordinate_sum V n (fun i => module_coordinate_sum V n
    (fun j => (matrix_entry n W j i *: F i j)%R)).

Definition third_action n (T : third_array n) (W : matrix n) : hessian_array n :=
  coefficient_contract (hessian_NormedModule n) n (third_entry n T) W.

Definition third_evaluation n (T : third_array n) (U V W : matrix n) : R :=
  hessian_evaluation n (third_action n T W) U V.
