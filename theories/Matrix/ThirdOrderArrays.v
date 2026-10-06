From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Gibbs.NestedGradientDefinitions Gibbs.HessianDefinitions.
Open Scope R_scope.

(* Third-order coefficient arrays. third_array n is an (S n) x (S n) tuple
   of the Hessian arrays of Gibbs.HessianDefinitions, with the Euclidean norm of
   all its entries; third_build and third_entry write and read its entries.
   matrix_nested_third_coefficients ... A is the array of the third
   derivatives matrix_nested_third_derivative (Gibbs.MatrixThirdDerivativeDefinitions) at A
   in the coordinate directions matrix_basis n j i. *)

Definition third_NormedModule (n : nat) : normedModType R :=
  tuple_NormedModule (tuple_NormedModule (hessian_NormedModule n) n) n.
Definition third_array (n : nat) : Type := third_NormedModule n.

Definition third_build (n : nat) (F : nat -> nat -> hessian_array n) : third_array n :=
  tuple_build (tuple_NormedModule (hessian_NormedModule n) n) n
    (fun i => tuple_build (hessian_NormedModule n) n (F i)).

Definition third_entry (n : nat) (T : third_array n) (i j : nat) : hessian_array n :=
  tuple_entry (hessian_NormedModule n) n j
    (tuple_entry (tuple_NormedModule (hessian_NormedModule n) n) n i T).

Definition matrix_nested_third_coefficients (n : nat) (beta gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (Y S : list nat) (A : matrix n) : third_array n :=
  third_build n (fun i j =>
    matrix_nested_hessian_derivative n beta gamma offset coeff Y S A (matrix_basis n j i)).
