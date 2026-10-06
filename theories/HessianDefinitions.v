From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixGibbsDefinitions
  MatrixSecondDefinitions MatrixThirdDefinitions GradientDefinitions.
Open Scope R_scope.

(* Hessian arrays for functions of a matrix. A hessian_array n holds one
   matrix for each pair (i, j) of matrix indices, and carries the Euclidean
   norm of all its entries, the Frobenius norm of the four-index array.
   hessian_build and hessian_entry build and read an array;
   hessian_action H V is the matrix with entries trace_pair (H i j) V, and
   hessian_evaluation H U V is trace_pair (hessian_action H V) U.
   matrix_nested_hessian collects the derivatives of the gradient of the
   nested Gibbs function in the directions of the basis matrices, and
   matrix_nested_gradient_second_derivative and
   matrix_nested_hessian_derivative take one more derivative, in a
   direction V. R_scope is opened after the MathComp imports, so the
   arithmetic is Stdlib's. *)

Definition hessian_NormedModule (n : nat) : normedModType R :=
  tuple_NormedModule (tuple_NormedModule (matrix_NormedModule n) n) n.
Definition hessian_array (n : nat) : Type := hessian_NormedModule n.

Definition hessian_build (n : nat) (F : nat -> nat -> matrix n) : hessian_array n :=
  tuple_build (tuple_NormedModule (matrix_NormedModule n) n) n
    (fun i => tuple_build (matrix_NormedModule n) n (F i)).

Definition hessian_entry (n : nat) (H : hessian_array n) (i j : nat) : matrix n :=
  tuple_entry (matrix_NormedModule n) n j
    (tuple_entry (tuple_NormedModule (matrix_NormedModule n) n) n i H).

Definition hessian_action (n : nat) (H : hessian_array n) (V : matrix n) : matrix n :=
  matrix_build n (fun i j => trace_pair n (hessian_entry n H i j) V).

Definition hessian_evaluation (n : nat) (H : hessian_array n) (U V : matrix n) : R :=
  trace_pair n (hessian_action n H V) U.

Definition matrix_nested_hessian (n : nat) (beta gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (Y S : list nat) (A : matrix n) : hessian_array n :=
  hessian_build n (fun i j =>
    matrix_nested_gradient_derivative n beta gamma offset coeff Y S A (matrix_basis n j i)).

Definition matrix_nested_gradient_second_derivative (n : nat) (beta gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (Y S : list nat) (A U V : matrix n) : matrix n :=
  matrix_build n (fun i j =>
    matrix_nested_third_derivative n beta gamma offset coeff Y S A (matrix_basis n j i) U V).

Definition matrix_nested_hessian_derivative (n : nat) (beta gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (Y S : list nat) (A V : matrix n) : hessian_array n :=
  hessian_build n (fun i j =>
    matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S A
      (matrix_basis n j i) V).
