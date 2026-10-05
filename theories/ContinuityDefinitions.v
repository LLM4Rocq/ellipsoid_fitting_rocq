From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions GradientDefinitions HessianDefinitions.
Open Scope R_scope.

(* Port of theories/ContinuityDefinitions.v from Coquelicot to
   MathComp-Analysis.

   Coquelicot's NormedModule R_AbsRing becomes normedModType R, as in the
   ports of MatrixDefinitions and HessianDefinitions. third_NormedModule n is
   built from tuple_NormedModule of MatrixDefinitions and hessian_NormedModule
   of HessianDefinitions, whose products are euclidean_product of
   MatrixEuclideanProduct and keep Coquelicot's product norm
   sqrt (norm (fst x) ^ 2 + norm (snd x) ^ 2). A third-order coefficient
   array therefore still carries the Euclidean norm of all its entries, that
   is the Frobenius norm of the six-index array, as in the original. Its ball
   is the norm ball, as MatrixDefinitions explains, and its topology is the
   one of the original.

   The other definitions keep the text of the original. They use only
   tuple_build and tuple_entry of MatrixDefinitions, matrix_basis of
   GradientDefinitions and matrix_nested_hessian_derivative of
   HessianDefinitions, whose ports keep the same names, arguments and values.
   MathComp is imported only for normedModType; R_scope is opened after it,
   so nothing here uses MathComp's arithmetic. *)

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
