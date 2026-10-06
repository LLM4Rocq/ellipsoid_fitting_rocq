From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Matrix.Definitions.
Open Scope R_scope.

(* Soft maxima of scores affine in a matrix A, and Gibbs averages of their
   derivatives. matrix_affine_scores n offset coeff A y s is
   offset y s + trace_pair n (coeff y s) A, matrix_inner_values is their
   soft maximum over s in S, and matrix_inner_derivative is the Gibbs
   average over s of trace_pair n (coeff y s) U; for gamma > 0 and nonempty
   S, it is the derivative of matrix_inner_values at A in the direction U
   (matrix_inner_frechet in Gibbs.MatrixFrechet). matrix_nested_derivative averages
   these derivatives under the law of matrix_inner_values over Y at inverse
   temperature - beta. The arithmetic, ln and exp are Stdlib's. *)

Definition matrix_affine_scores (n : nat) (offset : nat -> nat -> R)
    (coeff : nat -> nat -> matrix n) (A : matrix n) (y s : nat) : R :=
  offset y s + trace_pair n (coeff y s) A.

Definition matrix_inner_values (n : nat) (gamma : R) (offset : nat -> nat -> R)
    (coeff : nat -> nat -> matrix n) (S : list nat) (A : matrix n) (y : nat) : R :=
  soft_max gamma (matrix_affine_scores n offset coeff A y) S.

Definition matrix_inner_derivative (n : nat) (gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (S : list nat) (A U : matrix n) (y : nat) : R :=
  gibbs_average gamma (matrix_affine_scores n offset coeff A y) S
    (fun s => trace_pair n (coeff y s) U).

Definition matrix_nested_derivative (n : nat) (beta gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (Y S : list nat) (A U : matrix n) : R :=
  gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_derivative n gamma offset coeff S A U).
