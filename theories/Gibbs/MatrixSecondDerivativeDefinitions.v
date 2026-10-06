From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Matrix.Definitions Gibbs.MatrixDefinitions.
Open Scope R_scope.

(* The derivative of matrix_nested_derivative (Gibbs.MatrixDefinitions) in a
   second direction. matrix_inner_covariance is the covariance, under the
   inner Gibbs law over s in S, of trace_pair n (coeff y s) U and
   trace_pair n (coeff y s) V. matrix_nested_second_derivative is gamma
   times the outer average of these covariances minus beta times the outer
   covariance of the inner derivatives in the directions U and V. For
   beta, gamma > 0 and nonempty Y and S, it is the derivative at A, in the
   direction V, of the map
   M |-> matrix_nested_derivative n beta gamma offset coeff Y S M U
   (matrix_nested_derivative_frechet in Gibbs.MatrixSecondDerivative). The arithmetic is
   Stdlib's. *)

Definition matrix_inner_covariance (n : nat) (gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (S : list nat) (A U V : matrix n) (y : nat) : R :=
  gibbs_covariance gamma (matrix_affine_scores n offset coeff A y) S
    (fun s => trace_pair n (coeff y s) U)
    (fun s => trace_pair n (coeff y s) V).

Definition matrix_nested_second_derivative (n : nat) (beta gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (Y S : list nat) (A U V : matrix n) : R :=
  gamma * gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (fun y => matrix_inner_covariance n gamma offset coeff S A U V y) -
  beta * gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_derivative n gamma offset coeff S A U)
    (matrix_inner_derivative n gamma offset coeff S A V).
