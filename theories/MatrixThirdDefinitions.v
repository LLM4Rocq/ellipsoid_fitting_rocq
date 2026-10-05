From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions ThirdDefinitions
  MatrixDefinitions MatrixGibbsDefinitions MatrixSecondDefinitions.
Open Scope R_scope.

(* The third derivative of the nested soft minimax of the affine matrix
   scores offset y s + trace_pair n (coeff y s) A, in the directions U, V
   and W. matrix_inner_cumulant is the third cumulant of the pairings
   trace_pair n (coeff y s) U, V and W under the inner Gibbs law over S.
   matrix_nested_third_derivative combines, under the outer Gibbs law over
   Y at inverse temperature - beta, the mean of these inner cumulants, the
   covariances of the inner covariances with the inner means, and the third
   cumulant of the inner means. MatrixThird proves that it is the
   derivative of matrix_nested_second_derivative. *)

Definition matrix_inner_cumulant (n : nat) (gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (S : list nat) (A U V W : matrix n) (y : nat) : R :=
  gibbs_cumulant3 gamma (matrix_affine_scores n offset coeff A y) S
    (fun s => trace_pair n (coeff y s) U)
    (fun s => trace_pair n (coeff y s) V)
    (fun s => trace_pair n (coeff y s) W).

Definition matrix_nested_third_derivative (n : nat) (beta gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (Y S : list nat) (A U V W : matrix n) : R :=
  gamma ^ 2 * gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (fun y => matrix_inner_cumulant n gamma offset coeff S A U V W y) -
  beta * gamma *
    (gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
       (fun y => matrix_inner_covariance n gamma offset coeff S A U V y)
       (matrix_inner_derivative n gamma offset coeff S A W) +
     gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
       (fun y => matrix_inner_covariance n gamma offset coeff S A U W y)
       (matrix_inner_derivative n gamma offset coeff S A V) +
     gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
       (fun y => matrix_inner_covariance n gamma offset coeff S A V W y)
       (matrix_inner_derivative n gamma offset coeff S A U)) +
  beta ^ 2 * gibbs_cumulant3 (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_derivative n gamma offset coeff S A U)
    (matrix_inner_derivative n gamma offset coeff S A V)
    (matrix_inner_derivative n gamma offset coeff S A W).
