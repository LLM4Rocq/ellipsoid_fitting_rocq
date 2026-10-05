From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions ThirdDefinitions
  MatrixDefinitions MatrixGibbsDefinitions MatrixSecondDefinitions.
Open Scope R_scope.

(* Port of theories/MatrixThirdDefinitions.v from Coquelicot to
   MathComp-Analysis. The original used nothing from Coquelicot directly: its
   only Coquelicot content came through matrix n and trace_pair of
   MatrixDefinitions, whose port keeps the same names and arguments, and
   through the definitions of MatrixGibbsDefinitions and
   MatrixSecondDefinitions, whose ports keep their text. So the import of
   Coquelicot is dropped and nothing else changes. MathComp is not imported
   here, so the arithmetic, including the powers gamma ^ 2 and beta ^ 2, the
   products, the sums, the difference and the minus sign of - beta, is
   Stdlib's, as before. *)

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
