From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions MatrixDefinitions MatrixGibbsDefinitions.
Open Scope R_scope.

(* Port of theories/MatrixSecondDefinitions.v from Coquelicot to
   MathComp-Analysis. The original used nothing from Coquelicot directly: its
   only Coquelicot content came through matrix n and trace_pair of
   MatrixDefinitions, whose port keeps the same names and arguments, and
   through the definitions of MatrixGibbsDefinitions, which are unchanged. So
   the import of Coquelicot is dropped and nothing else changes. MathComp is
   not imported here, so the arithmetic, including the product gamma * _, the
   difference and the minus sign of - beta, is Stdlib's, as before. *)

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
