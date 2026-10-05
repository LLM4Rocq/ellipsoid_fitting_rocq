From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions MatrixDefinitions.
Open Scope R_scope.

(* Port of theories/MatrixGibbsDefinitions.v from Coquelicot to
   MathComp-Analysis. The original used nothing from Coquelicot directly:
   its only Coquelicot content came through matrix n and trace_pair of
   MatrixDefinitions, whose port keeps the same names and arguments. So the
   import of Coquelicot is dropped and nothing else changes. MathComp is not
   imported here, so the arithmetic, including the minus sign of - beta, and
   the ln and exp inside soft_max and gibbs_average are Stdlib's, as before. *)

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
