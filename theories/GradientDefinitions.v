From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions MatrixDefinitions
  MatrixGibbsDefinitions MatrixSecondDefinitions TensorGibbsDefinitions.
Open Scope R_scope.

(* Port of theories/GradientDefinitions.v from Coquelicot to
   MathComp-Analysis. The original used nothing from Coquelicot directly: its
   only Coquelicot content came through matrix n and matrix_build of
   MatrixDefinitions, through matrix_gibbs_mean of TensorGibbsDefinitions,
   and through the definitions of MatrixGibbsDefinitions and
   MatrixSecondDefinitions. Their ports keep the same names and arguments.
   So the import of Coquelicot is dropped and nothing else changes. MathComp
   is not imported here, so the literals 1 and 0 are Stdlib's reals, the
   test && is Stdlib's andb, Nat.eqb is Stdlib's, and the minus sign of
   - beta is Stdlib's, as before. *)

Definition matrix_basis (n i j : nat) : matrix n :=
  matrix_build n (fun r c => if (Nat.eqb r i && Nat.eqb c j)%bool then 1 else 0).

Definition matrix_inner_gradient (n : nat) (gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (S : list nat) (A : matrix n) (y : nat) : matrix n :=
  matrix_gibbs_mean n gamma (matrix_affine_scores n offset coeff A y) S (coeff y).

Definition matrix_nested_gradient (n : nat) (beta gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (Y S : list nat) (A : matrix n) : matrix n :=
  matrix_gibbs_mean n (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_gradient n gamma offset coeff S A).

Definition matrix_nested_gradient_derivative (n : nat) (beta gamma : R)
    (offset : nat -> nat -> R) (coeff : nat -> nat -> matrix n)
    (Y S : list nat) (A V : matrix n) : matrix n :=
  matrix_build n (fun i j =>
    matrix_nested_second_derivative n beta gamma offset coeff Y S A
      (matrix_basis n j i) V).
