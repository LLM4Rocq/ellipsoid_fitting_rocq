From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Matrix.Definitions Gibbs.MatrixDefinitions
  Gibbs.MatrixSecondDerivativeDefinitions Tensor.GibbsDefinitions.
Open Scope R_scope.

(* The gradient of the nested soft minimax of affine matrix scores, as a
   matrix, and its derivative. The scores are
   offset y s + trace_pair n (coeff y s) A (matrix_affine_scores).
   - matrix_basis n i j is the matrix unit: entry (i, j) is 1, the others
     are 0.
   - matrix_inner_gradient is the mean of the coefficient matrices
     coeff y s under the inner Gibbs law over S.
   - matrix_nested_gradient is the mean of these inner gradients under the
     outer Gibbs law over Y, at inverse temperature - beta. Its pairing
     trace_pair with U is the derivative in the direction U
     (matrix_nested_gradient_trace in Gibbs.MatrixNestedGradient).
   - matrix_nested_gradient_derivative n ... A V is the matrix whose entry
     (i, j) is the second derivative matrix_nested_second_derivative in the
     directions matrix_basis n j i and V. It is the derivative of the
     gradient in the direction V (matrix_nested_gradient_frechet). *)

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
