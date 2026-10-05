From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions MatrixDefinitions MatrixGibbsDefinitions
  MatrixSecondDefinitions MatrixThirdDefinitions.
Open Scope R_scope.

(* Soft min-max of matrix scores, for arrays of matrix blocks. For an array
   A of matrices, the score of the pair (z, s) is
   soft_matrix_scores y B I A z s, the sum over i in I of
   y z i * trace_pair (B s) (A i). soft_matrix_inner is the soft maximum of
   these scores over s in S, and soft_matrix_phi their soft min-max over Y
   and S. soft_matrix_block_add adds a matrix M to block i.
   soft_matrix_third is matrix_nested_third_derivative at the zero matrix,
   with offsets soft_matrix_scores y B I A and coefficient matrices
   soft_matrix_coefficients y B i z s = y z i * B s. MathComp is not
   imported, so the arithmetic, ln and exp are Stdlib's. *)

(* An array is observed on the finite coordinate list I.  The matrix index n
   represents positive matrix dimension S n.  These formulas extend the
   manuscript's symmetric block arrays to all real matrix blocks. *)
Definition soft_matrix_block_add n (A : nat -> matrix n) i (M : matrix n) : nat -> matrix n :=
  fun j => if Nat.eq_dec j i then matrix_add n (A j) M else A j.

Definition soft_matrix_scores n (y : nat -> nat -> R) (B : nat -> matrix n)
    (I : list nat) (A : nat -> matrix n) z s : R :=
  finite_sum (fun i => y z i * trace_pair n (B s) (A i)) I.

Definition soft_matrix_inner n gamma y B I S (A : nat -> matrix n) z : R :=
  soft_max gamma (soft_matrix_scores n y B I A z) S.

Definition soft_matrix_phi n beta gamma y B I Y S (A : nat -> matrix n) : R :=
  soft_minimax beta gamma (soft_matrix_scores n y B I A) Y S.

Definition soft_matrix_coefficients n (y : nat -> nat -> R) (B : nat -> matrix n) i z s : matrix n :=
  matrix_scale n (y z i) (B s).

Definition soft_matrix_third n beta gamma y B I Y S (A : nat -> matrix n)
    i (U V W : matrix n) : R :=
  matrix_nested_third_derivative n beta gamma (soft_matrix_scores n y B I A)
    (soft_matrix_coefficients n y B i) Y S (matrix_zero n) U V W.
