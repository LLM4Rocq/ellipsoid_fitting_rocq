From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions MatrixDefinitions MatrixGibbsDefinitions
  MatrixSecondDefinitions MatrixThirdDefinitions.
Open Scope R_scope.

(* Port of theories/SoftMatrixDefinitions.v from Coquelicot to
   MathComp-Analysis. The original used nothing from Coquelicot directly: its
   only Coquelicot content came through matrix n, matrix_zero, matrix_add,
   matrix_scale and trace_pair of MatrixDefinitions, and through the nested
   derivatives of MatrixGibbsDefinitions, MatrixSecondDefinitions and
   MatrixThirdDefinitions. Their ports keep the same names and arguments;
   matrix_zero, matrix_add and matrix_scale are now MathComp's 0, + and *: on
   the nested tuples, which are componentwise as Coquelicot's zero, plus and
   scal were. So the import of Coquelicot is dropped and nothing else
   changes. MathComp is not imported here, so the arithmetic and the test
   Nat.eq_dec j i are Stdlib's, as before. finite_sum, soft_max and
   soft_minimax come from SoftDefinitions, which is copied unchanged, so the
   ln and exp inside soft_max are Stdlib's. *)

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

Definition soft_matrix_first n beta gamma y B I Y S (A : nat -> matrix n) i (U : matrix n) : R :=
  matrix_nested_derivative n beta gamma (soft_matrix_scores n y B I A)
    (soft_matrix_coefficients n y B i) Y S (matrix_zero n) U.

Definition soft_matrix_second n beta gamma y B I Y S (A : nat -> matrix n)
    i (U V : matrix n) : R :=
  matrix_nested_second_derivative n beta gamma (soft_matrix_scores n y B I A)
    (soft_matrix_coefficients n y B i) Y S (matrix_zero n) U V.

Definition soft_matrix_third n beta gamma y B I Y S (A : nat -> matrix n)
    i (U V W : matrix n) : R :=
  matrix_nested_third_derivative n beta gamma (soft_matrix_scores n y B I A)
    (soft_matrix_coefficients n y B i) Y S (matrix_zero n) U V W.
