(* Prints the axioms on which the moment bound of Gaussian matrix series
   and its rectangular corollary (target T1 of phase 12) depends. `make
   check` compares the output with
   check/matrix_series_assumptions.expected. The definition compiles only
   if matrix_series_theorem proves the frozen statement
   matrix_series_statement. *)
From GaussianApplications Require Import MatrixSeriesStatement
  MatrixSeriesTheorem.

Definition matrix_series_theorem_checked :
  matrix_series_statement := matrix_series_theorem.

Print Assumptions matrix_series_theorem.
