(* Prints the axioms on which the orthogonal splitting of positive
   semidefinite matrices (target T5 of phase 12) depends. `make check`
   compares the output with check/psd_splitting_assumptions.expected. The
   definition compiles only if psd_splitting_theorem proves the frozen
   statement psd_splitting_statement. *)
From GaussianApplications Require Import PsdSplittingStatement
  PsdSplittingTheorem.

Definition psd_splitting_theorem_checked :
  psd_splitting_statement := psd_splitting_theorem.

Print Assumptions psd_splitting_theorem.
