(* Prints the axioms on which the spectral gap of the SK heat-bath dynamics
   for beta < 1/2 (target T4 of phase 12) depends. `make check` compares
   the output with check/sk_gap_assumptions.expected. The definition
   compiles only if sk_gap_theorem proves the frozen statement
   sk_gap_statement. *)
From GaussianApplications Require Import SKGapStatement SKGapTheorem.

Definition sk_gap_theorem_checked : sk_gap_statement := sk_gap_theorem.

Print Assumptions sk_gap_theorem.
