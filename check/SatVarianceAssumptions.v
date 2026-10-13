(* Prints the axioms on which the capped variance bound for random k-SAT
   (target T7 of phase 12) depends. `make check` compares the output with
   check/sat_variance_assumptions.expected. The definition compiles only if
   sat_variance_theorem proves the frozen statement sat_variance_statement. *)
From GaussianApplications Require Import SatVarianceStatement
  SatVarianceTheorem.

Definition sat_variance_theorem_checked :
  sat_variance_statement := sat_variance_theorem.

Print Assumptions sat_variance_theorem.
