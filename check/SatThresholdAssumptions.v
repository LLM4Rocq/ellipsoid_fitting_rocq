(* The axiom check of the satisfiability threshold of random k-SAT (target
   T9 of phase 13). The file only requires the frozen statement module and
   the theorem module, without Import, and names both by their absolute
   names, so that no name that the theorem module defines can stand for the
   frozen statement. The definition compiles only if sat_threshold_theorem
   proves the frozen statement sat_threshold_statement. The file then
   prints the full name of the definition and its axioms, which make check
   compares with check/sat_threshold_assumptions.expected. *)
Require GaussianApplications.SatThresholdStatement.
Require GaussianApplications.SatThresholdTheorem.

Definition sat_threshold_identity :
  GaussianApplications.SatThresholdStatement.sat_threshold_statement :=
  GaussianApplications.SatThresholdTheorem.sat_threshold_theorem.

Locate sat_threshold_identity.
Print Assumptions sat_threshold_identity.
