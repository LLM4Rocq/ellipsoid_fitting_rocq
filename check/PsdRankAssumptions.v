(* The axiom check of the exponential PSD rank of the shifted matching
   matrices (target T13 of phase 14). The file only requires the frozen
   statement module and the theorem module, without Import, and names both
   by their absolute names, so that no name that the theorem module defines
   can stand for the frozen statement. The definition compiles only if
   psd_rank_theorem proves the frozen statement psd_rank_statement. The
   file then prints the full name of the definition and its axioms, which
   make check compares with check/psd_rank_assumptions.expected. *)
Require GaussianApplications.PsdRankStatement.
Require GaussianApplications.PsdRankTheorem.

Definition psd_rank_identity :
  GaussianApplications.PsdRankStatement.psd_rank_statement :=
  GaussianApplications.PsdRankTheorem.psd_rank_theorem.

Locate psd_rank_identity.
Print Assumptions psd_rank_identity.
