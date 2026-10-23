(* The identity checks of the two theorems of phase 14, beside those of
   check/TheoremIdentities.v, which is pinned. For each,
   <theorem>_identity has the frozen statement as its type and the theorem
   as its body, both named by their absolute names, and the file only
   Requires, without Import: no name that a theorem module or a library
   module defines can stand for a frozen statement. The file prints the
   full name of each identity definition (Locate), then its axioms. Its
   code is fixed by scripts/check_sources.py, which starts
   scripts/run_checks.py to compile it. *)

Require GaussianApplications.PsdRankStatement GaussianApplications.PsdRankTheorem.
Require GaussianApplications.PsdLiftStatement GaussianApplications.PsdLiftTheorem.

Definition psd_rank_theorem_identity :
  GaussianApplications.PsdRankStatement.psd_rank_statement :=
  GaussianApplications.PsdRankTheorem.psd_rank_theorem.
Locate psd_rank_theorem_identity.
Print Assumptions psd_rank_theorem_identity.

Definition psd_lift_theorem_identity :
  GaussianApplications.PsdLiftStatement.psd_lift_statement :=
  GaussianApplications.PsdLiftTheorem.psd_lift_theorem.
Locate psd_lift_theorem_identity.
Print Assumptions psd_lift_theorem_identity.
