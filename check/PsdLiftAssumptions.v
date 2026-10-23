(* The axiom check of the corollary on unshifted matching matrices and
   exact semidefinite lifts (target T14 of phase 14). The file only
   requires the frozen statement module and the theorem module, without
   Import, and names both by their absolute names, so that no name that
   the theorem module defines can stand for the frozen statement. The
   definition compiles only if psd_lift_theorem proves the frozen statement
   psd_lift_statement. The file then prints the full name of the definition
   and its axioms, which make check compares with
   check/psd_lift_assumptions.expected. *)
Require GaussianApplications.PsdLiftStatement.
Require GaussianApplications.PsdLiftTheorem.

Definition psd_lift_identity :
  GaussianApplications.PsdLiftStatement.psd_lift_statement :=
  GaussianApplications.PsdLiftTheorem.psd_lift_theorem.

Locate psd_lift_identity.
Print Assumptions psd_lift_identity.
