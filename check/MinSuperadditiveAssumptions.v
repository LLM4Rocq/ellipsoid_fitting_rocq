(* The axiom check of the convergence from approximate minimum inequalities
   (target T12 of phase 13). The file only requires the frozen statement
   module and the theorem module, without Import, and names both by their
   absolute names, so that no name that the theorem module defines can
   stand for the frozen statement. The definition compiles only if
   min_superadditive_theorem proves the frozen statement
   min_superadditive_statement. The file then prints the full name of the
   definition and its axioms, which make check compares with
   check/min_superadditive_assumptions.expected. *)
Require GaussianApplications.MinSuperadditiveStatement.
Require GaussianApplications.MinSuperadditiveTheorem.

Definition min_superadditive_identity :
  GaussianApplications.MinSuperadditiveStatement.min_superadditive_statement :=
  GaussianApplications.MinSuperadditiveTheorem.min_superadditive_theorem.

Locate min_superadditive_identity.
Print Assumptions min_superadditive_identity.
