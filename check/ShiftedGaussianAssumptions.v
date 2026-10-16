(* The axiom check of the condition numbers for arbitrary deterministic
   Gaussian translations (target S2 of the shifted-Gaussian proof). The
   file only requires the frozen statement module and the theorem module,
   without Import, and names both by their absolute names, so that no name
   that the theorem module defines can stand for the frozen statement. The
   definition compiles only if shifted_gaussian_theorem proves the frozen
   statement shifted_gaussian_statement. The file then prints the full name
   of the definition and its axioms, which make check compares with
   check/shifted_gaussian_assumptions.expected. *)
Require EllipsoidUniversality.ShiftedGaussianStatement.
Require EllipsoidUniversality.Shifted.GaussianTheorem.

Definition shifted_gaussian_identity :
  EllipsoidUniversality.ShiftedGaussianStatement.shifted_gaussian_statement :=
  EllipsoidUniversality.Shifted.GaussianTheorem.shifted_gaussian_theorem.

Locate shifted_gaussian_identity.
Print Assumptions shifted_gaussian_identity.
