(* The axiom check of the Gaussian quadric exclusion (target S3 of the
   shifted-Gaussian proof). The file only requires the frozen statement
   module and the theorem module, without Import, and names both by their
   absolute names, so that no name that the theorem module defines can
   stand for the frozen statement. The definition compiles only if
   shifted_quadric_theorem proves the frozen statement
   shifted_quadric_statement. The file then prints the full name of the
   definition and its axioms, which make check compares with
   check/shifted_quadric_assumptions.expected. *)
Require EllipsoidUniversality.ShiftedQuadricStatement.
Require EllipsoidUniversality.Shifted.QuadricTheorem.

Definition shifted_quadric_identity :
  EllipsoidUniversality.ShiftedQuadricStatement.shifted_quadric_statement :=
  EllipsoidUniversality.Shifted.QuadricTheorem.shifted_quadric_theorem.

Locate shifted_quadric_identity.
Print Assumptions shifted_quadric_identity.
