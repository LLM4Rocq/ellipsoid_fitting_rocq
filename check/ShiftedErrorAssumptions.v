(* The axiom check of the Gaussian fitting error under arbitrary
   deterministic shifts (target S4 of the shifted-Gaussian proof). The file
   only requires the frozen statement module and the theorem module,
   without Import, and names both by their absolute names, so that no name
   that the theorem module defines can stand for the frozen statement. The
   definition compiles only if shifted_error_theorem proves the frozen
   statement shifted_error_statement. The file then prints the full name of
   the definition and its axioms, which make check compares with
   check/shifted_error_assumptions.expected. *)
Require EllipsoidUniversality.ShiftedErrorStatement.
Require EllipsoidUniversality.Shifted.ErrorTheorem.

Definition shifted_error_identity :
  EllipsoidUniversality.ShiftedErrorStatement.shifted_error_statement :=
  EllipsoidUniversality.Shifted.ErrorTheorem.shifted_error_theorem.

Locate shifted_error_identity.
Print Assumptions shifted_error_identity.
