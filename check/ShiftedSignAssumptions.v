(* The axiom check of the exact opposite-shift mixture laws and their
   fitting consequences (target S7 of the shifted-Gaussian proof). The file
   only requires the frozen statement module and the theorem module,
   without Import, and names both by their absolute names, so that no name
   that the theorem module defines can stand for the frozen statement. The
   definition compiles only if shifted_sign_theorem proves the frozen
   statement shifted_sign_statement. The file then prints the full name of
   the definition and its axioms, which make check compares with
   check/shifted_sign_assumptions.expected. *)
Require EllipsoidUniversality.ShiftedSignStatement.
Require EllipsoidUniversality.Shifted.SignTheorem.

Definition shifted_sign_identity :
  EllipsoidUniversality.ShiftedSignStatement.shifted_sign_statement :=
  EllipsoidUniversality.Shifted.SignTheorem.shifted_sign_theorem.

Locate shifted_sign_identity.
Print Assumptions shifted_sign_identity.
