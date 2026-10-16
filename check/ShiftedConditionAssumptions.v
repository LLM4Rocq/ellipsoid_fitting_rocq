(* The axiom check of the condition thresholds and the optimal condition
   number for small deterministic Gaussian translations (target S1 of the
   shifted-Gaussian proof). The file only requires the frozen statement
   module and the theorem module, without Import, and names both by their
   absolute names, so that no name that the theorem module defines can
   stand for the frozen statement. The definition compiles only if
   shifted_condition_theorem proves the frozen statement
   shifted_condition_statement. The file then prints the full name of the
   definition and its axioms, which make check compares with
   check/shifted_condition_assumptions.expected. *)
Require EllipsoidUniversality.ShiftedConditionStatement.
Require EllipsoidUniversality.Shifted.ConditionTheorem.

Definition shifted_condition_identity :
  EllipsoidUniversality.ShiftedConditionStatement.shifted_condition_statement :=
  EllipsoidUniversality.Shifted.ConditionTheorem.shifted_condition_theorem.

Locate shifted_condition_identity.
Print Assumptions shifted_condition_identity.
