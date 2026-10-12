(* Prints the axioms on which the curve of the optimal condition number at
   every fourth moment kappa > 1 depends. `make check` compares the output
   with check/condition_kappa_curve_assumptions.expected. The definition
   compiles only if condition_kappa_curve_theorem proves the frozen
   statement condition_kappa_curve_statement. *)
From EllipsoidUniversality Require Import ConditionKappaCurveStatement ConditionKappaCurveTheorem.

Definition condition_kappa_curve_theorem_checked :
  condition_kappa_curve_statement := condition_kappa_curve_theorem.

Print Assumptions condition_kappa_curve_theorem.
