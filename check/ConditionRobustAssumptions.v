(* Prints the axioms on which the robustness of the optimal condition
   number depends. `make check` compares the output with
   check/condition_robust_assumptions.expected. The definition compiles
   only if robust_condition_theorem proves the frozen statement
   robust_condition_theorem_statement. *)
From EllipsoidUniversality Require Import ConditionRobustStatement ConditionRobustTheorem.

Definition robust_condition_theorem_checked :
  robust_condition_theorem_statement := robust_condition_theorem.

Print Assumptions robust_condition_theorem.
