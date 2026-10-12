(* Prints the axioms on which the robustness of the threshold and of the
   optimal condition number at every fourth moment kappa > 1 depends.
   `make check` compares the output with
   check/condition_kappa_robust_assumptions.expected. The definition
   compiles only if condition_kappa_robust_theorem proves the frozen
   statement condition_kappa_robust_theorem_statement. *)
From EllipsoidUniversality Require Import ConditionKappaRobustStatement ConditionKappaRobustTheorem.

Definition condition_kappa_robust_theorem_checked :
  condition_kappa_robust_theorem_statement := condition_kappa_robust_theorem.

Print Assumptions condition_kappa_robust_theorem.
