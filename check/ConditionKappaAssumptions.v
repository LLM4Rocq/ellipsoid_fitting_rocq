(* Prints the axioms on which the threshold and the optimal condition
   number at every fourth moment kappa > 1 depend. `make check` compares
   the output with check/condition_kappa_assumptions.expected. The
   definition compiles only if condition_kappa_theorem proves the frozen
   statement condition_kappa_theorem_statement. *)
From EllipsoidUniversality Require Import ConditionKappaStatement ConditionKappaTheorem.

Definition condition_kappa_theorem_checked :
  condition_kappa_theorem_statement := condition_kappa_theorem.

Print Assumptions condition_kappa_theorem.
