(* Prints the axioms on which the condition-number theorem depends. `make
   check` compares the output with check/condition_assumptions.expected. The
   definition compiles only if condition_theorem proves the frozen statement
   condition_theorem_statement. *)
From EllipsoidUniversality Require Import ConditionStatement ConditionTheorem.

Definition condition_theorem_checked : condition_theorem_statement :=
  condition_theorem.

Print Assumptions condition_theorem.
