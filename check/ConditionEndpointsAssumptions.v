(* Prints the axioms on which the endpoint expansions of the
   condition-number curve depend. `make check` compares the output with
   check/condition_endpoints_assumptions.expected. The definition compiles
   only if condition_endpoints_theorem proves the frozen statement
   condition_endpoints_statement. *)
From EllipsoidUniversality Require Import ConditionEndpoints ConditionEndpointsTheorem.

Definition condition_endpoints_theorem_checked :
  condition_endpoints_statement := condition_endpoints_theorem.

Print Assumptions condition_endpoints_theorem.
