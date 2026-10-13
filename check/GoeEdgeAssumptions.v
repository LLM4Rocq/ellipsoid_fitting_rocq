(* Prints the axioms on which the sharp upper edge of the GOE (target T3 of
   phase 12) depends. `make check` compares the output with
   check/goe_edge_assumptions.expected. The definition compiles only if
   goe_edge_theorem proves the frozen statement goe_edge_statement. *)
From GaussianApplications Require Import GoeEdgeStatement GoeEdgeTheorem.

Definition goe_edge_theorem_checked : goe_edge_statement := goe_edge_theorem.

Print Assumptions goe_edge_theorem.
