(* Prints the axioms on which the universality theorem depends. `make check`
   compares the output with check/universality_assumptions.expected. The
   definition compiles only if universality_theorem proves the frozen
   statement universality_statement. *)
From EllipsoidUniversality Require Import UniversalityStatement UniversalityTheorem.

Definition universality_theorem_checked : universality_statement :=
  universality_theorem.

Print Assumptions universality_theorem.
