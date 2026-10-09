(* Prints the axioms on which the countable-mixture theorem depends. `make
   check` compares the output with check/countable_assumptions.expected. The
   definition compiles only if countable_theorem proves the frozen statement
   countable_theorem_statement. *)
From EllipsoidUniversality Require Import CountableMixtureStatement CountableTheorem.

Definition countable_theorem_checked : countable_theorem_statement :=
  countable_theorem.

Print Assumptions countable_theorem.
