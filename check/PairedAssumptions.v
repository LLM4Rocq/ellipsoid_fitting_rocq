(* Prints the axioms on which the paired-law theorem depends. `make check`
   compares the output with check/paired_assumptions.expected. The
   definition compiles only if paired_theorem proves the frozen statement
   paired_statement. *)
From EllipsoidUniversality Require Import PairedStatement PairedTheorem.

Definition paired_theorem_checked : paired_statement := paired_theorem.

Print Assumptions paired_theorem.
