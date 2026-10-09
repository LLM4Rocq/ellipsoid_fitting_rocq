(* Prints the axioms on which the robustness results depend. `make check`
   compares the output with check/robust_assumptions.expected. The
   definition compiles only if robust_theorem proves the frozen statement
   robust_theorem_statement. *)
From EllipsoidUniversality Require Import RobustStatement RobustTheorem.

Definition robust_theorem_checked : robust_theorem_statement :=
  robust_theorem.

Print Assumptions robust_theorem.
