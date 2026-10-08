(* Prints the axioms on which the finite-mixture theorem depends. `make check`
   compares the output with check/mixture_assumptions.expected. The
   definition compiles only if mixture_theorem proves the frozen statement
   mixture_theorem_statement. *)
From EllipsoidUniversality Require Import MixtureStatement MixtureTheorem.

Definition mixture_theorem_checked : mixture_theorem_statement :=
  mixture_theorem.

Print Assumptions mixture_theorem.
