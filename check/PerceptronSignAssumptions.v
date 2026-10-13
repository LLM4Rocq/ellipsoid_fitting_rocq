(* Prints the axioms on which the sign/Gaussian comparison for the Ising
   perceptron pressure (target T6 of phase 12) depends. `make check`
   compares the output with check/perceptron_sign_assumptions.expected. The
   definition compiles only if perceptron_sign_theorem proves the frozen
   statement perceptron_sign_statement. *)
From GaussianApplications Require Import PerceptronSignStatement
  PerceptronSignTheorem.

Definition perceptron_sign_theorem_checked :
  perceptron_sign_statement := perceptron_sign_theorem.

Print Assumptions perceptron_sign_theorem.
