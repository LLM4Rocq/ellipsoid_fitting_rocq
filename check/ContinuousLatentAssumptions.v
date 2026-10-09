(* Prints the axioms on which the continuous latent counterexample
   depends. `make check` compares the output with
   check/continuous_latent_assumptions.expected. The definition compiles
   only if continuous_latent_theorem proves the frozen statement
   continuous_latent_statement. *)
From EllipsoidUniversality Require Import ContinuousLatent ContinuousLatentTheorem.

Definition continuous_latent_theorem_checked : continuous_latent_statement :=
  continuous_latent_theorem.

Print Assumptions continuous_latent_theorem.
