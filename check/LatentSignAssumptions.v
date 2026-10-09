(* Prints the axioms on which the latent-sign theorem depends. `make check`
   compares the output with check/latent_sign_assumptions.expected. The
   definition compiles only if latent_sign_theorem proves the frozen
   statement latent_sign_statement. *)
From EllipsoidUniversality Require Import LatentSignStatement LatentSignTheorem.

Definition latent_sign_theorem_checked : latent_sign_statement :=
  latent_sign_theorem.

Print Assumptions latent_sign_theorem.
