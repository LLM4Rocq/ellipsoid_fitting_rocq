(* Prints the axioms on which the finite tensorization constant of the
   latent-sign law depends. `make check` compares the output with
   check/latent_tensor_upper_assumptions.expected. The definition compiles
   only if latent_tensor_upper_theorem proves the frozen statement
   latent_tensor_upper_statement. *)
From EllipsoidUniversality Require Import LatentTensorUpper LatentTensorUpperTheorem.

Definition latent_tensor_upper_theorem_checked :
  latent_tensor_upper_statement := latent_tensor_upper_theorem.

Print Assumptions latent_tensor_upper_theorem.
