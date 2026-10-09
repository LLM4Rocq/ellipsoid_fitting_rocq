(* Prints the axioms on which the tensorization bounds for the latent-sign
   law depend. `make check` compares the output with
   check/latent_tensor_assumptions.expected. The definition compiles only
   if latent_tensor_theorem proves the frozen statement
   latent_tensorization_statement. *)
From EllipsoidUniversality Require Import LatentTensorization LatentTensorTheorem.

Definition latent_tensor_theorem_checked : latent_tensorization_statement :=
  latent_tensor_theorem.

Print Assumptions latent_tensor_theorem.
