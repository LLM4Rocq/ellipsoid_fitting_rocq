(* Prints the axioms on which the scope results on the latent-sign law
   depend. `make check` compares the output with
   check/latent_scope_assumptions.expected. The definition compiles only if
   latent_scope_theorem proves the frozen statement latent_scope_statement. *)
From EllipsoidUniversality Require Import LatentSignScope LatentScopeTheorem.

Definition latent_scope_theorem_checked : latent_scope_statement :=
  latent_scope_theorem.

Print Assumptions latent_scope_theorem.
