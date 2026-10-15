(* The axiom check of the product smoothing of matrix squares (target T11
   of phase 13). The file only requires the frozen statement module and the
   theorem module, without Import, and names both by their absolute names,
   so that no name that the theorem module defines can stand for the frozen
   statement. The definition compiles only if product_smoothing_theorem
   proves the frozen statement product_smoothing_statement. The file then
   prints the full name of the definition and its axioms, which make check
   compares with check/product_smoothing_assumptions.expected. *)
Require GaussianApplications.ProductSmoothingStatement.
Require GaussianApplications.ProductSmoothingTheorem.

Definition product_smoothing_identity :
  GaussianApplications.ProductSmoothingStatement.product_smoothing_statement :=
  GaussianApplications.ProductSmoothingTheorem.product_smoothing_theorem.

Locate product_smoothing_identity.
Print Assumptions product_smoothing_identity.
