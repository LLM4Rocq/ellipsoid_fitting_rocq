(* Prints the axioms on which tensor packing in finite dimensions (target
   T2 of phase 12) depends. `make check` compares the output with
   check/tensor_packing_assumptions.expected. The definition compiles only
   if tensor_packing_theorem proves the frozen statement
   tensor_packing_statement. *)
From GaussianApplications Require Import TensorPackingStatement
  TensorPackingTheorem.

Definition tensor_packing_theorem_checked :
  tensor_packing_statement := tensor_packing_theorem.

Print Assumptions tensor_packing_theorem.
