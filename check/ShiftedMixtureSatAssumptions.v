(* The axiom check of the positive definite exact fitting for sparse
   deterministic shifts of product mixtures (target S6 of the
   shifted-Gaussian proof). The file only requires the frozen statement
   module and the theorem module, without Import, and names both by their
   absolute names, so that no name that the theorem module defines can
   stand for the frozen statement. The definition compiles only if
   shifted_mixture_sat_theorem proves the frozen statement
   shifted_mixture_sat_statement. The file then prints the full name of the
   definition and its axioms, which make check compares with
   check/shifted_mixture_sat_assumptions.expected. *)
Require EllipsoidUniversality.ShiftedMixtureSatStatement.
Require EllipsoidUniversality.Shifted.MixtureSatTheorem.

Definition shifted_mixture_sat_identity :
  EllipsoidUniversality.ShiftedMixtureSatStatement.shifted_mixture_sat_statement :=
  EllipsoidUniversality.Shifted.MixtureSatTheorem.shifted_mixture_sat_theorem.

Locate shifted_mixture_sat_identity.
Print Assumptions shifted_mixture_sat_identity.
