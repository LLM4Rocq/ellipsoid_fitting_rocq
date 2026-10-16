(* The axiom check of the fitting error and the quadric exclusion for
   symmetric product mixtures above the PSD threshold (target S5 of the
   shifted-Gaussian proof). The file only requires the frozen statement
   module and the theorem module, without Import, and names both by their
   absolute names, so that no name that the theorem module defines can
   stand for the frozen statement. The definition compiles only if
   shifted_mixture_unsat_theorem proves the frozen statement
   shifted_mixture_unsat_statement. The file then prints the full name of
   the definition and its axioms, which make check compares with
   check/shifted_mixture_unsat_assumptions.expected. *)
Require EllipsoidUniversality.ShiftedMixtureUnsatStatement.
Require EllipsoidUniversality.Shifted.MixtureUnsatTheorem.

Definition shifted_mixture_unsat_identity :
  EllipsoidUniversality.ShiftedMixtureUnsatStatement.shifted_mixture_unsat_statement :=
  EllipsoidUniversality.Shifted.MixtureUnsatTheorem.shifted_mixture_unsat_theorem.

Locate shifted_mixture_unsat_identity.
Print Assumptions shifted_mixture_unsat_identity.
