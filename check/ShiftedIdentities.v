(* The joint axiom check of the seven theorems of the shifted-Gaussian
   proof (targets S1 to S7). The file only requires the seven frozen
   statement modules and the seven theorem modules, without Import, and
   names all of them by their absolute names, so that no name that a
   theorem module defines can stand for a frozen statement. Each definition
   shifted_<x>_identity compiles only if shifted_<x>_theorem proves the
   frozen statement shifted_<x>_statement, and shifted_identities, whose
   type is the conjunction of the seven frozen statements, bundles the
   seven. The file prints, after each of the eight definitions, its full
   name (Locate), then its axioms, which the checker compares with the
   seven axioms of check/sat_variance_assumptions.expected. Its code is
   fixed by scripts/check_sources.py, which starts scripts/run_checks.py to
   compile it. *)
Require EllipsoidUniversality.ShiftedConditionStatement.
Require EllipsoidUniversality.Shifted.ConditionTheorem.
Require EllipsoidUniversality.ShiftedGaussianStatement.
Require EllipsoidUniversality.Shifted.GaussianTheorem.
Require EllipsoidUniversality.ShiftedQuadricStatement.
Require EllipsoidUniversality.Shifted.QuadricTheorem.
Require EllipsoidUniversality.ShiftedErrorStatement.
Require EllipsoidUniversality.Shifted.ErrorTheorem.
Require EllipsoidUniversality.ShiftedMixtureUnsatStatement.
Require EllipsoidUniversality.Shifted.MixtureUnsatTheorem.
Require EllipsoidUniversality.ShiftedMixtureSatStatement.
Require EllipsoidUniversality.Shifted.MixtureSatTheorem.
Require EllipsoidUniversality.ShiftedSignStatement.
Require EllipsoidUniversality.Shifted.SignTheorem.

Definition shifted_condition_identity :
  EllipsoidUniversality.ShiftedConditionStatement.shifted_condition_statement :=
  EllipsoidUniversality.Shifted.ConditionTheorem.shifted_condition_theorem.
Locate shifted_condition_identity.
Print Assumptions shifted_condition_identity.

Definition shifted_gaussian_identity :
  EllipsoidUniversality.ShiftedGaussianStatement.shifted_gaussian_statement :=
  EllipsoidUniversality.Shifted.GaussianTheorem.shifted_gaussian_theorem.
Locate shifted_gaussian_identity.
Print Assumptions shifted_gaussian_identity.

Definition shifted_quadric_identity :
  EllipsoidUniversality.ShiftedQuadricStatement.shifted_quadric_statement :=
  EllipsoidUniversality.Shifted.QuadricTheorem.shifted_quadric_theorem.
Locate shifted_quadric_identity.
Print Assumptions shifted_quadric_identity.

Definition shifted_error_identity :
  EllipsoidUniversality.ShiftedErrorStatement.shifted_error_statement :=
  EllipsoidUniversality.Shifted.ErrorTheorem.shifted_error_theorem.
Locate shifted_error_identity.
Print Assumptions shifted_error_identity.

Definition shifted_mixture_unsat_identity :
  EllipsoidUniversality.ShiftedMixtureUnsatStatement.shifted_mixture_unsat_statement :=
  EllipsoidUniversality.Shifted.MixtureUnsatTheorem.shifted_mixture_unsat_theorem.
Locate shifted_mixture_unsat_identity.
Print Assumptions shifted_mixture_unsat_identity.

Definition shifted_mixture_sat_identity :
  EllipsoidUniversality.ShiftedMixtureSatStatement.shifted_mixture_sat_statement :=
  EllipsoidUniversality.Shifted.MixtureSatTheorem.shifted_mixture_sat_theorem.
Locate shifted_mixture_sat_identity.
Print Assumptions shifted_mixture_sat_identity.

Definition shifted_sign_identity :
  EllipsoidUniversality.ShiftedSignStatement.shifted_sign_statement :=
  EllipsoidUniversality.Shifted.SignTheorem.shifted_sign_theorem.
Locate shifted_sign_identity.
Print Assumptions shifted_sign_identity.

Definition shifted_identities :
  EllipsoidUniversality.ShiftedConditionStatement.shifted_condition_statement /\
  EllipsoidUniversality.ShiftedGaussianStatement.shifted_gaussian_statement /\
  EllipsoidUniversality.ShiftedQuadricStatement.shifted_quadric_statement /\
  EllipsoidUniversality.ShiftedErrorStatement.shifted_error_statement /\
  EllipsoidUniversality.ShiftedMixtureUnsatStatement.shifted_mixture_unsat_statement /\
  EllipsoidUniversality.ShiftedMixtureSatStatement.shifted_mixture_sat_statement /\
  EllipsoidUniversality.ShiftedSignStatement.shifted_sign_statement :=
  conj shifted_condition_identity
    (conj shifted_gaussian_identity
      (conj shifted_quadric_identity
        (conj shifted_error_identity
          (conj shifted_mixture_unsat_identity
            (conj shifted_mixture_sat_identity shifted_sign_identity))))).

Locate shifted_identities.
Print Assumptions shifted_identities.
