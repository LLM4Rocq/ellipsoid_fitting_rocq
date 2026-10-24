(* The identity driver of the statement snapshot SnapshotShifted (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotShifted.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotShifted.json. *)

Require EllipsoidUniversality.ShiftedConditionStatement.
Require EllipsoidUniversality.ShiftedGaussianStatement.
Require EllipsoidUniversality.ShiftedQuadricStatement.
Require EllipsoidUniversality.ShiftedErrorStatement.
Require EllipsoidUniversality.ShiftedMixtureUnsatStatement.
Require EllipsoidUniversality.ShiftedMixtureSatStatement.
Require EllipsoidUniversality.ShiftedSignStatement.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "EllipsoidUniversality.ShiftedConditionStatement.shifted_condition_measurability_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedConditionStatement.shifted_condition_threshold_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedConditionStatement.shifted_condition_number_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedConditionStatement.shifted_condition_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedGaussianStatement.shifted_gaussian_measurability_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedGaussianStatement.shifted_gaussian_uniform_lower_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedGaussianStatement.shifted_gaussian_bounds_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedGaussianStatement.shifted_gaussian_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedQuadricStatement.shifted_quadric_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedErrorStatement.shifted_error_measurable_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedErrorStatement.shifted_error_limit_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedErrorStatement.shifted_error_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedMixtureUnsatStatement.finite_shifted_mixture_unsat_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedMixtureUnsatStatement.countable_shifted_mixture_unsat_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedMixtureUnsatStatement.shifted_mixture_unsat_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedMixtureSatStatement.finite_shifted_mixture_sat_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedMixtureSatStatement.countable_shifted_mixture_sat_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedMixtureSatStatement.shifted_mixture_sat_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedSignStatement.shifted_sign_outer_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedSignStatement.shifted_sign_observables_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedSignStatement.shifted_sign_gaussian_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedSignStatement.shifted_sign_mixture_statement".
KernelIdentity "definition" "EllipsoidUniversality.ShiftedSignStatement.shifted_sign_statement".
