(* The identity driver of the statement snapshot SnapshotPhase8 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase8.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase8.json. *)

Require EllipsoidUniversality.CountableMixtureDefinitions.
Require EllipsoidUniversality.CountableMixtureStatement.
Require EllipsoidUniversality.ConditionDefinitions.
Require EllipsoidUniversality.ConditionStatement.
Require EllipsoidUniversality.LatentSignScope.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "EllipsoidUniversality.CountableMixtureDefinitions.countable_mixture_family".
KernelIdentity "definition" "EllipsoidUniversality.CountableMixtureDefinitions.countable_fourth_moment".
KernelIdentity "definition" "EllipsoidUniversality.CountableMixtureDefinitions.countable_labelled_law".
KernelIdentity "definition" "EllipsoidUniversality.CountableMixtureDefinitions.countable_mixture_probability".
KernelIdentity "definition" "EllipsoidUniversality.CountableMixtureStatement.countable_mixture_statement".
KernelIdentity "definition" "EllipsoidUniversality.CountableMixtureStatement.countable_interpolation_statement".
KernelIdentity "definition" "EllipsoidUniversality.CountableMixtureStatement.countable_theorem_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionDefinitions.condition_t".
KernelIdentity "definition" "EllipsoidUniversality.ConditionDefinitions.condition_alpha".
KernelIdentity "definition" "EllipsoidUniversality.ConditionDefinitions.condition_star".
KernelIdentity "definition" "EllipsoidUniversality.ConditionDefinitions.data_condition_number".
KernelIdentity "definition" "EllipsoidUniversality.ConditionStatement.condition_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionStatement.condition_number_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionStatement.countable_condition_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionStatement.countable_condition_number_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionStatement.condition_theorem_statement".
KernelIdentity "definition" "EllipsoidUniversality.LatentSignScope.latent_point_expectation".
KernelIdentity "definition" "EllipsoidUniversality.LatentSignScope.latent_covariance_statement".
KernelIdentity "definition" "EllipsoidUniversality.LatentSignScope.latent_variance_statement".
KernelIdentity "definition" "EllipsoidUniversality.LatentSignScope.latent_scope_statement".
