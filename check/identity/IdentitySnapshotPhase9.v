(* The identity driver of the statement snapshot SnapshotPhase9 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase9.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase9.json. *)

Require EllipsoidUniversality.RobustDefinitions.
Require EllipsoidUniversality.RobustStatement.
Require EllipsoidUniversality.LatentTensorization.
Require EllipsoidUniversality.ContinuousLatent.
Require EllipsoidUniversality.ConditionEndpoints.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "EllipsoidUniversality.RobustDefinitions.robust_point_law".
KernelIdentity "definition" "EllipsoidUniversality.RobustDefinitions.finite_weights".
KernelIdentity "definition" "EllipsoidUniversality.RobustDefinitions.robust_tv".
KernelIdentity "definition" "EllipsoidUniversality.RobustDefinitions.robust_points".
KernelIdentity "definition" "EllipsoidUniversality.RobustDefinitions.robust_sample_law".
KernelIdentity "definition" "EllipsoidUniversality.RobustDefinitions.robust_close".
KernelIdentity "definition" "EllipsoidUniversality.RobustDefinitions.contaminated_weights".
KernelIdentity "definition" "EllipsoidUniversality.RobustDefinitions.contaminated_laws".
KernelIdentity "definition" "EllipsoidUniversality.RobustStatement.robust_statement".
KernelIdentity "definition" "EllipsoidUniversality.RobustStatement.robust_interpolation_statement".
KernelIdentity "definition" "EllipsoidUniversality.RobustStatement.contamination_statement".
KernelIdentity "definition" "EllipsoidUniversality.RobustStatement.robust_theorem_statement".
KernelIdentity "definition" "EllipsoidUniversality.LatentTensorization.latent_replace".
KernelIdentity "definition" "EllipsoidUniversality.LatentTensorization.latent_cond_expectation".
KernelIdentity "definition" "EllipsoidUniversality.LatentTensorization.latent_cond_variance".
KernelIdentity "definition" "EllipsoidUniversality.LatentTensorization.latent_variance".
KernelIdentity "definition" "EllipsoidUniversality.LatentTensorization.latent_tensorization".
KernelIdentity "definition" "EllipsoidUniversality.LatentTensorization.latent_tensorization_statement".
KernelIdentity "definition" "EllipsoidUniversality.ContinuousLatent.cl_value".
KernelIdentity "definition" "EllipsoidUniversality.ContinuousLatent.cl_weight".
KernelIdentity "definition" "EllipsoidUniversality.ContinuousLatent.cl_moment".
KernelIdentity "definition" "EllipsoidUniversality.ContinuousLatent.cl_point_law".
KernelIdentity "definition" "EllipsoidUniversality.ContinuousLatent.continuous_latent_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionEndpoints.condition_alpha_near_one".
KernelIdentity "definition" "EllipsoidUniversality.ConditionEndpoints.condition_alpha_near_infinity".
KernelIdentity "definition" "EllipsoidUniversality.ConditionEndpoints.condition_star_near_zero".
KernelIdentity "definition" "EllipsoidUniversality.ConditionEndpoints.condition_star_near_quarter".
KernelIdentity "definition" "EllipsoidUniversality.ConditionEndpoints.condition_endpoints_statement".
