(* The identity driver of the statement snapshot SnapshotPhase10 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase10.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase10.json. *)

Require EllipsoidUniversality.ConditionRobustStatement.
Require EllipsoidUniversality.LatentTensorUpper.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "EllipsoidUniversality.ConditionRobustStatement.robust_condition_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionRobustStatement.robust_condition_number_statement".
KernelIdentity "definition" "EllipsoidUniversality.ConditionRobustStatement.robust_condition_theorem_statement".
KernelIdentity "definition" "EllipsoidUniversality.LatentTensorUpper.latent_tensor_constant".
KernelIdentity "definition" "EllipsoidUniversality.LatentTensorUpper.latent_tensor_upper_statement".
