(* The identity driver of the statement snapshot SnapshotPhase14 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase14.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase14.json. *)

Require GaussianApplications.PsdLiftDefinitions.
Require GaussianApplications.PsdLiftStatement.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "GaussianApplications.PsdLiftDefinitions.kn_edges".
KernelIdentity "definition" "GaussianApplications.PsdLiftDefinitions.matching_slack_mx".
KernelIdentity "definition" "GaussianApplications.PsdLiftDefinitions.in_matching_polytope".
KernelIdentity "definition" "GaussianApplications.PsdLiftDefinitions.semidefinite_lift".
KernelIdentity "definition" "GaussianApplications.PsdLiftStatement.psd_lift_statement".
