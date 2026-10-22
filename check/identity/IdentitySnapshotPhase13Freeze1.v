(* The identity driver of the statement snapshot SnapshotPhase13Freeze1 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase13Freeze1.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase13Freeze1.json. *)

Require Checks.Phase13Definitions.
Declare ML Module "kernel_identity".

KernelIdentity "type" "Checks.Phase13Definitions.unif_mean_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.unif_var_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.binomial_mean_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.linear_op_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.monotone_op_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.meet_avg_characterization".
