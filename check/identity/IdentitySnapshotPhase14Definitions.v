(* The identity driver of the statement snapshot SnapshotPhase14Definitions (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase14Definitions.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase14Definitions.json. *)

Require Checks.Phase14Definitions.
Declare ML Module "kernel_identity".

KernelIdentity "type" "Checks.Phase14Definitions.ksubset_characterization".
KernelIdentity "type" "Checks.Phase14Definitions.ksubset_mx_characterization".
KernelIdentity "type" "Checks.Phase14Definitions.perm_cut_characterization".
