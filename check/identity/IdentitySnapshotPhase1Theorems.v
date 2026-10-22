(* The identity driver of the statement snapshot SnapshotPhase1Theorems (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase1Theorems.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase1Theorems.json. *)

Require EllipsoidFitting.PaperMainResults.
Require EllipsoidFitting.MainTheorem.
Declare ML Module "kernel_identity".

KernelIdentity "type" "EllipsoidFitting.PaperMainResults.paper_main_results".
KernelIdentity "type" "EllipsoidFitting.MainTheorem.ellipsoid_fitting_main".
