(* The identity driver of the statement snapshot SnapshotMatrixSigmaRing (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotMatrixSigmaRing.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotMatrixSigmaRing.json. *)

Require Checks.MatrixSigmaRing.
Declare ML Module "kernel_identity".

KernelIdentity "type" "Checks.MatrixSigmaRing.matrix_sigma_ring_characterization".
