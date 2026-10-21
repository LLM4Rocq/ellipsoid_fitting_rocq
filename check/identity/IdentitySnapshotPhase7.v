(* The identity driver of the statement snapshot SnapshotPhase7 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase7.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase7.json. *)

Require EllipsoidUniversality.LatentSignDefinitions.
Require EllipsoidUniversality.LatentSignStatement.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "EllipsoidUniversality.LatentSignDefinitions.latent_sample_density".
KernelIdentity "definition" "EllipsoidUniversality.LatentSignDefinitions.latent_probability".
KernelIdentity "definition" "EllipsoidUniversality.LatentSignStatement.latent_sign_statement".
