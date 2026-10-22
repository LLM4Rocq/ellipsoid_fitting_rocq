(* The identity driver of the statement snapshot SnapshotApplicationsDefinitions (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotApplicationsDefinitions.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotApplicationsDefinitions.json. *)

Require Checks.ApplicationsDefinitions.
Declare ML Module "kernel_identity".

KernelIdentity "type" "Checks.ApplicationsDefinitions.mxdot_characterization".
KernelIdentity "type" "Checks.ApplicationsDefinitions.frobenius_characterization".
KernelIdentity "type" "Checks.ApplicationsDefinitions.opnorm_characterization".
KernelIdentity "type" "Checks.ApplicationsDefinitions.psdmx_characterization".
KernelIdentity "type" "Checks.ApplicationsDefinitions.goe_mx_characterization".
KernelIdentity "type" "Checks.ApplicationsDefinitions.matrix_measurable_characterization".
KernelIdentity "type" "Checks.ApplicationsDefinitions.gauss_characterization".
KernelIdentity "type" "Checks.ApplicationsDefinitions.gauss_determined".
