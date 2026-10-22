(* The identity driver of the statement snapshot SnapshotPhase13Freeze2 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase13Freeze2.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase13Freeze2.json. *)

Require Checks.Phase13Definitions.
Declare ML Module "kernel_identity".

KernelIdentity "type" "Checks.Phase13Definitions.unif_mean_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.unif_var_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.binomial_mean_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.linear_op_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.monotone_op_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.meet_avg_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.bdot_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.bchar_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.blk_deg_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.blk_dist_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.fcoef_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.low_blk_deg_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.prob_vec_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.prod_avg_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.smoothing_hyps_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.weighted_gram_characterization".
KernelIdentity "type" "Checks.Phase13Definitions.psd_factorization_characterization".
