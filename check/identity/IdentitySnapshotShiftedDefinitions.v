(* The identity driver of the statement snapshot SnapshotShiftedDefinitions (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotShiftedDefinitions.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotShiftedDefinitions.json. *)

Require Checks.ShiftedDefinitions.
Declare ML Module "kernel_identity".

KernelIdentity "type" "Checks.ShiftedDefinitions.family_sequence_limit_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.coordinate_support_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.quadric_eval_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.tuple_map_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.mixture_weights_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.mixture_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.cmixture_weights_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.cmixture_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.row_symmetric_law_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.row_shift_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.row_shift_law_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.sign_shift_weights_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.sign_shift_law_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.row_outer_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.row_of_tuple_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.point_law_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.sample_row_tuple_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.sample_flat_row_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.sample_flat_col_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.sample_of_row_tuple_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.sample_translate_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.translation_fitting_error_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.gaussian_small_shift_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.finite_row_law_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.countable_row_law_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.row_sample_map_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.iid_row_sample_law_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.shifted_iid_sample_law_characterization".
KernelIdentity "type" "Checks.ShiftedDefinitions.sign_mixture_sample_law_characterization".
