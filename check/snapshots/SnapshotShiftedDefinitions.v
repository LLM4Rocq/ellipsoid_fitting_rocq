(* The statement snapshot SnapshotShiftedDefinitions (scripts/check_sources.py, rule 30):
   the characterizations of check/ShiftedDefinitions.v, which protect
   the definitions that the seven shifted statement files accepted at
   51c2e14d5c2d unfold to, printed in full against the library at
   7c370d9c2c5c, where the file was written. Written by
   scripts/snapshot_baselines.py; its reference, the output at that
   commit, is check/snapshots/SnapshotShiftedDefinitions.txt. *)

Require Checks.ShiftedDefinitions.

Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 78.

Check Checks.ShiftedDefinitions.family_sequence_limit_characterization.
Check Checks.ShiftedDefinitions.coordinate_support_characterization.
Check Checks.ShiftedDefinitions.quadric_eval_characterization.
Check Checks.ShiftedDefinitions.tuple_map_characterization.
Check Checks.ShiftedDefinitions.mixture_weights_characterization.
Check Checks.ShiftedDefinitions.mixture_characterization.
Check Checks.ShiftedDefinitions.cmixture_weights_characterization.
Check Checks.ShiftedDefinitions.cmixture_characterization.
Check Checks.ShiftedDefinitions.row_symmetric_law_characterization.
Check Checks.ShiftedDefinitions.row_shift_characterization.
Check Checks.ShiftedDefinitions.row_shift_law_characterization.
Check Checks.ShiftedDefinitions.sign_shift_weights_characterization.
Check Checks.ShiftedDefinitions.sign_shift_law_characterization.
Check Checks.ShiftedDefinitions.row_outer_characterization.
Check Checks.ShiftedDefinitions.row_of_tuple_characterization.
Check Checks.ShiftedDefinitions.point_law_characterization.
Check Checks.ShiftedDefinitions.sample_row_tuple_characterization.
Check Checks.ShiftedDefinitions.sample_flat_row_characterization.
Check Checks.ShiftedDefinitions.sample_flat_col_characterization.
Check Checks.ShiftedDefinitions.sample_of_row_tuple_characterization.
Check Checks.ShiftedDefinitions.sample_translate_characterization.
Check Checks.ShiftedDefinitions.translation_fitting_error_characterization.
Check Checks.ShiftedDefinitions.gaussian_small_shift_characterization.
Check Checks.ShiftedDefinitions.finite_row_law_characterization.
Check Checks.ShiftedDefinitions.countable_row_law_characterization.
Check Checks.ShiftedDefinitions.row_sample_map_characterization.
Check Checks.ShiftedDefinitions.iid_row_sample_law_characterization.
Check Checks.ShiftedDefinitions.shifted_iid_sample_law_characterization.
Check Checks.ShiftedDefinitions.sign_mixture_sample_law_characterization.
