(* The statement snapshot SnapshotPhase13Freeze1 (scripts/check_sources.py, rule 30):
   the declarations accepted at c0d9cf0b0334, printed in full. Written
   by scripts/snapshot_baselines.py; its reference, the output at that
   commit, is check/snapshots/SnapshotPhase13Freeze1.txt. *)

Require Checks.Phase13Definitions.

Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 78.

Check Checks.Phase13Definitions.unif_mean_characterization.
Check Checks.Phase13Definitions.unif_var_characterization.
Check Checks.Phase13Definitions.binomial_mean_characterization.
Check Checks.Phase13Definitions.linear_op_characterization.
Check Checks.Phase13Definitions.monotone_op_characterization.
Check Checks.Phase13Definitions.meet_avg_characterization.
