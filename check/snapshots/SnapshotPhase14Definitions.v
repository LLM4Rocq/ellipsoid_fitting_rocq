(* The statement snapshot SnapshotPhase14Definitions (scripts/check_sources.py, rule 30):
   the declarations accepted at 39f58468aeaa, printed in full. Written
   by scripts/snapshot_baselines.py; its reference, the output at that
   commit, is check/snapshots/SnapshotPhase14Definitions.txt. *)

Require Checks.Phase14Definitions.

Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 78.

Check Checks.Phase14Definitions.ksubset_characterization.
Check Checks.Phase14Definitions.ksubset_mx_characterization.
Check Checks.Phase14Definitions.perm_cut_characterization.
