(* The statement snapshot SnapshotPhase1Theorems (scripts/check_sources.py, rule 30):
   the declarations accepted at 29df54e436f0, printed in full. Written
   by scripts/snapshot_baselines.py; its reference, the output at that
   commit, is check/snapshots/SnapshotPhase1Theorems.txt. *)

Require EllipsoidFitting.PaperMainResults.
Require EllipsoidFitting.MainTheorem.

Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 78.

Print Module EllipsoidFitting.PaperMainResults.
Check EllipsoidFitting.PaperMainResults.paper_main_results.
Print Module EllipsoidFitting.MainTheorem.
Check EllipsoidFitting.MainTheorem.ellipsoid_fitting_main.
