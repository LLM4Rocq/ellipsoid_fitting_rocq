(* The statement snapshot SnapshotMatrixSigmaRing (scripts/check_sources.py, rule 30):
   the characterization of check/MatrixSigmaRing.v, accepted on 15
   October 2026, printed in full against the library at b6173f138f14.
   Written by scripts/snapshot_baselines.py; its reference, the output
   at that commit, is check/snapshots/SnapshotMatrixSigmaRing.txt. *)

Require Checks.MatrixSigmaRing.

Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 78.

Check Checks.MatrixSigmaRing.matrix_sigma_ring_characterization.
