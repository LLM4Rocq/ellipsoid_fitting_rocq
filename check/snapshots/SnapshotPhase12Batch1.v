(* The statement snapshot SnapshotPhase12Batch1 (scripts/check_sources.py, rule 30):
   the declarations accepted at fc76edfc953c, printed in full. Written
   by scripts/snapshot_baselines.py; its reference, the output at that
   commit, is check/snapshots/SnapshotPhase12Batch1.txt. *)

Require GaussianApplications.MatrixSeriesStatement.
Require GaussianApplications.GoeEdgeStatement.
Require GaussianApplications.PsdSplittingStatement.
Require GaussianAnalysis.matrix.lambda_max.

Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 78.

Print Module GaussianApplications.MatrixSeriesStatement.
Print GaussianApplications.MatrixSeriesStatement.matrix_series_statement.
Print Module GaussianApplications.GoeEdgeStatement.
Print GaussianApplications.GoeEdgeStatement.goe_edge_statement.
Print Module GaussianApplications.PsdSplittingStatement.
Print GaussianApplications.PsdSplittingStatement.psd_splitting_statement.
Print GaussianAnalysis.matrix.lambda_max.lambda_max.
