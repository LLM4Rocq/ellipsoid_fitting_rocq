(* The identity driver of the statement snapshot SnapshotPhase12Batch1 (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase12Batch1.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase12Batch1.json. *)

Require GaussianApplications.MatrixSeriesStatement.
Require GaussianApplications.GoeEdgeStatement.
Require GaussianApplications.PsdSplittingStatement.
Require GaussianAnalysis.matrix.lambda_max.
Declare ML Module "kernel_identity".

KernelIdentity "definition" "GaussianApplications.MatrixSeriesStatement.matrix_series_statement".
KernelIdentity "definition" "GaussianApplications.GoeEdgeStatement.goe_edge_statement".
KernelIdentity "definition" "GaussianApplications.PsdSplittingStatement.psd_splitting_statement".
KernelIdentity "definition" "GaussianAnalysis.matrix.lambda_max.lambda_max".
