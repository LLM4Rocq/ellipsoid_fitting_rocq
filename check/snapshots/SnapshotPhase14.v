(* The statement snapshot SnapshotPhase14 (scripts/check_sources.py, rule 30):
   the declarations accepted at 39f58468aeaa, printed in full. Written
   by scripts/snapshot_baselines.py; its reference, the output at that
   commit, is check/snapshots/SnapshotPhase14.txt. *)

Require GaussianApplications.PsdLiftDefinitions.
Require GaussianApplications.PsdLiftStatement.

Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 78.

Print Module GaussianApplications.PsdLiftDefinitions.
Print GaussianApplications.PsdLiftDefinitions.kn_edges.
Print GaussianApplications.PsdLiftDefinitions.matching_slack_mx.
Print GaussianApplications.PsdLiftDefinitions.in_matching_polytope.
Print GaussianApplications.PsdLiftDefinitions.semidefinite_lift.
Print Module GaussianApplications.PsdLiftStatement.
Print GaussianApplications.PsdLiftStatement.psd_lift_statement.
