(* The statement snapshot SnapshotPhase10 (scripts/check_sources.py, rule 30):
   the declarations accepted at b26eb1e0eff3, printed in full. Written
   by scripts/snapshot_baselines.py; its reference, the output at that
   commit, is check/snapshots/SnapshotPhase10.txt. *)

Require EllipsoidUniversality.ConditionRobustStatement.
Require EllipsoidUniversality.LatentTensorUpper.

Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 78.

Print Module EllipsoidUniversality.ConditionRobustStatement.
Print EllipsoidUniversality.ConditionRobustStatement.robust_condition_statement.
Print EllipsoidUniversality.ConditionRobustStatement.robust_condition_number_statement.
Print EllipsoidUniversality.ConditionRobustStatement.robust_condition_theorem_statement.
Print Module EllipsoidUniversality.LatentTensorUpper.
Print EllipsoidUniversality.LatentTensorUpper.latent_tensor_constant.
Print EllipsoidUniversality.LatentTensorUpper.latent_tensor_upper_statement.
