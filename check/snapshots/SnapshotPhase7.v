(* The statement snapshot SnapshotPhase7 (scripts/check_sources.py, rule 30):
   the declarations accepted at d4de51d11b12, printed in full. Written
   by scripts/snapshot_baselines.py; its reference, the output at that
   commit, is check/snapshots/SnapshotPhase7.txt. *)

Require EllipsoidUniversality.LatentSignDefinitions.
Require EllipsoidUniversality.LatentSignStatement.

Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 78.

Print Module EllipsoidUniversality.LatentSignDefinitions.
Print EllipsoidUniversality.LatentSignDefinitions.latent_sample_density.
Print EllipsoidUniversality.LatentSignDefinitions.latent_probability.
Print Module EllipsoidUniversality.LatentSignStatement.
Print EllipsoidUniversality.LatentSignStatement.latent_sign_statement.
