(* The statement snapshot SnapshotPhase14Statements (scripts/check_sources.py, rule 30):
   the general statements of phase 14 accepted at 39f58468aeaa, stated
   by check/Phase14Statements.v, and the library lemmas that prove them,
   printed in full against the library at 4d020691cfee, the first
   commit of main with their proofs. Written by
   scripts/snapshot_baselines.py; its reference, the output at that
   commit, is check/snapshots/SnapshotPhase14Statements.txt. *)

Require Checks.Phase14Statements.

Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 78.

Check Checks.Phase14Statements.accepted_multiplicity.trace_multiplicity_accepted.
Check Checks.Phase14Statements.accepted_multiplicity.ksubset_multiplicity_accepted.
Check Checks.Phase14Statements.accepted_harmonic.harmonic_ln_accepted.
Check Checks.Phase14Statements.accepted_binomial_bounds.bin_mul_pow_accepted.
Check Checks.Phase14Statements.accepted_expander.expander_accepted.
Check @GaussianAnalysis.matrix.multiplicity.trace_multiplicity.
Check @GaussianAnalysis.matrix.multiplicity.ksubset_multiplicity.
Check @GaussianAnalysis.combinatorics.harmonic.harmonic_ln.
Check @GaussianAnalysis.combinatorics.binomial_bounds.bin_mul_pow.
Check @GaussianAnalysis.combinatorics.expander.expander.
