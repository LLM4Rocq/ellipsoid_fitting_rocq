(* The identity driver of the statement snapshot SnapshotPhase14Statements (rule 30 (e)
   of scripts/check_sources.py): the references of the kernel term of
   each declaration that check/snapshots/SnapshotPhase14Statements.v prints, read by
   the exporter of check/identity/. Written by
   scripts/snapshot_baselines.py from check/identity/inventory.json; its
   reference is check/identity/IdentitySnapshotPhase14Statements.json. *)

Require Checks.Phase14Statements.
Declare ML Module "kernel_identity".

KernelIdentity "type" "Checks.Phase14Statements.accepted_multiplicity.trace_multiplicity_accepted".
KernelIdentity "type" "Checks.Phase14Statements.accepted_multiplicity.ksubset_multiplicity_accepted".
KernelIdentity "type" "Checks.Phase14Statements.accepted_harmonic.harmonic_ln_accepted".
KernelIdentity "type" "Checks.Phase14Statements.accepted_binomial_bounds.bin_mul_pow_accepted".
KernelIdentity "type" "Checks.Phase14Statements.accepted_expander.expander_accepted".
KernelIdentity "type" "GaussianAnalysis.matrix.multiplicity.trace_multiplicity".
KernelIdentity "type" "GaussianAnalysis.matrix.multiplicity.ksubset_multiplicity".
KernelIdentity "type" "GaussianAnalysis.combinatorics.harmonic.harmonic_ln".
KernelIdentity "type" "GaussianAnalysis.combinatorics.binomial_bounds.bin_mul_pow".
KernelIdentity "type" "GaussianAnalysis.combinatorics.expander.expander".
