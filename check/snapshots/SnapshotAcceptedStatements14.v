(* The bodies of the 5 accepted _statement definitions, printed at
   39f58468aeaa (scripts/check_sources.py, rule 30 (d)). The definitions
   no longer exist at HEAD: this file is compiled only at the
   acceptance commit, and its output is compared with the statements
   of the lemmas of check/Phase14Statements.v. *)

Require GaussianAnalysis.combinatorics.binomial_bounds.
Require GaussianAnalysis.combinatorics.expander.
Require GaussianAnalysis.combinatorics.harmonic.
Require GaussianAnalysis.matrix.multiplicity.

Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 78.

Print GaussianAnalysis.matrix.multiplicity.trace_multiplicity_statement.
Print GaussianAnalysis.matrix.multiplicity.ksubset_multiplicity_statement.
Print GaussianAnalysis.combinatorics.harmonic.harmonic_ln_statement.
Print GaussianAnalysis.combinatorics.binomial_bounds.bin_mul_pow_statement.
Print GaussianAnalysis.combinatorics.expander.expander_statement.
