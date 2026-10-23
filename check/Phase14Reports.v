(* One identified axiom report per characterization lemma of
   check/Phase14Definitions.v and per accepted general statement of
   check/Phase14Statements.v, beside those of check/Reports.v, which is
   pinned: the full name of the lemma (Locate), then its axioms. The two
   check files are compiled first, into build/checks/, as Checks.<Name>;
   this file only Requires them. Its code is fixed by
   scripts/check_sources.py, and make check compiles it through
   scripts/run_checks.py. *)

Require Checks.Phase14Definitions Checks.Phase14Statements.

(* check/Phase14Definitions.v *)
Locate Checks.Phase14Definitions.ksubset_characterization.
Print Assumptions Checks.Phase14Definitions.ksubset_characterization.
Locate Checks.Phase14Definitions.ksubset_mx_characterization.
Print Assumptions Checks.Phase14Definitions.ksubset_mx_characterization.
Locate Checks.Phase14Definitions.perm_cut_characterization.
Print Assumptions Checks.Phase14Definitions.perm_cut_characterization.

(* check/Phase14Statements.v *)
Locate Checks.Phase14Statements.accepted_multiplicity.trace_multiplicity_accepted.
Print Assumptions Checks.Phase14Statements.accepted_multiplicity.trace_multiplicity_accepted.
Locate Checks.Phase14Statements.accepted_multiplicity.ksubset_multiplicity_accepted.
Print Assumptions Checks.Phase14Statements.accepted_multiplicity.ksubset_multiplicity_accepted.
Locate Checks.Phase14Statements.accepted_harmonic.harmonic_ln_accepted.
Print Assumptions Checks.Phase14Statements.accepted_harmonic.harmonic_ln_accepted.
Locate Checks.Phase14Statements.accepted_binomial_bounds.bin_mul_pow_accepted.
Print Assumptions Checks.Phase14Statements.accepted_binomial_bounds.bin_mul_pow_accepted.
Locate Checks.Phase14Statements.accepted_expander.expander_accepted.
Print Assumptions Checks.Phase14Statements.accepted_expander.expander_accepted.
