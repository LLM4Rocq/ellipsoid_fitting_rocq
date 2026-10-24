#!/usr/bin/env python3
"""Check the rules on sources that the build does not check.

1. The frozen files are unchanged. The code of each file of FROZEN, with
   comments removed and whitespace collapsed, must equal its code at the
   commit named in check/frozen-baseline. Comments may change. The files
   of EXACT must be byte-identical to that commit. The code of each file
   of EXTENSION_FROZEN, the statement of the universality theorem of
   extension/ and its definitions, must equal its code at the commit
   EXTENSION_BASELINE, the merge that brought them to main. The code of
   each file of PHASE6_FROZEN, the statements of the finite-mixture
   theorem and of its corollary for the paired law and their definitions,
   must equal its code at the commit PHASE6_BASELINE, at which the user
   accepted them.
2. No module of theories/, library/ or extension/ contains Admitted,
   Axiom, Parameter or Conjecture outside comments.
3. library/ is independent of the papers and of Stdlib's reals: no module
   of library/ requires a module of EllipsoidFitting or
   EllipsoidUniversality, Stdlib's real analysis (Reals, Lra, Psatz,
   Rpower and the other R* modules) or MathComp's bridge to them (Rstruct,
   Rstruct_topology).
4. Given the output of check/Assumptions.v as first argument, every axiom
   it prints is among those of check/assumptions.expected. Given the output
   of check/UniversalityAssumptions.v as second argument, every axiom it
   prints is among those of check/universality_assumptions.expected. Fewer
   is fine. Every axiom of check/universality_assumptions.expected is among
   those of check/assumptions.expected, whose text is frozen (EXACT).
5. check/UniversalityAssumptions.v has the code UNIVERSALITY_CHECK: it
   checks that universality_theorem proves the frozen statement
   universality_statement, and prints the axioms of universality_theorem.
6. Phase 6. check/MixtureAssumptions.v and check/PairedAssumptions.v have
   the codes MIXTURE_CHECK and PAIRED_CHECK: they check that
   mixture_theorem proves mixture_theorem_statement and paired_theorem
   proves paired_statement, and print their axioms. Given these outputs as
   third and fourth arguments, every axiom they print is among those of
   check/mixture_assumptions.expected and check/paired_assumptions.expected,
   whose axioms are among those of check/assumptions.expected.
7. Phase 7. The check files and expected lists of CHECKS_EXACT, those of
   the axiom checks of phases 5 and 6, are byte-identical to the commit
   CHECKS_BASELINE. Every axiom report given as an argument has the line
   "Axioms:" or the line "Closed under the global context"; a report with
   neither, for example an empty one, is an error, not an empty set of
   axioms. The definition of tuple_prod, on which the frozen statements of
   phases 5 and 6 depend, is pinned: the Require commands of TUPLE_PROD
   and the code of its section tuple_prod must equal their code at
   CHECKS_BASELINE.
8. Phase 7. The code of each file of LATENT_FROZEN, the statement of the
   latent-sign corollary and its definitions, must equal its code at the
   commit LATENT_BASELINE, at which the user accepted them.
   check/LatentSignAssumptions.v has the code LATENT_CHECK: it checks that
   latent_sign_theorem proves latent_sign_statement and prints its axioms.
   Given its output as fifth argument, every axiom it prints is among those
   of check/latent_sign_assumptions.expected, whose axioms are among those
   of check/assumptions.expected.
9. Phase 8. The code of each file of PHASE8_FROZEN, the statements of the
   countable-mixture theorem, of the condition-number theorem and of the
   scope results on the latent-sign law, and their definitions, must equal
   its code at the commit PHASE8_BASELINE, at which the user accepted them.
10. Phase 8. check/CountableAssumptions.v, check/ConditionAssumptions.v
   and check/LatentScopeAssumptions.v have the codes COUNTABLE_CHECK,
   CONDITION_CHECK and LATENT_SCOPE_CHECK: they check that
   countable_theorem proves countable_theorem_statement, condition_theorem
   proves condition_theorem_statement and latent_scope_theorem proves
   latent_scope_statement, and print their axioms. Given their outputs as
   sixth, seventh and eighth arguments, every axiom they print is among
   those of check/countable_assumptions.expected,
   check/condition_assumptions.expected and
   check/latent_scope_assumptions.expected, whose axioms are among those
   of check/assumptions.expected.
11. Phase 9. An axiom report with the line "Axioms:" must list at least
   one axiom after it; a report without axioms is accepted only through
   the line "Closed under the global context". The check files and
   expected lists of CHECKS_EXACT_P8, those of the axiom checks of phases
   7 and 8, are byte-identical to the commit CHECKS_P8_BASELINE, a
   separate baseline; CHECKS_BASELINE and check/frozen-baseline do not
   change.
12. Phase 9. The code of each file of PHASE9_FROZEN, the statements of the
   robustness corollary, of the tensorization bounds of the latent-sign
   law, of the continuous-latent counterexample and of the endpoint
   expansions of the condition-number curve, and their definitions, must
   equal its code at the commit PHASE9_BASELINE, at which the user accepted
   them.
13. Phase 9. check/RobustAssumptions.v, check/LatentTensorAssumptions.v,
   check/ContinuousLatentAssumptions.v and
   check/ConditionEndpointsAssumptions.v have the codes ROBUST_CHECK,
   LATENT_TENSOR_CHECK, CONTINUOUS_LATENT_CHECK and
   CONDITION_ENDPOINTS_CHECK: they check that robust_theorem proves
   robust_theorem_statement, latent_tensor_theorem proves
   latent_tensorization_statement, continuous_latent_theorem proves
   continuous_latent_statement and condition_endpoints_theorem proves
   condition_endpoints_statement, and print their axioms. Given their
   outputs as ninth to twelfth arguments, every axiom they print is among
   those of check/robust_assumptions.expected,
   check/latent_tensor_assumptions.expected,
   check/continuous_latent_assumptions.expected and
   check/condition_endpoints_assumptions.expected, whose axioms are among
   those of check/assumptions.expected.
14. Phase 10. The code of each file of PHASE10_FROZEN, the statements of
   the robustness of the optimal condition number and of the finite
   tensorization constant of the latent-sign law, must equal its code at
   the commit PHASE10_BASELINE, at which the user accepted them.
15. Phase 10. check/ConditionRobustAssumptions.v and
   check/LatentTensorUpperAssumptions.v have the codes
   CONDITION_ROBUST_CHECK and LATENT_TENSOR_UPPER_CHECK: they check that
   robust_condition_theorem proves robust_condition_theorem_statement and
   latent_tensor_upper_theorem proves latent_tensor_upper_statement, and
   print their axioms. Given their outputs as thirteenth and fourteenth
   arguments, every axiom they print is among those of
   check/condition_robust_assumptions.expected and
   check/latent_tensor_upper_assumptions.expected, whose axioms are among
   those of check/assumptions.expected.
16. Phase 10. The check files and expected lists of CHECKS_EXACT_P9, those
   of the axiom checks of phase 9, are byte-identical to the commit
   CHECKS_P9_BASELINE, a separate baseline; CHECKS_BASELINE,
   CHECKS_P8_BASELINE and check/frozen-baseline do not change.
17. Phase 11. The code of each file of PHASE11_FROZEN, the definitions of
   the condition-number curve at every fourth moment and the statements of
   the curve, of the threshold theorem at every fourth moment and of its
   robustness, must equal its code at the commit PHASE11_BASELINE, at which
   the user accepted them.
18. Phase 11. The check files and expected lists of CHECKS_EXACT_P10, those
   of the axiom checks of phase 10, are byte-identical to the commit
   CHECKS_P10_BASELINE, a separate baseline; CHECKS_BASELINE,
   CHECKS_P8_BASELINE, CHECKS_P9_BASELINE and check/frozen-baseline do not
   change.
19. Phase 11. check/ConditionKappaCurveAssumptions.v,
   check/ConditionKappaAssumptions.v and
   check/ConditionKappaRobustAssumptions.v have the codes
   CONDITION_KAPPA_CURVE_CHECK, CONDITION_KAPPA_CHECK and
   CONDITION_KAPPA_ROBUST_CHECK: they check that
   condition_kappa_curve_theorem proves condition_kappa_curve_statement,
   condition_kappa_theorem proves condition_kappa_theorem_statement and
   condition_kappa_robust_theorem proves
   condition_kappa_robust_theorem_statement, and print their axioms. Given
   their outputs as fifteenth to seventeenth arguments, every axiom they
   print is among those of check/condition_kappa_curve_assumptions.expected,
   check/condition_kappa_assumptions.expected and
   check/condition_kappa_robust_assumptions.expected, whose axioms are
   among those of check/assumptions.expected.
20. Phase 11. The check files and expected lists of CHECKS_EXACT_P11, those
   of the axiom checks of phase 11, are byte-identical to the commit
   CHECKS_P11_BASELINE, a separate baseline; CHECKS_BASELINE,
   CHECKS_P8_BASELINE, CHECKS_P9_BASELINE, CHECKS_P10_BASELINE and
   check/frozen-baseline do not change.
21. Phase 12. Rule 2 also covers applications/, the directory of the
   logical root GaussianApplications. Rule 3 applies to applications/ as
   to library/: no module of applications/ requires a module of
   EllipsoidFitting or EllipsoidUniversality, Stdlib's real analysis or
   MathComp's bridge to it. No module of library/ requires a module of
   GaussianApplications. An omitted axiom report is an error: the script
   takes exactly one report per theorem of its table, in the order of
   THEOREMS (the main theorem, the universality theorem, then those of
   PHASE6_THEOREMS to PHASE14_THEOREMS, then SHIFTED_THEOREMS, 37 in all
   since rule 37), and a
   missing or extra report makes it fail.
22. Phase 12, the freeze of batch 1. The code of each file of
   PHASE12_B1_FROZEN, the statements of the Gaussian matrix series, of the
   sharp upper edge of the GOE and of the orthogonal splitting of positive
   semidefinite matrices, must equal its code at the commit
   PHASE12_B1_BASELINE, at which the user accepted them. The definition of
   lambda_max, on which the second depends, is pinned: the Require
   commands of LAMBDA_MAX and the code of its section lambda_max must equal
   their code at PHASE12_B1_BASELINE; the lemmas after the section may
   change. The other library definitions that these statements unfold to
   are protected by check/ApplicationsDefinitions.v, which states a
   characterization of each (mxdot, frobenius, opnorm, psdmx, goe_mx, the
   measurable structure of matrices, and gauss through its values on
   boxes, which determine it), has the code APPLICATIONS_DEFINITIONS_CHECK,
   and is compiled by make check. The reports are identified by their
   paths: the arguments must be exactly the paths of REPORTS, one per
   theorem of THEOREMS, in that order, so that a missing, extra,
   duplicated or substituted report is an error, and a report that does
   not exist is an error. make check deletes the reports before it
   compiles the check files, so a report is never reused from an earlier
   run.
23. Phase 12, the freeze of batch 2. The code of each file of
   PHASE12_B2_FROZEN, the statements of the tensor packing, of the
   spectral gap of the SK heat-bath dynamics, of the sign/Gaussian
   comparison for the Ising perceptron and of the capped variance for
   random k-SAT, with the definitions files of the last three, must equal
   its code at the commit PHASE12_B2_BASELINE, at which the user accepted
   them. The library definitions that these files unfold to (mxdot,
   frobenius, opnorm, goe_mx, gauss and the measurable structure of
   matrices) are those of rule 22, protected by
   check/ApplicationsDefinitions.v.
24. Phase 12, the axiom checks. The seven check files of PHASE12_THEOREMS,
   check/MatrixSeriesAssumptions.v to check/SatVarianceAssumptions.v, have
   the codes of PHASE12_CHECKS: each checks that the theorem of a target
   (matrix_series_theorem, tensor_packing_theorem, goe_edge_theorem,
   sk_gap_theorem, psd_splitting_theorem, perceptron_sign_theorem,
   sat_variance_theorem) proves its frozen statement, and prints its
   axioms. Given their outputs as the eighteenth to twenty-fourth
   arguments, every axiom they print is among those of the expected list
   of the target, check/<target>_assumptions.expected, whose axioms are
   among those of check/assumptions.expected. The script then takes 24
   reports, one per theorem of THEOREMS.
25. Phase 12, the pin. The check files and expected lists of
   CHECKS_EXACT_P12, those of the axiom checks of phase 12 (rule 24), are
   byte-identical to the commit CHECKS_P12_BASELINE (commit P), a separate
   baseline; the older baselines and check/frozen-baseline do not change.
26. Phase 13, the freeze of batch 1. The code of each file of
   PHASE13_B1_FROZEN, the definition and the statement of the
   satisfiability threshold of random k-SAT and the statement of the
   convergence from approximate minimum inequalities, must equal its code
   at the commit PHASE13_B1_BASELINE, at which the user accepted them.
   The project definitions that the frozen statements of phase 13 and the
   accepted general statements of its packets unfold to are protected by
   check/Phase13Definitions.v, which states a characterization of each,
   written out down to the definitions of MathComp and MathComp-Analysis.
   Its code is fixed: it must equal the last code of
   PHASE13_DEFINITIONS_FREEZES, and the code of each freeze is a prefix of
   the code of the next one, so that a freeze extends the file without
   altering it. make check deletes its output,
   build/phase13_definitions.txt, then compiles the file into it; the
   output is required: it must exist and be a complete axiom report whose
   axioms are among those of check/sat_variance_assumptions.expected (the
   seven axioms of phases 11 and 12). The Makefile must hold the two
   commands of PHASE13_MAKE_LINES, the deletion of the output and the
   compilation, so that an old output cannot stand for a new one.
   INVENTORY records the general
   statements that the user accepted, one entry per statement: the full
   acceptance commit, the path, the name of the Prop definition and the
   proposition as Print shows it at that commit, with its section
   parameters. Each entry must name a full commit at which that file
   defines that name, and no two entries name the same statement.
27. Phase 13, the freeze of batch 2. The code of each file of
   PHASE13_B2_FROZEN, the statements of the exact normalization of PSD
   factors and of the product smoothing of matrix squares, must equal its
   code at the commit PHASE13_B2_BASELINE, at which the user accepted them.
   check/Phase13Definitions.v is extended, by its freeze 2 code in
   PHASE13_DEFINITIONS_FREEZES, with the definitions that these statements
   and packet P unfold to (bdot, bchar, blk_deg, blk_dist, fcoef,
   low_blk_deg, prob_vec, prod_avg, smoothing_hyps, weighted_gram and
   psd_factorization); INVENTORY gains the statements of packet P.
28. Phase 13, the freeze of batch 3. The code of each file of
   PHASE13_B3_FROZEN, the definitions and the statement of the exponential
   PSD rank of the shifted matching matrices, must equal its code at the
   commit PHASE13_B3_BASELINE, at which the user accepted them. Their
   project definitions are psdmx (check/ApplicationsDefinitions.v) and
   psd_factorization (check/Phase13Definitions.v, freeze 2). The third
   freeze of check/Phase13Definitions.v adds psd_eval and psd_eval_cone,
   which the statements of P4 unfold to, and INVENTORY gains the accepted
   statements of item X and of P4, reviewed with batch 3.
29. Phase 13, the axiom checks and the accepted statements. The four check
   files of PHASE13_THEOREMS, check/SatThresholdAssumptions.v,
   check/PsdNormalizationAssumptions.v, check/ProductSmoothingAssumptions.v
   and check/MinSuperadditiveAssumptions.v, have the codes of PHASE13_CHECKS:
   each requires the frozen statement module and the theorem module of a
   target (T9 to T12) without Import, defines <target>_identity with the
   frozen statement as its type and the theorem as its body, both by their
   absolute names, so that it compiles only if the theorem proves the frozen
   statement and no name of the theorem module can stand for the statement,
   and prints the full name of that definition (Locate, a marker line that is
   not an axiom) and its axioms, which must be among those of its expected
   list; the axioms of each of the four lists must be among the
   seven of check/sat_variance_assumptions.expected (those of phases 11 and
   12: no Classical_Prop.classic). The script then takes 28 reports, one per
   theorem of THEOREMS. check/LibraryStatements.v has the
   code LIBRARY_STATEMENTS_CHECK: for every entry of INVENTORY it states the
   accepted proposition in full, as the lemma <base>_accepted (base: the name
   without the suffix _statement), and proves it by exact: @base, so that the
   type of the library lemma must be convertible with it; every entry must
   have such a lemma, with the recorded proposition (a leading fun of section
   parameters read as forall). make check deletes its output,
   build/library_statements.txt, and compiles the file into it; the output is
   required and must be a complete axiom report within the seven axioms. The
   Makefile must hold the commands of PHASE13_MAKE_LINES_P.

30. Phase 13, the repair of the checks of 15 October 2026
   (reviews/phase13-checker-repair.md, version 2).
   (a) Reading. The text of a source is read as Rocq reads it, by
   scripts/rocq_lex.py, loaded by its path: comments nest; a double quote
   opens a string both in code and in a comment, and the comment delimiters
   inside a string do not count; a comment separates tokens; the blanks are
   those of Rocq, so U+00A0 and every other character are kept; carriage
   returns are kept. A text that the lexer cannot read is a failure: an
   unterminated comment or string, and the forms that Rocq reads by the
   keywords in scope (a comment opener or a double quote glued to the token
   before it, and the quotations :{{ and lp:). code() (rules 1, 7 to 29,
   32 to 34 and 36 to 38),
   the pinned sections, the Require commands of rule 3 and the scan of rule
   2 read the sentences of that code, never the inside of a comment or a
   string. The scan of rule 2 refuses, after any attributes and modifiers,
   Axiom, Parameter, Conjecture (singular or plural), Admitted, Admit
   Obligations, Declare Instance, Declare ML Module, Add LoadPath, Add ML
   Path, Load, Extraction in its forms, Redirect, Cd, every Elpi command,
   Extra Dependency, HB.graph, Set or Unset of Guard, Positivity or Universe
   Checking, the attribute bypass_check, and a Variable, Hypothesis or
   Context outside a section. Elpi, which Hierarchy-Builder brings, runs
   shell commands and writes files while Rocq compiles (its built-ins
   system and open_out), from a quotation or from a file that Extra
   Dependency names (E37); the other commands of Hierarchy-Builder take
   only Rocq terms, and HB.graph writes the file it names. In library/,
   extension/ and applications/, a global or exported setting, an exported
   module and Require Export are refused. In a frozen file, a pinned section
   or a code-fixed check file, a non-ASCII character outside comments, Set
   Warnings, a warning attribute, and a comment not followed by a blank, a
   line boundary or a parenthesis are refused. A missing frozen, pinned or
   code-fixed file is a failure.
   (b) Compilation. make check first runs this script with --before-build,
   which applies every rule that reads only the sources (rules 1 to 3, 7 to
   29 and 32 to 39, and those of rule 30 that read no compiled file), and
   stops on a
   failure before anything compiles, since a source that breaks them can
   run code during the build (E37). It then builds, and runs this script
   again, which applies the same rules and starts the runner only if they
   hold. make runs the build and this script without the variables of
   UNSAFE_ENV of the Makefile (an rc file, load paths, plugin paths) and
   without any variable whose name starts with OCAML or CAML (findlib and
   the OCaml compiler), and Rocq runs with -q. The modules of scripts/ that this script and the
   runner load are compiled from their source, never from the bytecode
   cached in scripts/__pycache__/, which python3 -B does not prevent and
   which can stand for another source (E36). make reads a GNUmakefile or a
   makefile before the Makefile: this script refuses both, but only make
   -f Makefile check, or a check from outside the tree that they are
   absent, makes sure that make runs this script at all (E38). This
   script creates a run identifier and starts scripts/run_checks.py,
   loaded by its path, with python3 -I -B; the
   runner compiles each check file of CHECK_FILES with its flags, -q and the
   warning comment-terminator-in-string as an error, publishes an output
   only after exit status 0, and writes build/checks/manifest.json after
   full success. This script then requires that manifest, with this run's
   identifier, ROCQ_VERSION and the PACKAGES installed, every check file of
   CHECK_FILES in order with its flags and output, the SHA-256 of each source
   as it is now and of each output and standard error as they are read, and
   no file of build/checks/ that it does not list. The runner also runs
   rocqchk -silent -o on every module of library/, theories/, extension/ and
   applications/ and every check file, each named with -norec, so that the
   kernel checks each again; its output must show the default theory (Set
   predicative, no rewrite rules), nothing that relies on type-in-type,
   unsafe (co)fixpoints or assumed positivity, and no axiom of a project
   module (rule 2 at the kernel level). The files of FIXED_FILES
   (the Makefile and the reviewed scripts) have their fixed SHA-256;
   scripts/ holds exactly SCRIPTS; the option lines of _CoqProject are
   COQPROJECT_OPTIONS and every other line is a source file of the four
   source directories; the files of ABSENT_FILES do not exist, each name
   compared against the directory listing so that a case-insensitive file
   system does not confuse makefile with Makefile; git tracks no
   build product (compiled Rocq files, the generated makefiles, build/,
   Python bytecode). This replaces the command-text checks of rules 26 and
   29 and the report arguments of rules 4 to 24: the outputs are those of
   CHECK_FILES, read through the manifest.
   (c) Output. Each output holds exactly what its entry of CHECK_FILES
   requires, and none reports an unsafe construction (an unsafe hierarchy,
   an assumed guard or positivity, a Theory section): one complete axiom
   report within its expected list for each theorem check file, after the
   full name of its identity definition for the four of phase 13, the
   two of phase 14 and the seven of step 18; nothing for
   check/ApplicationsDefinitions.v and
   check/MatrixSigmaRing.v; three complete reports for
   check/Phase13Definitions.v and one each for check/LibraryStatements.v,
   check/Phase14Definitions.v, check/Phase14Statements.v and
   check/ShiftedDefinitions.v, within the seven axioms of
   check/sat_variance_assumptions.expected; for check/TheoremIdentities.v,
   check/Reports.v, check/Phase14Identities.v, check/Phase14Reports.v,
   check/ShiftedIdentities.v and check/ShiftedReports.v, the full name of
   each identity,
   characterization lemma or accepted statement, in order, each followed by
   one complete report within its list. check/TheoremIdentities.v
   requires the statement and theorem modules without Import and defines,
   by absolute names, <theorem>_identity with the frozen statement as its
   type and the theorem as its body, for each of the 28 theorems: in the
   theorem check files of phases 5 to 12, which import the unfrozen theorem
   modules after the statement modules, a definition of a theorem module can
   shadow the statement.
   (d) Snapshots. Each snapshot file of CHECK_FILES requires the frozen
   modules of one acceptance baseline, and compiled check files, without
   Import, and prints under Set Printing All, Set Printing Universes, Set
   Printing Depth 1000000 and Set Printing Width 78 the module lists of the
   frozen modules (Print Module), the bodies of their definitions, the
   statements of their theorems, the pinned sections, the characterization
   lemmas and the accepted statements. Its standard error must be empty, its
   output must not hold the elision token ..., and its output must equal its
   reference in check/snapshots/, written by scripts/snapshot_baselines.py
   from a build of the acceptance commit, whose SHA-256 is fixed: a
   reference is never regenerated to make an output pass. NEW_CHECK_CODE
   fixes the code of the new check files. Each project constant that the
   snapshot of a frozen or accepted statement names (resolved by Locate at
   its acceptance commit, in check/snapshots/REFERENCES.json) is defined in
   a frozen file, lies in a pinned section, or is named by the snapshot of a
   characterization lemma. check/MatrixSigmaRing.v characterizes the
   SigmaRing instance of matrices that the statements of phase 12, batch 1,
   name: its measurable sets are, by reflexivity, those that
   check/ApplicationsDefinitions.v characterizes (the user's decision of 15
   October 2026).
   (e) Identities (E42). A snapshot prints names, and a printed name can
   resolve to another constant than at the acceptance commit, with the same
   text. For each snapshot that prints a declaration, the driver
   check/identity/Identity<Name>.v requires the same modules and asks the
   exporter of check/identity/ (Declare ML Module "kernel_identity", allowed
   in these drivers only) for each declaration: a Print in definition mode
   (type and body), except the opaque roots listed in
   scripts/identity_sidecars.py, in opaque-body mode, and a Check in type
   mode. check/identity/inventory.json lists the queries and must equal the
   list read from the snapshot files; each driver must equal the text
   generated from it. scripts/run_checks.py builds the exporter from its
   fixed sources and compiles the drivers with OCAMLPATH set to that build
   only. Each output must be framed exactly (one complete record per query,
   in order, with the expected target, mode and parts, and nothing else),
   its standard error empty, and the references it lists (the kernel names,
   user and canonical, of each constant, inductive, constructor and
   projection of each term, at its position in the term) must equal those of
   the reference check/identity/Identity<Name>.json, written by
   scripts/snapshot_baselines.py from a build of the acceptance commit, whose
   SHA-256 IDENTITY_REFERENCES fixes. There are IDENTITY_QUERIES queries in
   IDENTITY_PARTS parts. The manifest records the versions of ocamlopt and
   findlib (OCAML_VERSION, FINDLIB_VERSION), the SHA-256 of the exporter's
   build recipe and that of the plugin built, which must equal the plugin of
   every reference (check/identity/REFERENCES.json). The protection closure
   of (d) also holds for these kernel names, user and canonical, of every
   kind of reference: a project name is a subject of its snapshot, defined
   in a frozen file (by the file of its kernel name), pinned, referenced by a
   characterization snapshot, or, under Checks., defined in a check file. The sidecars hold no universe: the snapshots
   print them. They identify names; they do not fix what a name means, which
   the frozen files, the pinned sections and the characterizations do.
31. Phase 13, the pin. The ten files of CHECKS_EXACT_P13, the four axiom
   checks of phase 13 (rule 29) and their expected lists,
   check/Phase13Definitions.v and check/LibraryStatements.v, are
   byte-identical to the commit CHECKS_P13_BASELINE, the commit of the
   repair of rule 30, a separate baseline. So is the repaired machinery
   and its reference data: every file of MACHINERY_P13 (the scripts other
   than this one, the Makefile and the check files that the repair added)
   and every file that git lists at that commit under a directory of
   MACHINERY_DIRS_P13 (the identity drivers and their references, the
   statement snapshots and their references, the regression tests). The
   comparison is of bytes, not of code. This script cannot check itself;
   the fingerprint record of the machinery, kept outside the repository,
   holds its SHA-256. The older baselines and check/frozen-baseline do not
   change. Since rule 34, the five files of P14_CHANGED, which the extension
   of phase 14 changes, are left out of this comparison and fixed by
   FIXED_FILES instead.
32. Phase 14, the freeze of batch 1 (the user's acceptance of 22 October
   2026, 14:29). The code of each file of PHASE14_FROZEN, the definitions
   and the statement of the corollary on unshifted matching matrices and
   exact semidefinite lifts, must equal its code at the commit
   PHASE14_BASELINE, at which the user accepted them. INVENTORY_P14
   records the general statements of batch 1 accepted at that commit, as
   INVENTORY does for phase 13 (rule 26): the acceptance commit, the path,
   the name of the Prop definition and the proposition as Print shows it at
   that commit under Set Printing Implicit; each entry must name a full
   commit at which that file defines that name, and no two entries name
   the same statement. The project definitions that these statements unfold
   to and that no earlier check protects (ksubset, ksubset_mx and perm_cut,
   whose code the user bound to that commit until this round) are
   characterized by check/Phase14Definitions.v, whose code is fixed
   (PHASE14_DEFINITIONS_CHECK); make check compiles it into a required
   output, one complete axiom report within the seven axioms of
   check/sat_variance_assumptions.expected.
33. Phase 14, the axiom checks and the accepted statements. The two check
   files of PHASE14_THEOREMS, check/PsdRankAssumptions.v and
   check/PsdLiftAssumptions.v, have the codes of PHASE14_CHECKS: as in rule
   29, each requires the frozen statement module and the theorem module
   without Import, defines <target>_identity with the frozen statement as
   its type and the theorem (psd_rank_theorem, psd_lift_theorem) as its
   body, by absolute names, and prints its full name and its axioms, which
   must be among those of its expected list; the axioms of each list must
   be among the seven. The script then takes 30 reports, one per theorem of
   THEOREMS (37 since rule 37). check/Phase14Statements.v has the code
   PHASE14_STATEMENTS_CHECK: for every entry of INVENTORY_P14 it states the
   accepted proposition in full, as the lemma <base>_accepted, and proves it
   by exact: @base, with the recorded proposition (a leading fun of section
   parameters read as forall), as check/LibraryStatements.v does for
   INVENTORY; its output is required, one complete axiom report within the
   seven axioms. check/TheoremIdentities.v and check/Reports.v are pinned
   (rule 31), so check/Phase14Identities.v defines the identities of the two
   theorems (PHASE14_IDENTITIES) and check/Phase14Reports.v prints an
   identified report for each characterization lemma of
   check/Phase14Definitions.v and each lemma of check/Phase14Statements.v
   (PHASE14_REPORTS), each within the seven axioms; their codes are fixed by
   NEW_CHECK_CODE.
34. Phase 14, the snapshots, the identities and the files of the
   extension. Rule 30 (d) and (e) apply to four new snapshots:
   SnapshotPhase14, the frozen files of rule 32 at PHASE14_BASELINE;
   SnapshotPhase14Definitions, the characterization lemmas of
   check/Phase14Definitions.v against the library at PHASE14_BASELINE, a
   characterization snapshot; SnapshotPhase14Statements, the lemmas of
   check/Phase14Statements.v and the library lemmas that prove them, against
   the library at 4d020691, the first commit of main with their proofs (the
   accepted statements were proved after their acceptance, so their lemmas
   do not exist at PHASE14_BASELINE); and SnapshotAcceptedStatements14, the
   accepted bodies printed at PHASE14_BASELINE, compiled at that commit
   only, as SnapshotAcceptedStatements. check/snapshots/AcceptedConversions14.v,
   compiled at 4d020691 by scripts/snapshot_baselines.py, gives each
   accepted body, printed under Set Printing All at PHASE14_BASELINE, as the
   type of two definitions whose bodies are the lemma of
   check/Phase14Statements.v and the library lemma. The extension changes
   five files of rule 31, P14_CHANGED (scripts/snapshot_baselines.py,
   scripts/identity_sidecars.py, check/snapshots/REFERENCES.json,
   check/identity/inventory.json and check/identity/REFERENCES.json); rule
   31 applies to the others, and these five, like every file that the
   extension adds, have their SHA-256 in FIXED_FILES or their code in
   NEW_CHECK_CODE.
35. Phase 14, the pin. The eight files of CHECKS_EXACT_P14 (the two axiom
   checks of rule 33 with their expected lists, check/Phase14Definitions.v,
   check/Phase14Statements.v, check/Phase14Identities.v and
   check/Phase14Reports.v) and the files of MACHINERY_P14 (the five files of
   P14_CHANGED and the snapshot files, references, conversions, identity
   drivers and identity references that the extension adds) are
   byte-identical to the commit CHECKS_P14_BASELINE (commit P of phase 14),
   a separate baseline. The older baselines, the pin of rule 31 for every
   other file and check/frozen-baseline do not change. Since rule 38, the
   four files of SHIFTED_CHANGED, which step 18 changes, are left out of
   this comparison and fixed by FIXED_FILES instead; rule 39 pins them.
36. Step 18, the shifted freeze (the user's acceptance of the seven
   statement files of the shifted-Gaussian extension on 16 October 2026,
   and the user's approval of the step 18 amendment on 23 October 2026,
   14:24). The code of each file of SHIFTED_FROZEN must equal its code at
   the commit SHIFTED_BASELINE, at which the user accepted them. The
   project definitions that these statements unfold to and that no earlier
   check protects are characterized by check/ShiftedDefinitions.v, whose
   code is fixed (SHIFTED_DEFINITIONS_CHECK); its output is required, one
   complete axiom report within the seven axioms of
   check/sat_variance_assumptions.expected.
37. Step 18, the axiom checks, the identities and the merge guards. The
   seven check files of SHIFTED_THEOREMS,
   check/ShiftedConditionAssumptions.v to check/ShiftedSignAssumptions.v,
   have the codes of SHIFTED_CHECKS: as in rule 33, each requires the
   frozen statement module and the theorem module without Import, defines
   shifted_<x>_identity with the frozen statement as its type and the
   theorem as its body, by absolute names, and prints its full name and its
   axioms, which must be among those of its expected list; the axioms of
   each list must be among the seven. The script then takes 37 reports,
   one per theorem of THEOREMS. check/ShiftedIdentities.v defines the
   identities of the seven theorems (SHIFTED_IDENTITIES) and their
   conjunction shifted_identities, and prints an identified report after
   each; check/ShiftedReports.v prints an identified report for each
   characterization lemma of check/ShiftedDefinitions.v (SHIFTED_REPORTS);
   each report is within the seven axioms, and the codes of the two files
   are fixed by NEW_CHECK_CODE. Two guards, applied before the build, keep
   a merge from passing while it leaves a check file out: the theorem check
   files of CHECK_FILES (the entries whose output is one marked report
   labelled by a theorem of THEOREMS) are in one-to-one correspondence with
   THEOREMS, one entry per theorem (the count guard); and every .v file
   under check/, at any depth outside check/regression/, is the source of
   an entry of CHECK_FILES or one of the four files of
   HISTORICAL_CHECK_FILES, which scripts/snapshot_baselines.py compiles at
   their baselines only (the completeness guard). A key of FIXED_FILES
   exempts no file from it.
38. Step 18, the snapshots and the identities. Rule 30 (d) and (e) apply
   to two new snapshots: SnapshotShifted, the frozen files of rule 36 at
   SHIFTED_BASELINE; and SnapshotShiftedDefinitions, the characterization
   lemmas of check/ShiftedDefinitions.v against the library at 7c370d9,
   where that file was written (the code of library/ and extension/ is the
   same at the two commits), a characterization snapshot. Step 18 changes
   four files of rule 35, SHIFTED_CHANGED (scripts/snapshot_baselines.py,
   check/snapshots/REFERENCES.json, check/identity/inventory.json and
   check/identity/REFERENCES.json), by additions; rule 35 applies to the
   other files, and these four, like every file that step 18 adds, have
   their SHA-256 in FIXED_FILES or their code in NEW_CHECK_CODE.
39. Step 18, the pin. The seventeen files of CHECKS_EXACT_SHIFTED (the seven
   axiom checks of rule 37 with their expected lists,
   check/ShiftedDefinitions.v, check/ShiftedIdentities.v and
   check/ShiftedReports.v) and the twelve files of MACHINERY_SHIFTED (the
   four files of SHIFTED_CHANGED, the two snapshot files of rule 38 with
   their references, and their two identity drivers with their references)
   are byte-identical to the commit CHECKS_SHIFTED_BASELINE (the step 18
   integration commit), a separate baseline. Every file that rule 35 no
   longer compares is among them. The older baselines, the pins of rules 31
   and 35 for every other file and check/frozen-baseline do not change.
"""

import argparse
import hashlib
import json
import re
import secrets
import subprocess
import sys
import types
from pathlib import Path
from typing import NamedTuple

ROOT = Path(__file__).resolve().parent.parent


def _load(name, path):
    """A module of scripts/, compiled from its source: the checker does not
    change sys.path (python3 -I keeps scripts/ out of it), and it never reads
    the bytecode cached in scripts/__pycache__/, which python3 -B does not
    prevent and which can stand for another source (E36)."""
    for component in (path, *path.parents):
        if component == ROOT:
            break
        if component.is_symlink():
            raise SystemExit(f"{component}: a checker input is a symlink")
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(Path(path).read_bytes(), str(path), "exec"), module.__dict__)
    return module


rocq_lex = _load("rocq_lex", ROOT / "scripts" / "rocq_lex.py")
identity_sidecars = _load("identity_sidecars", ROOT / "scripts" / "identity_sidecars.py")

FROZEN = [
    "theories/MainStatement.v",
    "theories/MainTheorem.v",
    "theories/PaperMainResults.v",
    "theories/PaperMainDefinitions.v",
    "theories/GaussianProbabilityProductDefinitions.v",
    "theories/GaussianProbabilityDefinitions.v",
    "theories/GaussianDefinitions.v",
    "theories/AnalysisIntegralDefinitions.v",
]
EXACT = ["check/Assumptions.v", "check/assumptions.expected"]
EXTENSION_FROZEN = [
    "extension/UniversalityDefinitions.v",
    "extension/UniversalityStatement.v",
]
EXTENSION_BASELINE = "3c6afa103ccd56c7d98bc59cb253d5d40d13fda0"
PHASE6_FROZEN = [
    "extension/MixtureDefinitions.v",
    "extension/MixtureStatement.v",
    "extension/PairedDefinitions.v",
    "extension/PairedStatement.v",
]
PHASE6_BASELINE = "eef46941972935dfaaef689a853f94d7e7d4798c"
CHECKS_EXACT = [
    "check/UniversalityAssumptions.v",
    "check/universality_assumptions.expected",
    "check/MixtureAssumptions.v",
    "check/mixture_assumptions.expected",
    "check/PairedAssumptions.v",
    "check/paired_assumptions.expected",
]
CHECKS_BASELINE = "c3e555eba4d2d3958d76418c21feebcc241510fc"
CHECKS_EXACT_P8 = [
    "check/LatentSignAssumptions.v",
    "check/latent_sign_assumptions.expected",
    "check/CountableAssumptions.v",
    "check/countable_assumptions.expected",
    "check/ConditionAssumptions.v",
    "check/condition_assumptions.expected",
    "check/LatentScopeAssumptions.v",
    "check/latent_scope_assumptions.expected",
]
CHECKS_P8_BASELINE = "a89ed1e6e29e1041a9a108d82f85bc84620bdd3d"
CHECKS_EXACT_P9 = [
    "check/RobustAssumptions.v",
    "check/robust_assumptions.expected",
    "check/LatentTensorAssumptions.v",
    "check/latent_tensor_assumptions.expected",
    "check/ContinuousLatentAssumptions.v",
    "check/continuous_latent_assumptions.expected",
    "check/ConditionEndpointsAssumptions.v",
    "check/condition_endpoints_assumptions.expected",
]
CHECKS_P9_BASELINE = "e4c46e12d61a28bed6047968565c8424b505319b"
CHECKS_EXACT_P10 = [
    "check/ConditionRobustAssumptions.v",
    "check/condition_robust_assumptions.expected",
    "check/LatentTensorUpperAssumptions.v",
    "check/latent_tensor_upper_assumptions.expected",
]
CHECKS_P10_BASELINE = "eda8a0651798999ec6b9f677532107aae60b0623"
CHECKS_EXACT_P11 = [
    "check/ConditionKappaCurveAssumptions.v",
    "check/condition_kappa_curve_assumptions.expected",
    "check/ConditionKappaAssumptions.v",
    "check/condition_kappa_assumptions.expected",
    "check/ConditionKappaRobustAssumptions.v",
    "check/condition_kappa_robust_assumptions.expected",
]
CHECKS_P11_BASELINE = "d29b278ff7300472a0b572a66cfd335ae262509c"
CHECKS_EXACT_P12 = [
    "check/MatrixSeriesAssumptions.v",
    "check/matrix_series_assumptions.expected",
    "check/TensorPackingAssumptions.v",
    "check/tensor_packing_assumptions.expected",
    "check/GoeEdgeAssumptions.v",
    "check/goe_edge_assumptions.expected",
    "check/SKGapAssumptions.v",
    "check/sk_gap_assumptions.expected",
    "check/PsdSplittingAssumptions.v",
    "check/psd_splitting_assumptions.expected",
    "check/PerceptronSignAssumptions.v",
    "check/perceptron_sign_assumptions.expected",
    "check/SatVarianceAssumptions.v",
    "check/sat_variance_assumptions.expected",
]
CHECKS_P12_BASELINE = "495929a550250684dcad654988436af67f808210"
CHECKS_EXACT_P13 = [
    "check/SatThresholdAssumptions.v",
    "check/sat_threshold_assumptions.expected",
    "check/PsdNormalizationAssumptions.v",
    "check/psd_normalization_assumptions.expected",
    "check/ProductSmoothingAssumptions.v",
    "check/product_smoothing_assumptions.expected",
    "check/MinSuperadditiveAssumptions.v",
    "check/min_superadditive_assumptions.expected",
    "check/Phase13Definitions.v",
    "check/LibraryStatements.v",
]
MACHINERY_P13 = [
    "Makefile",
    "scripts/export_from_ellipsoid_rocq.py",
    "scripts/stale_citations.py",
    "scripts/unused.py",
    "scripts/rocq_lex.py",
    "scripts/test_rocq_lex.py",
    "scripts/run_checks.py",
    "scripts/snapshot_baselines.py",
    "scripts/run_regressions.py",
    "scripts/source_inventory.py",
    "scripts/test_source_inventory.py",
    "scripts/test_command_heads.py",
    "scripts/test_check_runner.py",
    "scripts/test_report_outputs.py",
    "scripts/test_dependency_consistency.py",
    "scripts/test_regression_cleanup.py",
    "scripts/identity_sidecars.py",
    "scripts/test_identity_sidecars.py",
    "check/TheoremIdentities.v",
    "check/Reports.v",
    "check/MatrixSigmaRing.v",
]
MACHINERY_DIRS_P13 = ["check/identity", "check/snapshots", "check/regression"]
CHECKS_P13_BASELINE = "c5bdf87f827050ebd6a4680d7ba8ddf4fb59ed6f"
TUPLE_PROD = "library/probability/lindeberg.v"
LATENT_FROZEN = [
    "extension/LatentSignDefinitions.v",
    "extension/LatentSignStatement.v",
]
LATENT_BASELINE = "d4de51d11b12b50afa4c96a7fa90b37f9f6b92ee"
PHASE8_FROZEN = [
    "extension/CountableMixtureDefinitions.v",
    "extension/CountableMixtureStatement.v",
    "extension/ConditionDefinitions.v",
    "extension/ConditionStatement.v",
    "extension/LatentSignScope.v",
]
PHASE8_BASELINE = "5442e84ba6cdc9ad69848040ea4483269e578896"
PHASE9_FROZEN = [
    "extension/RobustDefinitions.v",
    "extension/RobustStatement.v",
    "extension/LatentTensorization.v",
    "extension/ContinuousLatent.v",
    "extension/ConditionEndpoints.v",
]
PHASE9_BASELINE = "1c05ffcbebc81492639e7f9afc7b3dc2b88021e0"
PHASE10_FROZEN = [
    "extension/ConditionRobustStatement.v",
    "extension/LatentTensorUpper.v",
]
PHASE10_BASELINE = "b26eb1e0eff32371248c211ece597fc9bc3463f9"
PHASE11_FROZEN = [
    "extension/ConditionKappaDefinitions.v",
    "extension/ConditionKappaCurveStatement.v",
    "extension/ConditionKappaStatement.v",
    "extension/ConditionKappaRobustStatement.v",
]
PHASE11_BASELINE = "c5f41c44e5bc2622f6dfd940c654553503e9eb1d"
PHASE12_B1_FROZEN = [
    "applications/MatrixSeriesStatement.v",
    "applications/GoeEdgeStatement.v",
    "applications/PsdSplittingStatement.v",
]
PHASE12_B1_BASELINE = "fc76edfc953cac79f4fa258a3228cb536784cded"
PHASE12_B2_FROZEN = [
    "applications/TensorPackingStatement.v",
    "applications/SKGapDefinitions.v",
    "applications/SKGapStatement.v",
    "applications/PerceptronSignDefinitions.v",
    "applications/PerceptronSignStatement.v",
    "applications/SatVarianceDefinitions.v",
    "applications/SatVarianceStatement.v",
]
PHASE12_B2_BASELINE = "0d5afbac072113544fd4c46451a7b6397b7344b3"
PHASE13_B1_FROZEN = [
    "applications/SatThresholdDefinitions.v",
    "applications/SatThresholdStatement.v",
    "applications/MinSuperadditiveStatement.v",
]
PHASE13_B1_BASELINE = "46e45c84b99a50663205933ae501da029dd66098"
PHASE13_B2_FROZEN = [
    "applications/PsdNormalizationStatement.v",
    "applications/ProductSmoothingStatement.v",
]
PHASE13_B2_BASELINE = "46e45c84b99a50663205933ae501da029dd66098"
PHASE13_B3_FROZEN = [
    "applications/PsdRankDefinitions.v",
    "applications/PsdRankStatement.v",
]
PHASE13_B3_BASELINE = "46e45c84b99a50663205933ae501da029dd66098"
PHASE14_FROZEN = [
    "applications/PsdLiftDefinitions.v",
    "applications/PsdLiftStatement.v",
]
PHASE14_BASELINE = "39f58468aeaa024a54509c1b684c3a40e208e5d8"
# Rule 35: the files that commit P of phase 14 adds or changes, pinned to it.
CHECKS_EXACT_P14 = [
    "check/PsdRankAssumptions.v",
    "check/psd_rank_assumptions.expected",
    "check/PsdLiftAssumptions.v",
    "check/psd_lift_assumptions.expected",
    "check/Phase14Definitions.v",
    "check/Phase14Statements.v",
    "check/Phase14Identities.v",
    "check/Phase14Reports.v",
]
MACHINERY_P14 = [
    "scripts/snapshot_baselines.py",
    "scripts/identity_sidecars.py",
    "check/snapshots/REFERENCES.json",
    "check/identity/inventory.json",
    "check/identity/REFERENCES.json",
    "check/snapshots/SnapshotPhase14.v",
    "check/snapshots/SnapshotPhase14.txt",
    "check/snapshots/SnapshotPhase14Definitions.v",
    "check/snapshots/SnapshotPhase14Definitions.txt",
    "check/snapshots/SnapshotPhase14Statements.v",
    "check/snapshots/SnapshotPhase14Statements.txt",
    "check/snapshots/SnapshotAcceptedStatements14.v",
    "check/snapshots/SnapshotAcceptedStatements14.txt",
    "check/snapshots/AcceptedConversions14.v",
    "check/identity/IdentitySnapshotPhase14.v",
    "check/identity/IdentitySnapshotPhase14.json",
    "check/identity/IdentitySnapshotPhase14Definitions.v",
    "check/identity/IdentitySnapshotPhase14Definitions.json",
    "check/identity/IdentitySnapshotPhase14Statements.v",
    "check/identity/IdentitySnapshotPhase14Statements.json",
]
CHECKS_P14_BASELINE = "bdcb12c65c0933c7a07fd8e6ce7e6a0f9bee2b3a"
# Rule 36: the seven statement files of the shifted-Gaussian extension.
SHIFTED_FROZEN = [
    "extension/ShiftedConditionStatement.v",
    "extension/ShiftedGaussianStatement.v",
    "extension/ShiftedQuadricStatement.v",
    "extension/ShiftedErrorStatement.v",
    "extension/ShiftedMixtureUnsatStatement.v",
    "extension/ShiftedMixtureSatStatement.v",
    "extension/ShiftedSignStatement.v",
]
SHIFTED_BASELINE = "51c2e14d5c2d75469f8147901bc8f664d33d4b6c"
# Rule 39: the files that the step 18 integration commit adds or changes in
# check/ and the machinery, pinned to it.
CHECKS_EXACT_SHIFTED = [
    "check/ShiftedConditionAssumptions.v",
    "check/ShiftedGaussianAssumptions.v",
    "check/ShiftedQuadricAssumptions.v",
    "check/ShiftedErrorAssumptions.v",
    "check/ShiftedMixtureUnsatAssumptions.v",
    "check/ShiftedMixtureSatAssumptions.v",
    "check/ShiftedSignAssumptions.v",
    "check/shifted_condition_assumptions.expected",
    "check/shifted_gaussian_assumptions.expected",
    "check/shifted_quadric_assumptions.expected",
    "check/shifted_error_assumptions.expected",
    "check/shifted_mixture_unsat_assumptions.expected",
    "check/shifted_mixture_sat_assumptions.expected",
    "check/shifted_sign_assumptions.expected",
    "check/ShiftedDefinitions.v",
    "check/ShiftedIdentities.v",
    "check/ShiftedReports.v",
]
MACHINERY_SHIFTED = [
    "scripts/snapshot_baselines.py",
    "check/snapshots/REFERENCES.json",
    "check/identity/inventory.json",
    "check/identity/REFERENCES.json",
    "check/snapshots/SnapshotShifted.v",
    "check/snapshots/SnapshotShifted.txt",
    "check/snapshots/SnapshotShiftedDefinitions.v",
    "check/snapshots/SnapshotShiftedDefinitions.txt",
    "check/identity/IdentitySnapshotShifted.v",
    "check/identity/IdentitySnapshotShifted.json",
    "check/identity/IdentitySnapshotShiftedDefinitions.v",
    "check/identity/IdentitySnapshotShiftedDefinitions.json",
]
CHECKS_SHIFTED_BASELINE = "cc6fc9d49c73f74e0bccdb7f7a7d5716ce02958a"
# Rule 38: the files of rule 35 that step 18 changes.
SHIFTED_CHANGED = [
    "scripts/snapshot_baselines.py",
    "check/snapshots/REFERENCES.json",
    "check/identity/inventory.json",
    "check/identity/REFERENCES.json",
]
# Rule 37: the files under check/ that no CheckFile compiles, the accepted
# bodies and the conversions, which scripts/snapshot_baselines.py compiles at
# their baselines only (the completeness guard).
HISTORICAL_CHECK_FILES = [
    "check/snapshots/SnapshotAcceptedStatements.v",
    "check/snapshots/SnapshotAcceptedStatements14.v",
    "check/snapshots/AcceptedConversions.v",
    "check/snapshots/AcceptedConversions14.v",
]
# Rule 34: the files of rule 31 that the extension of phase 14 changes.
P14_CHANGED = [
    "scripts/snapshot_baselines.py",
    "scripts/identity_sidecars.py",
    "check/snapshots/REFERENCES.json",
    "check/identity/inventory.json",
    "check/identity/REFERENCES.json",
]
LAMBDA_MAX = "library/matrix/lambda_max.v"
APPLICATIONS_DEFINITIONS = "check/ApplicationsDefinitions.v"
APPLICATIONS_DEFINITIONS_CHECK = (
    'From HB Require Import structures. From mathcomp Require Import '
    'all_ssreflect_compat ssralg ssrnum matrix. From mathcomp Require '
    'Import sesquilinear boolp classical_sets functions. From mathcomp '
    'Require Import reals ereal topology normedtype sequences exp. From '
    'mathcomp Require Import measure lebesgue_measure lebesgue_integral. '
    'From mathcomp Require Import measurable_realfun probability. From '
    'GaussianAnalysis.gaussian Require Import measurable_matrix gauss. '
    'From GaussianAnalysis.matrix Require Import euclidean opnorm '
    'psd_part. From GaussianAnalysis.random_matrix Require Import goe. '
    'Import GRing.Theory Num.Theory. Local Open Scope ring_scope. Local '
    'Open Scope classical_set_scope. Lemma mxdot_characterization (R : '
    "realType) m n (A B : 'M[R]_(m, n)) : mxdot A B = \\sum_i \\sum_j A i j "
    '* B i j. Proof. by []. Qed. Lemma frobenius_characterization (R : '
    "realType) m n (A : 'M[R]_(m, n)) : frobenius A = Num.sqrt (\\sum_i "
    '\\sum_j A i j ^+ 2). Proof. by rewrite /frobenius '
    'mxdot_characterization; under eq_bigr do under eq_bigr do rewrite '
    '-expr2. Qed. Lemma opnorm_characterization (R : realType) m n (A : '
    "'M[R]_(m, n)) : opnorm A = sup [set frobenius (A *m x) | x in [set x "
    ": 'cV[R]_n | frobenius x <= 1]]. Proof. by []. Qed. Lemma "
    "psdmx_characterization (R : realType) n (A : 'M[R]_n) : psdmx A <-> "
    "A \\is symmetricmx /\\ forall x : 'cV[R]_n, 0 <= (x^T *m A *m x) 0 0. "
    'Proof. by split => -[As Ap]; split => // x; have := Ap x; rewrite '
    'mxdot_colE mulmxA. Qed. Lemma goe_mx_characterization (R : realType) '
    "d (a : 'rV[R]_(d * d)) : goe_mx a = (Num.sqrt (2 * d%:R))^-1 *: "
    '(vec_mx a + (vec_mx a)^T). Proof. by []. Qed. Lemma '
    'matrix_measurable_characterization {dT} (T : measurableType dT) m n '
    ": @measurable _ 'M[T]_(m, n) = <<s [set [set M : 'M[T]_(m, n) | "
    "forall i j, A i j (M i j)] | A in [set A : 'I_m -> 'I_n -> set T | "
    'forall i j, measurable (A i j)]] >>. Proof. exact: '
    'measurable_mxboxes. Qed. Lemma gauss_characterization (R : realType) '
    "n (A : 'I_n -> set R) : (forall i, measurable (A i)) -> gauss n [set "
    "x : 'rV[R]_n | forall i, A i (x 0 i)] = (\\prod_(i < n) normal_prob 0 "
    '1 (A i))%E. Proof. exact: gauss_box. Qed. Lemma gauss_determined (R '
    ": realType) n (P : {measure set 'rV[R]_n -> \\bar R}) : (forall A : "
    "'I_n -> set R, (forall i, measurable (A i)) -> P [set x : 'rV[R]_n | "
    'forall i, A i (x 0 i)] = (\\prod_(i < n) normal_prob 0 1 (A i))%E) -> '
    'forall X, measurable X -> P X = gauss n X. Proof. exact: '
    'gauss_unique. Qed.')
PHASE14_DEFINITIONS = "check/Phase14Definitions.v"
PHASE14_DEFINITIONS_CHECK = ('From HB Require Import structures. From mathcomp Require Import all_'
    'ssreflect_compat fingroup perm ssralg ssrnum. From mathcomp Require '
    'Import matrix reals. From GaussianAnalysis.matrix Require Import mul'
    'tiplicity. From GaussianAnalysis.combinatorics Require Import expand'
    'er. Import GRing.Theory Num.Theory. Local Open Scope ring_scope. Lem'
    "ma ksubset_characterization (k w : nat) : ksubset k w = {A : {set 'I"
    '_k} | #|A| == w}. Proof. by []. Qed. Lemma ksubset_mx_characterizati'
    "on (R : realType) (k w : nat) (s : {perm 'I_k}) : ksubset_mx R w s ="
    ' \\matrix_(i < #|{: ksubset k w}|, j < #|{: ksubset k w}|) ((val (enu'
    'm_val i : ksubset k w) == [set s x | x in val (enum_val j : ksubset '
    'k w)]) %:R : R). Proof. by []. Qed. Lemma perm_cut_characterization '
    "(d l : nat) (s : 'I_d -> {perm 'I_l}) (W : {set 'I_(l + l)}) : perm_"
    "cut s W = [set e : 'I_d * 'I_l | (lshift l e.2 \\in W) != (rshift l ("
    's e.1 e.2) \\in W)]. Proof. by []. Qed. Print Assumptions perm_cut_ch'
    'aracterization.')
PHASE13_DEFINITIONS = "check/Phase13Definitions.v"
PHASE13_DEFINITIONS_OUTPUT = "build/phase13_definitions.txt"
# The code of check/Phase13Definitions.v at each freeze of phase 13, in
# order; each is a prefix of the next, and the file has the last one.
PHASE13_DEFINITIONS_FREEZES = [
    # freeze 1 (batch 1): unif_mean, unif_var, binomial_mean, linear_op,
    # monotone_op, meet_avg
    (
    'From HB Require Import structures. From mathcomp Require Import al'
    'l_ssreflect_compat ssralg ssrnum. From GaussianAnalysis.probabilit'
    'y Require Import finite_mean binomial_mean. From GaussianAnalysis.'
    'probability Require Import commuting_operators. Import GRing.Theor'
    'y Num.Theory. Local Open Scope ring_scope. Lemma unif_mean_charact'
    'erization (R : realFieldType) (T : finType) (f : T -> R) : unif_me'
    'an f = (#|T|%:R)^-1 * \\sum_(x : T) f x. Proof. by []. Qed. Lemma u'
    'nif_var_characterization (R : realFieldType) (T : finType) (f : T '
    '-> R) : unif_var f = (#|T|%:R)^-1 * \\sum_(x : T) (f x - (#|T|%:R)^'
    '-1 * \\sum_(y : T) f y) ^+ 2. Proof. by []. Qed. Lemma binomial_mea'
    'n_characterization (R : numDomainType) (m : nat) (p : R) (f : nat '
    '-> R) : binomial_mean m p f = \\sum_(j < m.+1) (p ^+ j * (1 - p) ^+'
    " (m - j) *+ 'C(m, j)) * f j. Proof. by []. Qed. Lemma linear_op_ch"
    'aracterization (R : numDomainType) (X : Type) (A : (X -> R) -> X -'
    '> R) : linear_op A <-> (forall (f g : X -> R) (x : X), A (fun y =>'
    ' f y + g y) x = A f x + A g x) /\\ (forall (a : R) (f : X -> R) (x '
    ': X), A (fun y => a * f y) x = a * A f x). Proof. by []. Qed. Lemm'
    'a monotone_op_characterization (R : numDomainType) (X : Type) (A :'
    ' (X -> R) -> X -> R) : monotone_op A <-> forall f g : X -> R, (for'
    'all y, f y <= g y) -> forall x, A f x <= A g x. Proof. by []. Qed.'
    ' Lemma meet_avg_characterization (R : realFieldType) (T C : finTyp'
    'e) (E : C -> {set T}) (f : {set T} -> R) (S : {set T}) : meet_avg '
    'E f S = (#|C|%:R)^-1 * \\sum_(c : C) f (S :&: E c). Proof. by []. Q'
    'ed. Print Assumptions meet_avg_characterization.'),
    # freeze 2 (batch 2): the definitions of freeze 1, then bdot, bchar,
    # blk_deg, blk_dist, fcoef, low_blk_deg, prob_vec, prod_avg,
    # smoothing_hyps, weighted_gram, psd_factorization
    (
    'From HB Require Import structures. From mathcomp Require Import al'
    'l_ssreflect_compat ssralg ssrnum. From GaussianAnalysis.probabilit'
    'y Require Import finite_mean binomial_mean. From GaussianAnalysis.'
    'probability Require Import commuting_operators. Import GRing.Theor'
    'y Num.Theory. Local Open Scope ring_scope. Lemma unif_mean_charact'
    'erization (R : realFieldType) (T : finType) (f : T -> R) : unif_me'
    'an f = (#|T|%:R)^-1 * \\sum_(x : T) f x. Proof. by []. Qed. Lemma u'
    'nif_var_characterization (R : realFieldType) (T : finType) (f : T '
    '-> R) : unif_var f = (#|T|%:R)^-1 * \\sum_(x : T) (f x - (#|T|%:R)^'
    '-1 * \\sum_(y : T) f y) ^+ 2. Proof. by []. Qed. Lemma binomial_mea'
    'n_characterization (R : numDomainType) (m : nat) (p : R) (f : nat '
    '-> R) : binomial_mean m p f = \\sum_(j < m.+1) (p ^+ j * (1 - p) ^+'
    " (m - j) *+ 'C(m, j)) * f j. Proof. by []. Qed. Lemma linear_op_ch"
    'aracterization (R : numDomainType) (X : Type) (A : (X -> R) -> X -'
    '> R) : linear_op A <-> (forall (f g : X -> R) (x : X), A (fun y =>'
    ' f y + g y) x = A f x + A g x) /\\ (forall (a : R) (f : X -> R) (x '
    ': X), A (fun y => a * f y) x = a * A f x). Proof. by []. Qed. Lemm'
    'a monotone_op_characterization (R : numDomainType) (X : Type) (A :'
    ' (X -> R) -> X -> R) : monotone_op A <-> forall f g : X -> R, (for'
    'all y, f y <= g y) -> forall x, A f x <= A g x. Proof. by []. Qed.'
    ' Lemma meet_avg_characterization (R : realFieldType) (T C : finTyp'
    'e) (E : C -> {set T}) (f : {set T} -> R) (S : {set T}) : meet_avg '
    'E f S = (#|C|%:R)^-1 * \\sum_(c : C) f (S :&: E c). Proof. by []. Q'
    'ed. Print Assumptions meet_avg_characterization. From mathcomp Req'
    'uire Import zmodp matrix reals. From GaussianAnalysis.fourier Requ'
    'ire Import boolean_fourier product_smoothing. From GaussianAnalysi'
    's.matrix Require Import psd_part psd_factorization. Lemma bdot_cha'
    "racterization (t a : nat) (p y : 'M['F_2]_(t, a)) : bdot p y = \\su"
    'm_(i < t) \\sum_(j < a) p i j * y i j. Proof. by []. Qed. Lemma bch'
    "ar_characterization (R : pzRingType) (t a : nat) (p y : 'M['F_2]_("
    't, a)) : bchar R p y = (-1) ^+ nat_of_ord (\\sum_(i < t) \\sum_(j < '
    'a) p i j * y i j). Proof. by []. Qed. Lemma blk_deg_characterizati'
    "on (t a : nat) (p : 'M['F_2]_(t, a)) : blk_deg p = #|[set i : 'I_t"
    ' | row i p != 0]|. Proof. by []. Qed. Lemma blk_dist_characterizat'
    "ion (t a : nat) (p q : 'M['F_2]_(t, a)) : blk_dist p q = #|[set i "
    ": 'I_t | row i p != row i q]|. Proof. by []. Qed. Lemma fcoef_char"
    'acterization (R : numFieldType) (t a : nat) (V : lmodType R) (f : '
    "'M['F_2]_(t, a) -> V) (p : 'M['F_2]_(t, a)) : fcoef f p = (#|{: 'M"
    "['F_2]_(t, a)}|%:R)^-1 *: \\sum_(y : 'M['F_2]_(t, a)) (-1) ^+ nat_o"
    'f_ord (\\sum_(i < t) \\sum_(j < a) p i j * y i j) *: f y. Proof. by '
    '[]. Qed. Lemma low_blk_deg_characterization (R : numFieldType) (t '
    "a : nat) (V : lmodType R) (D : nat) (f : 'M['F_2]_(t, a) -> V) : l"
    "ow_blk_deg D f <-> forall p : 'M['F_2]_(t, a), (D < #|[set i : 'I_"
    "t | row i p != 0%R]|)%N -> (#|{: 'M['F_2]_(t, a)}|%:R)^-1 *: \\sum_"
    "(y : 'M['F_2]_(t, a)) (-1) ^+ nat_of_ord (\\sum_(i < t) \\sum_(j < a"
    ') p i j * y i j) *: f y = 0. Proof. by []. Qed. Lemma prob_vec_cha'
    'racterization (R : numDomainType) (T : finType) (w : T -> R) : pro'
    'b_vec w <-> (forall x, 0 <= w x) /\\ \\sum_x w x = 1. Proof. by []. '
    'Qed. Lemma prod_avg_characterization (R : numDomainType) (X M : fi'
    "nType) (t a : nat) (V : lmodType R) (pi : 'I_t -> M -> 'rV['F_2]_a"
    " -> X -> R) (F : t.-tuple X -> V) (m : t.-tuple M) (y : 'M['F_2]_("
    't, a)) : prod_avg pi F m y = \\sum_(x : t.-tuple X) (\\prod_(i < t) '
    'pi i (tnth m i) (row i y) (tnth x i)) *: F x. Proof. by []. Qed. L'
    'emma smoothing_hyps_characterization (R : numDomainType) (X M : fi'
    "nType) (t a : nat) (mu : 'I_t -> X -> R) (nu : 'I_t -> M -> R) (pi"
    " : 'I_t -> M -> 'rV['F_2]_a -> X -> R) (theta : R) : smoothing_hyp"
    's mu nu pi theta <-> [/\\ forall i, (forall x, 0 <= mu i x) /\\ \\sum'
    '_x mu i x = 1, forall i, (forall m, 0 <= nu i m) /\\ \\sum_m nu i m '
    '= 1, forall i m y, (forall x, 0 <= pi i m y x) /\\ \\sum_x pi i m y '
    'x = 1, forall i y x, \\sum_m nu i m * pi i m y x = mu i x & forall '
    'i y (g : X -> R), \\sum_m nu i m * (\\sum_x pi i m y x * g x - \\sum_'
    'x mu i x * g x) ^+ 2 <= theta * \\sum_x mu i x * g x ^+ 2]. Proof. '
    'by []. Qed. Lemma weighted_gram_characterization (R : numFieldType'
    ") (t a r : nat) (lambda : R) (Rw : nat) (H : 'M['F_2]_(t, a) -> 'M"
    "[R]_(Rw, r)) (q : 'M['F_2]_(t, a)) : weighted_gram lambda H q = \\s"
    "um_(p : 'M['F_2]_(t, a)) lambda ^+ #|[set i : 'I_t | row i q != ro"
    "w i p]| *: (((#|{: 'M['F_2]_(t, a)}|%:R)^-1 *: \\sum_(y : 'M['F_2]_"
    '(t, a)) (-1) ^+ nat_of_ord (\\sum_(i < t) \\sum_(j < a) p i j * y i '
    "j) *: H y) *m ((#|{: 'M['F_2]_(t, a)}|%:R)^-1 *: \\sum_(y : 'M['F_2"
    ']_(t, a)) (-1) ^+ nat_of_ord (\\sum_(i < t) \\sum_(j < a) p i j * y '
    'i j) *: H y)^T). Proof. by []. Qed. Lemma psd_factorization_charac'
    'terization (R : realType) (I J : finType) (A : I -> J -> R) (r : n'
    "at) : psd_factorization A r <-> exists (F : I -> 'M[R]_r) (G : J -"
    "> 'M[R]_r), [/\\ forall i, psdmx (F i), forall j, psdmx (G j) & for"
    'all i j, A i j = \\tr (F i *m G j)]. Proof. by []. Qed. Print Assum'
    'ptions psd_factorization_characterization.'),
    # freeze 3 (batch 3)
    (
    'From HB Require Import structures. From mathcomp Require Import al'
    'l_ssreflect_compat ssralg ssrnum. From GaussianAnalysis.probabilit'
    'y Require Import finite_mean binomial_mean. From GaussianAnalysis.'
    'probability Require Import commuting_operators. Import GRing.Theor'
    'y Num.Theory. Local Open Scope ring_scope. Lemma unif_mean_charact'
    'erization (R : realFieldType) (T : finType) (f : T -> R) : unif_me'
    'an f = (#|T|%:R)^-1 * \\sum_(x : T) f x. Proof. by []. Qed. Lemma u'
    'nif_var_characterization (R : realFieldType) (T : finType) (f : T '
    '-> R) : unif_var f = (#|T|%:R)^-1 * \\sum_(x : T) (f x - (#|T|%:R)^'
    '-1 * \\sum_(y : T) f y) ^+ 2. Proof. by []. Qed. Lemma binomial_mea'
    'n_characterization (R : numDomainType) (m : nat) (p : R) (f : nat '
    '-> R) : binomial_mean m p f = \\sum_(j < m.+1) (p ^+ j * (1 - p) ^+'
    " (m - j) *+ 'C(m, j)) * f j. Proof. by []. Qed. Lemma linear_op_ch"
    'aracterization (R : numDomainType) (X : Type) (A : (X -> R) -> X -'
    '> R) : linear_op A <-> (forall (f g : X -> R) (x : X), A (fun y =>'
    ' f y + g y) x = A f x + A g x) /\\ (forall (a : R) (f : X -> R) (x '
    ': X), A (fun y => a * f y) x = a * A f x). Proof. by []. Qed. Lemm'
    'a monotone_op_characterization (R : numDomainType) (X : Type) (A :'
    ' (X -> R) -> X -> R) : monotone_op A <-> forall f g : X -> R, (for'
    'all y, f y <= g y) -> forall x, A f x <= A g x. Proof. by []. Qed.'
    ' Lemma meet_avg_characterization (R : realFieldType) (T C : finTyp'
    'e) (E : C -> {set T}) (f : {set T} -> R) (S : {set T}) : meet_avg '
    'E f S = (#|C|%:R)^-1 * \\sum_(c : C) f (S :&: E c). Proof. by []. Q'
    'ed. Print Assumptions meet_avg_characterization. From mathcomp Req'
    'uire Import zmodp matrix reals. From GaussianAnalysis.fourier Requ'
    'ire Import boolean_fourier product_smoothing. From GaussianAnalysi'
    's.matrix Require Import psd_part psd_factorization. Lemma bdot_cha'
    "racterization (t a : nat) (p y : 'M['F_2]_(t, a)) : bdot p y = \\su"
    'm_(i < t) \\sum_(j < a) p i j * y i j. Proof. by []. Qed. Lemma bch'
    "ar_characterization (R : pzRingType) (t a : nat) (p y : 'M['F_2]_("
    't, a)) : bchar R p y = (-1) ^+ nat_of_ord (\\sum_(i < t) \\sum_(j < '
    'a) p i j * y i j). Proof. by []. Qed. Lemma blk_deg_characterizati'
    "on (t a : nat) (p : 'M['F_2]_(t, a)) : blk_deg p = #|[set i : 'I_t"
    ' | row i p != 0]|. Proof. by []. Qed. Lemma blk_dist_characterizat'
    "ion (t a : nat) (p q : 'M['F_2]_(t, a)) : blk_dist p q = #|[set i "
    ": 'I_t | row i p != row i q]|. Proof. by []. Qed. Lemma fcoef_char"
    'acterization (R : numFieldType) (t a : nat) (V : lmodType R) (f : '
    "'M['F_2]_(t, a) -> V) (p : 'M['F_2]_(t, a)) : fcoef f p = (#|{: 'M"
    "['F_2]_(t, a)}|%:R)^-1 *: \\sum_(y : 'M['F_2]_(t, a)) (-1) ^+ nat_o"
    'f_ord (\\sum_(i < t) \\sum_(j < a) p i j * y i j) *: f y. Proof. by '
    '[]. Qed. Lemma low_blk_deg_characterization (R : numFieldType) (t '
    "a : nat) (V : lmodType R) (D : nat) (f : 'M['F_2]_(t, a) -> V) : l"
    "ow_blk_deg D f <-> forall p : 'M['F_2]_(t, a), (D < #|[set i : 'I_"
    "t | row i p != 0%R]|)%N -> (#|{: 'M['F_2]_(t, a)}|%:R)^-1 *: \\sum_"
    "(y : 'M['F_2]_(t, a)) (-1) ^+ nat_of_ord (\\sum_(i < t) \\sum_(j < a"
    ') p i j * y i j) *: f y = 0. Proof. by []. Qed. Lemma prob_vec_cha'
    'racterization (R : numDomainType) (T : finType) (w : T -> R) : pro'
    'b_vec w <-> (forall x, 0 <= w x) /\\ \\sum_x w x = 1. Proof. by []. '
    'Qed. Lemma prod_avg_characterization (R : numDomainType) (X M : fi'
    "nType) (t a : nat) (V : lmodType R) (pi : 'I_t -> M -> 'rV['F_2]_a"
    " -> X -> R) (F : t.-tuple X -> V) (m : t.-tuple M) (y : 'M['F_2]_("
    't, a)) : prod_avg pi F m y = \\sum_(x : t.-tuple X) (\\prod_(i < t) '
    'pi i (tnth m i) (row i y) (tnth x i)) *: F x. Proof. by []. Qed. L'
    'emma smoothing_hyps_characterization (R : numDomainType) (X M : fi'
    "nType) (t a : nat) (mu : 'I_t -> X -> R) (nu : 'I_t -> M -> R) (pi"
    " : 'I_t -> M -> 'rV['F_2]_a -> X -> R) (theta : R) : smoothing_hyp"
    's mu nu pi theta <-> [/\\ forall i, (forall x, 0 <= mu i x) /\\ \\sum'
    '_x mu i x = 1, forall i, (forall m, 0 <= nu i m) /\\ \\sum_m nu i m '
    '= 1, forall i m y, (forall x, 0 <= pi i m y x) /\\ \\sum_x pi i m y '
    'x = 1, forall i y x, \\sum_m nu i m * pi i m y x = mu i x & forall '
    'i y (g : X -> R), \\sum_m nu i m * (\\sum_x pi i m y x * g x - \\sum_'
    'x mu i x * g x) ^+ 2 <= theta * \\sum_x mu i x * g x ^+ 2]. Proof. '
    'by []. Qed. Lemma weighted_gram_characterization (R : numFieldType'
    ") (t a r : nat) (lambda : R) (Rw : nat) (H : 'M['F_2]_(t, a) -> 'M"
    "[R]_(Rw, r)) (q : 'M['F_2]_(t, a)) : weighted_gram lambda H q = \\s"
    "um_(p : 'M['F_2]_(t, a)) lambda ^+ #|[set i : 'I_t | row i q != ro"
    "w i p]| *: (((#|{: 'M['F_2]_(t, a)}|%:R)^-1 *: \\sum_(y : 'M['F_2]_"
    '(t, a)) (-1) ^+ nat_of_ord (\\sum_(i < t) \\sum_(j < a) p i j * y i '
    "j) *: H y) *m ((#|{: 'M['F_2]_(t, a)}|%:R)^-1 *: \\sum_(y : 'M['F_2"
    ']_(t, a)) (-1) ^+ nat_of_ord (\\sum_(i < t) \\sum_(j < a) p i j * y '
    'i j) *: H y)^T). Proof. by []. Qed. Lemma psd_factorization_charac'
    'terization (R : realType) (I J : finType) (A : I -> J -> R) (r : n'
    "at) : psd_factorization A r <-> exists (F : I -> 'M[R]_r) (G : J -"
    "> 'M[R]_r), [/\\ forall i, psdmx (F i), forall j, psdmx (G j) & for"
    'all i j, A i j = \\tr (F i *m G j)]. Proof. by []. Qed. Print Assum'
    'ptions psd_factorization_characterization. From mathcomp Require I'
    'mport classical_sets. From GaussianAnalysis.matrix Require Import '
    'psd_duality. Lemma psd_eval_characterization (R : realType) (n N :'
    " nat) (G : 'I_N -> 'M[R]_n) (F : 'M[R]_n) : psd_eval G F = \\row_j "
    '\\tr (F *m G j). Proof. by []. Qed. Lemma psd_eval_cone_characteriz'
    "ation (R : realType) (n N : nat) (G : 'I_N -> 'M[R]_n) : psd_eval_"
    "cone G = [set \\row_j \\tr (F *m G j) | F in [set F : 'M[R]_n | psdm"
    'x F]]%classic. Proof. by []. Qed. Print Assumptions psd_eval_cone_'
    'characterization.'),
]
# The general statements accepted by the user: (acceptance commit, path,
# name of the Prop definition, the proposition as Print shows it).
INVENTORY = [
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/finite_mean.v',
     'unif_mean_union_statement',
     'forall (R : realFieldType) (T I : finType) (P : I -> pred T), @unif_mean R T (fun x : T => [exists i, P i x]%:R : R) <= \\sum_i @unif_mean R T (fun x : T => (P i x)%:R : R)'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/finite_mean.v',
     'unif_mean_indicatorN_statement',
     'forall (R : realFieldType) (T : finType) (P : pred T), (0 < #|T|)%N -> @unif_mean R T (fun x : T => (~~ P x)%:R : R) = 1 - @unif_mean R T (fun x : T => (P x)%:R : R)'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/finite_mean.v',
     'unif_mean_markov_statement',
     'forall (R : realFieldType) (T : finType) (f : T -> R) (t : R), (forall x : T, 0 <= f x) -> t * @unif_mean R T (fun x : T => (t <= f x)%R%:R : R) <= @unif_mean R T f'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/finite_mean.v',
     'unif_mean_cutoff_statement',
     'forall (R : realFieldType) (T : finType) (f : T -> R) (M t : R), 0 <= t -> (forall x : T, f x <= M) -> @unif_mean R T f <= t + M * @unif_mean R T (fun x : T => (t <= f x)%R%:R : R)'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/finite_mean.v',
     'unif_chebyshev_statement',
     'forall (R : realFieldType) (T : finType) (f : T -> R) (t : R), 0 < t -> @unif_mean R T (fun x : T => (t <= `|f x - @unif_mean R T f|)%R%:R : R) <= @unif_var R T f / t ^+ 2'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/finite_mean.v',
     'unif_mean_tuple_prod_ord_statement',
     "forall (R : realFieldType) (T : finType) (m : nat) (g : 'I_m -> T -> R), @unif_mean R (tuple_tuple_of__canonical__fintype_Finite m T) (fun t : m.-tuple T => \\prod_(i < m) g i (@tnth m T t i)) = \\prod_(i < m) @unif_mean R T (g i)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/finite_mean.v',
     'unif_mean_tuple_prod_set_statement',
     "forall (R : realFieldType) (T : finType) (m : nat) (J : {set 'I_m}) (g : T -> R), (0 < #|T|)%N -> @unif_mean R (tuple_tuple_of__canonical__fintype_Finite m T) (fun t : m.-tuple T => \\prod_(i in J) g (@tnth m T t i)) = @unif_mean R T g ^+ #|J|"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'binomial_mean0_statement',
     'forall (R : numDomainType) (p : R) (f : nat -> R), @binomial_mean R 0 p f = f 0%N'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'binomial_meanS_statement',
     'forall (R : numDomainType) (m : nat) (p : R) (f : nat -> R), @binomial_mean R m.+1 p f = (1 - p) * @binomial_mean R m p f + p * @binomial_mean R m p (fun j : nat => f j.+1)'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'eq_binomial_mean_statement',
     'forall (R : numDomainType) (m : nat) (p : R) (f g : nat -> R), (forall j : nat, (j <= m)%N -> f j = g j) -> @binomial_mean R m p f = @binomial_mean R m p g'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'binomial_mean_cst_statement',
     'forall (R : numDomainType) (m : nat) (p c : R), @binomial_mean R m p (fun=> c) = c'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'binomial_meanD_statement',
     'forall (R : numDomainType) (m : nat) (p : R) (f g : nat -> R), @binomial_mean R m p (fun j : nat => f j + g j) = @binomial_mean R m p f + @binomial_mean R m p g'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'binomial_meanZ_statement',
     'forall (R : numDomainType) (m : nat) (p c : R) (f : nat -> R), @binomial_mean R m p (fun j : nat => c * f j) = c * @binomial_mean R m p f'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'ler_binomial_mean_statement',
     'forall (R : numDomainType) (m : nat) (p : R) (f g : nat -> R), 0 <= p <= 1 -> (forall j : nat, (j <= m)%N -> f j <= g j) -> @binomial_mean R m p f <= @binomial_mean R m p g'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'binomial_mean_id_statement',
     'forall (R : numDomainType) (m : nat) (p : R), @binomial_mean R m p [eta @Algebra.natmul R 1] = m%:R * p'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'binomial_mean_sqr_dev_statement',
     'forall (R : numDomainType) (m : nat) (p : R), @binomial_mean R m p (fun j : nat => (j%:R - m%:R * p) ^+ 2) = m%:R * p * (1 - p)'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'binomial_chebyshev_statement',
     'forall (R : realFieldType) (m : nat) (p t : R), 0 <= p <= 1 -> 0 < t -> @binomial_mean R m p (fun j : nat => (t <= `|j%:R - m%:R * p|)%R%:R) <= m%:R * p * (1 - p) / t ^+ 2'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'binomial_mean_last_statement',
     'forall (R : numDomainType) (m : nat) (p : R) (f : nat -> R), 0 <= p <= 1 -> (forall j : nat, (j <= m)%N -> 0 <= f j) -> p ^+ m * f m <= @binomial_mean R m p f'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'binomial_mean_trials_statement',
     "forall (R : numDomainType) (m m' : nat) (p : R) (f : nat -> R), 0 <= p <= 1 -> {homo f : i j / (i <= j)%N >-> i <= j} -> (m <= m')%N -> @binomial_mean R m p f <= @binomial_mean R m' p f"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'unif_mean_binomial_mean_statement',
     'forall (R : realFieldType) (T : finType) (m : nat) (p : R) (f : nat -> T -> R), @unif_mean R T (fun x : T => @binomial_mean R m p (f^~ x)) = @binomial_mean R m p (fun j : nat => @unif_mean R T (f j))'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'binomial_meanE_statement',
     'forall (R : realType) (m : nat) (p : R) (f : nat -> R), @binomial_mean R m p f = \\sum_(j < m.+1) @binomial_pmf R m p (nat_of_ord j) * f (nat_of_ord j)'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/binomial_mean.v',
     'integral_binomial_mean_statement',
     'forall (R : realType) (m : nat) (p : R) (f : nat -> R), 0 <= p <= 1 -> (\\int[@binomial_prob R m p]_j (f j)%:E)%E = (@binomial_mean R m p f)%:E'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/commuting_operators.v',
     'homo_iter_statement',
     'forall (disp : Order.disp_t) (T : preorderType disp) (A : T -> T) (m : nat), {homo A : x y / (x <= y)%O} -> {homo @iter T m A : x y / (x <= y)%O}'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/commuting_operators.v',
     'iter_le_subcomm_statement',
     'forall (disp : Order.disp_t) (T : preorderType disp) (A B : T -> T) (x : T), {homo A : y z / (y <= z)%O} -> {homo B : y z / (y <= z)%O} -> (forall y : T, (B (A y) <= A (B y))%O) -> (B x <= A x)%O -> forall m : nat, (@iter T m B x <= @iter T m A x)%O'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/commuting_operators.v',
     'monotone_iter_le_statement',
     'forall (R : numDomainType) (X : Type) (A B : (X -> R) -> X -> R) (f : X -> R), @monotone_op R X A -> @monotone_op R X B -> (forall (g : X -> R) (x : X), B (A g) x <= A (B g) x) -> (forall x : X, B f x <= A f x) -> forall (m : nat) (x : X), @iter (X -> R) m B f x <= @iter (X -> R) m A f x'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/commuting_operators.v',
     'iter_scale_statement',
     'forall (R : numDomainType) (X : Type) (A : (X -> R) -> X -> R) (c : R), @linear_op R X A -> forall (m : nat) (f : X -> R) (x : X), @iter (X -> R) m (fun (g : X -> R) (y : X) => c * A g y) f x = c ^+ m * @iter (X -> R) m A f x'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/commuting_operators.v',
     'iter_mix_binomial_statement',
     'forall (R : numDomainType) (X : Type) (A B : (X -> R) -> X -> R) (p : R), @linear_op R X A -> @linear_op R X B -> (forall f : X -> R, A (B f) = B (A f)) -> forall (m : nat) (f : X -> R) (x : X), @iter (X -> R) m (fun (g : X -> R) (y : X) => p * A g y + (1 - p) * B g y) f x = @binomial_mean R m p (fun j : nat => @iter (X -> R) j A (@iter (X -> R) (m - j) B f) x)'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/commuting_operators.v',
     'binomial_mix_le_iter_statement',
     'forall (R : numDomainType) (X : Type) (A B C : (X -> R) -> X -> R) (p : R) (f : X -> R), 0 <= p <= 1 -> @linear_op R X A -> @linear_op R X B -> @linear_op R X C -> @monotone_op R X A -> @monotone_op R X B -> @monotone_op R X C -> (forall g : X -> R, A (B g) = B (A g)) -> (forall (g : X -> R) (x : X), A (C g) x <= C (A g) x) -> (forall (g : X -> R) (x : X), B (C g) x <= C (B g) x) -> (forall x : X, p * A f x + (1 - p) * B f x <= C f x) -> forall (m : nat) (x : X), @binomial_mean R m p (fun j : nat => @iter (X -> R) j A (@iter (X -> R) (m - j) B f) x) <= @iter (X -> R) m C f x'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/commuting_operators.v',
     'meet_avg_linear_statement',
     'forall (R : realFieldType) (T C : finType) (E : C -> {set T}), @linear_op R {set T} (@meet_avg R T C E)'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/commuting_operators.v',
     'meet_avg_monotone_statement',
     'forall (R : realFieldType) (T C : finType) (E : C -> {set T}), @monotone_op R {set T} (@meet_avg R T C E)'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/commuting_operators.v',
     'meet_avg_cst_statement',
     'forall (R : realFieldType) (T C : finType) (E : C -> {set T}) (a : R) (S0 : {set T}), (0 < #|C|)%N -> @meet_avg R T C E (fun=> a) S0 = a'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/commuting_operators.v',
     'meet_avgC_statement',
     'forall (R : realFieldType) (T C D : finType) (E : C -> {set T}) (F : D -> {set T}) (f : {set T} -> R), @meet_avg R T C E (@meet_avg R T D F f) = @meet_avg R T D F (@meet_avg R T C E f)'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/probability/commuting_operators.v',
     'iter_meet_avg_statement',
     'forall (R : realFieldType) (T C : finType) (E : C -> {set T}) (m : nat) (f : {set T} -> R) (S : {set T}), @iter ({set T} -> R) m (@meet_avg R T C E) f S = @unif_mean R (tuple_tuple_of__canonical__fintype_Finite m C) (fun t : m.-tuple C => f (S :&: \\bigcap_(c <- t) E c))'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'bchar_algebra_statement',
     "fun (t a : nat) (R : pzRingType) => [/\\ forall y : matrix 'F_2 t a, @bchar t a R 0 y = 1, forall p q y : matrix 'F_2 t a, @bchar t a R (p + q) y = @bchar t a R p y * @bchar t a R q y, forall p y : matrix 'F_2 t a, @bchar t a R p y = @bchar t a R y p & forall p y : matrix 'F_2 t a, @bchar t a R p y = 1 \\/ @bchar t a R p y = -1]"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'bchar_orthogonal_statement',
     "fun (t a : nat) (R : pzRingType) => forall p q : matrix 'F_2 t a, \\sum_y @bchar t a R p y * @bchar t a R q y = (if p == q then #|{: matrix 'F_2 t a}|%:R else 0)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'bchar_delta_statement',
     "fun (t a : nat) (R : pzRingType) => forall (i : 'I_t) (j : 'I_a) (y : matrix 'F_2 t a), @bchar t a R (@delta_mx (fintype_ordinal__canonical__GRing_PzSemiRing (Zp_trunc (pdiv 2))) t a i j) y = (-1) ^+ nat_of_ord (y i j)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'blk_dist_metric_statement',
     "fun t a : nat => [/\\ forall p q : matrix 'F_2 t a, @blk_dist t a p q = @blk_deg t a (p + q), forall p q : matrix 'F_2 t a, @blk_dist t a p q = 0%N <-> p = q, forall p q : matrix 'F_2 t a, @blk_dist t a p q = @blk_dist t a q p, forall p q s : matrix 'F_2 t a, (@blk_dist t a p s <= @blk_dist t a p q + @blk_dist t a q s)%N & forall p q s : matrix 'F_2 t a, @blk_dist t a (p + s) (q + s) = @blk_dist t a p q]"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'fcoef_inversion_statement',
     "fun (t a : nat) (R : numFieldType) => forall (V : lmodType R) (f : matrix 'F_2 t a -> V) (y : matrix 'F_2 t a), f y = \\sum_p @bchar t a R p y *: @fcoef t a R V f p"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'fcoef_expansion_statement',
     "fun (t a : nat) (R : numFieldType) => forall (V : lmodType R) (c : matrix 'F_2 t a -> V) (q : matrix 'F_2 t a), @fcoef t a R V (fun y : matrix 'F_2 t a => \\sum_p @bchar t a R p y *: c p) q = c q"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'fcoef_plancherel_statement',
     "fun (t a : nat) (R : numFieldType) => forall (V W Z : lmodType R) (b : V -> W -> Z), (forall w : W, linear (b^~ w)) -> (forall v : V, linear (b v)) -> forall (f : matrix 'F_2 t a -> V) (g : matrix 'F_2 t a -> W), #|{: matrix 'F_2 t a}|%:R^-1 *: \\sum_y b (f y) (g y) = \\sum_p b (@fcoef t a R V f p) (@fcoef t a R W g p)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'fcoef_linear_statement',
     "fun (t a : nat) (R : numFieldType) => forall (V : lmodType R) (c : R) (f g : matrix 'F_2 t a -> V) (p : matrix 'F_2 t a), @fcoef t a R V (fun y : matrix 'F_2 t a => c *: f y + g y) p = c *: @fcoef t a R V f p + @fcoef t a R V g p"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'fcoef_comp_linear_statement',
     "fun (t a : nat) (R : numFieldType) => forall (V W : lmodType R) (h : V -> W), linear h -> forall (f : matrix 'F_2 t a -> V) (p : matrix 'F_2 t a), @fcoef t a R W (fun y : matrix 'F_2 t a => h (f y)) p = h (@fcoef t a R V f p)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'fcoef_mulmx_statement',
     "fun (t a : nat) (R : numFieldType) => forall (m n k l : nat) (A : matrix R m n) (f : matrix 'F_2 t a -> matrix R n k) (B : matrix R k l) (p : matrix 'F_2 t a), @fcoef t a R (matrix_matrix__canonical__GRing_Lmodule R m l) (fun y : matrix 'F_2 t a => A *m f y *m B) p = A *m @fcoef t a R (matrix_matrix__canonical__GRing_Lmodule R n k) f p *m B"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'fcoef_norm_le_statement',
     "fun (t a : nat) (R : numFieldType) => forall (f : matrix 'F_2 t a -> R^o) (c : R) (p : matrix 'F_2 t a), (forall y : matrix 'F_2 t a, `|f y : R| <= c) -> `|@fcoef t a R (GRing.GRing_regular__canonical__GRing_Lmodule R) f p : R| <= c"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'fcoef_translate_statement',
     "fun (t a : nat) (R : numFieldType) => forall (V : lmodType R) (f : matrix 'F_2 t a -> V) (p q : matrix 'F_2 t a), @fcoef t a R V (fun y : matrix 'F_2 t a => @bchar t a R q y *: f y) (p + q) = @fcoef t a R V f p"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'low_blk_deg_expansion_statement',
     "fun (t a : nat) (R : numFieldType) => forall (V : lmodType R) (D : nat) (f : matrix 'F_2 t a -> V), @low_blk_deg t a R V D f <-> (forall y : matrix 'F_2 t a, f y = \\sum_(p | (@blk_deg t a p <= D)%N) @bchar t a R p y *: @fcoef t a R V f p)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'low_blk_deg_translate_statement',
     "fun (t a : nat) (R : numFieldType) => forall (V : lmodType R) (D : nat) (f : matrix 'F_2 t a -> V) (q : matrix 'F_2 t a), (forall p : matrix 'F_2 t a, (D < @blk_dist t a p q)%N -> @fcoef t a R V f p = 0) -> @low_blk_deg t a R V D (fun y : matrix 'F_2 t a => @bchar t a R q y *: f y)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'blk_dist_row_statement',
     "forall (a : nat) (s z : matrix 'F_2 1 a), @blk_dist 1 a s z = (s != z)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'bchar_col_mx_statement',
     "fun t1 t2 a : nat => forall (R : pzRingType) (p1 y1 : matrix 'F_2 t1 a) (p2 y2 : matrix 'F_2 t2 a), @bchar (t1 + t2) a R (@col_mx 'F_2 t1 t2 a p1 p2) (@col_mx 'F_2 t1 t2 a y1 y2) = @bchar t1 a R p1 y1 * @bchar t2 a R p2 y2"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'blk_col_mx_statement',
     "fun t1 t2 a : nat => forall (p1 q1 : matrix 'F_2 t1 a) (p2 q2 : matrix 'F_2 t2 a), @blk_deg (t1 + t2) a (@col_mx 'F_2 t1 t2 a p1 p2) = (@blk_deg t1 a p1 + @blk_deg t2 a p2)%N /\\ @blk_dist (t1 + t2) a (@col_mx 'F_2 t1 t2 a p1 p2) (@col_mx 'F_2 t1 t2 a q1 q2) = (@blk_dist t1 a p1 q1 + @blk_dist t2 a p2 q2)%N"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/fourier/boolean_fourier.v',
     'fcoef_col_mx_statement',
     "fun t1 t2 a : nat => forall (R : numFieldType) (V : lmodType R) (f : matrix 'F_2 (t1 + t2) a -> V) (p1 : matrix 'F_2 t1 a) (p2 : matrix 'F_2 t2 a), @fcoef (t1 + t2) a R V f (@col_mx 'F_2 t1 t2 a p1 p2) = @fcoef t1 a R V (fun y1 : matrix 'F_2 t1 a => @fcoef t2 a R V (fun y2 : matrix 'F_2 t2 a => f (@col_mx 'F_2 t1 t2 a y1 y2)) p2) p1"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/matrix/psd_factorization.v',
     'psd_factorization_ge0_statement',
     'forall (R : realType) (I J : finType) (A : I -> J -> R) (r : nat), @psd_factorization R I J A r -> forall (i : I) (j : J), 0 <= A i j'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/matrix/psd_factorization.v',
     'psd_factorization_size_gt0_statement',
     'forall (R : realType) (I J : finType) (A : I -> J -> R) (r : nat), @psd_factorization R I J A r -> (exists (i : I) (j : J), A i j != 0) -> (0 < r)%N'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/matrix/psd_factorization.v',
     'psd_factorization_restrict_statement',
     "forall (R : realType) (I J I' J' : finType) (A : I -> J -> R) (r : nat) (f : I' -> I) (g : J' -> J), @psd_factorization R I J A r -> @psd_factorization R I' J' (fun (i : I') (j : J') => A (f i) (g j)) r"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/matrix/psd_factorization.v',
     'psd_factorization_widen_statement',
     'forall (R : realType) (I J : finType) (A : I -> J -> R) (r s : nat), (r <= s)%N -> @psd_factorization R I J A r -> @psd_factorization R I J A s'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/matrix/psd_factorization.v',
     'psd_factorization_shift_statement',
     'forall (R : realType) (I J : finType) (A : I -> J -> R) (r : nat) (rho : R), 0 <= rho -> @psd_factorization R I J A r -> @psd_factorization R I J (fun (i : I) (j : J) => A i j + rho) r.+1'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/matrix/psd_factorization.v',
     'psd_factorization_nonneg_statement',
     "forall (R : realType) (I J : finType) (r : nat) (a : I -> 'I_r -> R) (b : J -> 'I_r -> R), (forall (i : I) (k : 'I_r), 0 <= a i k) -> (forall (j : J) (k : 'I_r), 0 <= b j k) -> @psd_factorization R I J (fun (i : I) (j : J) => \\sum_(k < r) a i k * b j k) r"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/combinatorics/binomial_bounds.v',
     'central_bin_le_statement',
     "forall n : nat, (3 * n).+1 * 'C(2 * n, n) ^ 2 <= 16 ^ n"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/combinatorics/binomial_bounds.v',
     'central_bin_ge_statement',
     "forall n : nat, 0 < n -> 16 ^ n <= 4 * n * 'C(2 * n, n) ^ 2"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/combinatorics/binomial_bounds.v',
     'half_bin_ge_statement',
     "forall h : nat, 4 ^ h <= 2 * h.+1 * 'C(h, h./2) ^ 2"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/combinatorics/binomial_bounds.v',
     'leq_bin_half_statement',
     "forall n k : nat, 'C(n, k) <= 'C(n, n./2)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/combinatorics/binomial_bounds.v',
     'bin_near_half_statement',
     "forall h g T : nat, 6 * T <= h -> h <= 2 * (g + T) -> 2 * g <= h + 2 * T -> 'C(h, h./2) <= 2 ^ T.+1 * 'C(h, g)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/combinatorics/binomial_bounds.v',
     'bin_sqr_central_statement',
     "forall u j : nat, j <= u -> 'C(u, j) ^ 2 * 'C(2 * u, u) = 'C(2 * j, j) * 'C(2 * (u - j), u - j) * 'C(2 * u, 2 * j)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/combinatorics/binomial_bounds.v',
     'bin_sqr_ratio_statement',
     "forall u j : nat, j <= u -> 'C(u, j) ^ 4 * j.+1 * (u - j).+1 <= 4 * u.+1 * 'C(2 * u, 2 * j) ^ 2"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/combinatorics/binomial_bounds.v',
     'bin_partial_sum_statement',
     "forall (R : realType) (N M : nat), M <= N -> ((\\sum_(j < M.+1) 'C(N, nat_of_ord j)%:R : R) <= ((@expR R 1 * N%:R / M%:R) ^+ M : R))%R"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/matrix/psd_duality.v',
     'psd_eval_cone_closed_statement',
     "forall (R : realType) (n N : nat) (G : 'I_N -> matrix R n n), (forall j : 'I_N, @psdmx R n (G j)) -> @closed (matrix_matrix__canonical__topology_structure_Topological 1 N (numFieldTopology.Real_sort__canonical__topology_structure_Topological R)) (@psd_eval_cone R n N G)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/matrix/psd_duality.v',
     'psdmx_dual_statement',
     'forall (R : realType) (n : nat) (S : matrix R n n), S \\is symmetricmx -> @psdmx R n S <-> (forall F : matrix R n n, @psdmx R n F -> 0 <= \\tr (F *m S))'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/matrix/psd_duality.v',
     'psd_farkas_statement',
     "forall (R : realType) (n N : nat) (G : 'I_N -> matrix R n n) (y : matrix R 1 N), (forall j : 'I_N, @psdmx R n (G j)) -> @psd_eval_cone R n N G y <-> (forall c : matrix R 1 N, @psdmx R n (\\sum_j c 0 j *: G j) -> 0 <= @mxdot R 1 N c y)"),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/matrix/psd_duality.v',
     'psd_slack_certificate_statement',
     'forall (R : realType) (n : nat) (I : finType) (B : I -> matrix R n n) (s : I -> R) (i0 : I), (forall i : I, @psdmx R n (B i)) -> s i0 = 0 -> (exists2 A : matrix R n n, @psdmx R n A & forall i : I, \\tr (A *m B i) = s i) <-> (forall w : I -> R, \\sum_i w i = 1 -> @psdmx R n (\\sum_i w i *: B i) -> 0 <= \\sum_i w i * s i)'),
    ('46e45c84b99a50663205933ae501da029dd66098',
     'library/matrix/psd_duality.v',
     'psd_slack_certificate_affine_statement',
     "forall (R : realType) (n m : nat) (I : finType) (C : 'I_m -> matrix R n n) (c : 'I_m -> R) (D : matrix R n n) (d : R) (B : I -> matrix R n n) (i0 : I), (forall i : I, @psdmx R n (B i)) -> (forall (i : I) (l : 'I_m), \\tr (C l *m B i) = c l) -> (forall X : matrix R n n, @psdmx R n X -> (forall l : 'I_m, \\tr (C l *m X) = c l) -> 0 <= \\tr (D *m X) + d) -> \\tr (D *m B i0) + d = 0 -> exists2 A : matrix R n n, @psdmx R n A & forall i : I, \\tr (A *m B i) = \\tr (D *m B i) + d"),
]
# Rule 32: the general statements of batch 1 of phase 14 that the user
# accepted at 39f58468 (DECISIONS.md, 22 October 2026, 14:29): the acceptance
# commit, the path, the name of the Prop definition and the proposition as
# Print shows it at that commit under Set Printing Implicit, in the context of
# the Require, Import and Open Scope commands of its file; a leading fun of
# section parameters is read as forall. Separate from INVENTORY, whose lines
# E12 patches.
INVENTORY_P14 = [
    ('39f58468aeaa024a54509c1b684c3a40e208e5d8',
     'library/matrix/multiplicity.v',
     'trace_multiplicity_statement',
     "fun R : realType => forall (N m : nat) (K : 'M_N) (S0 : seq {perm 'I_N}), @psdmx R N K -> K *m (@const_mx R N 1 1 : 'cV_N) = @const_mx R N 1 1 -> (0 < m)%N -> (forall s : perm_perm_type__canonical__eqtype_Equality 'I_N, s \\in S0 -> @perm_mx R N s *m K = K *m @perm_mx R N s) -> (forall Q : 'M_N, Q \\is symmetricmx -> Q *m Q = Q -> Q != 0 -> Q *m (@const_mx R N 1 1 : 'cV_N) = 0 -> (forall s : perm_perm_type__canonical__eqtype_Equality 'I_N, s \\in S0 -> @perm_mx R N s *m Q = Q *m @perm_mx R N s) -> m%:R <= \\tr Q) -> forall x : 'cV_N, @mxdot R N 1 x (@const_mx R N 1 1) = 0 -> @mxdot R N 1 x (K *m x) ^+ 2 <= (\\tr (K *m K) - 1) / m%:R * @mxdot R N 1 x x ^+ 2"),
    ('39f58468aeaa024a54509c1b684c3a40e208e5d8',
     'library/matrix/multiplicity.v',
     'ksubset_multiplicity_statement',
     "fun R : realType => forall (k w : nat) (Q : 'M_#|{: ksubset k w}|), ~~ odd k -> (5 < k)%N -> Q \\is symmetricmx -> Q *m Q = Q -> Q != 0 -> Q *m (@const_mx R #|{: ksubset k w}| 1 1 : 'cV_#|{: ksubset k w}|) = 0 -> (forall s : {perm 'I_k}, @ksubset_mx R k w s *m Q = Q *m @ksubset_mx R k w s) -> (k %/ 2)%:R <= \\tr Q"),
    ('39f58468aeaa024a54509c1b684c3a40e208e5d8',
     'library/combinatorics/harmonic.v',
     'harmonic_ln_statement',
     'fun R : realType => forall n : nat, (0 < n)%N -> \\sum_(i < n) i.+1%:R^-1 <= 1 + @ln R (n%:R : R)'),
    ('39f58468aeaa024a54509c1b684c3a40e208e5d8',
     'library/combinatorics/binomial_bounds.v',
     'bin_mul_pow_statement',
     "forall b l s : nat, (b <= l)%N -> ('C(b, s) * l ^ s <= 'C(l, s) * b ^ s)%N"),
    ('39f58468aeaa024a54509c1b684c3a40e208e5d8',
     'library/combinatorics/expander.v',
     'expander_statement',
     "forall l : nat, 0 < l -> exists s : 'I_100 -> {perm 'I_l}, forall W : {set 'I_(l + l)}, minn #|W| (l + l - #|W|) <= #|@perm_cut 100 l s W|"),
]
UNIVERSALITY_CHECK = (
    "From EllipsoidUniversality Require Import UniversalityStatement "
    "UniversalityTheorem. Definition universality_theorem_checked : "
    "universality_statement := universality_theorem. "
    "Print Assumptions universality_theorem.")
MIXTURE_CHECK = (
    "From EllipsoidUniversality Require Import MixtureStatement "
    "MixtureTheorem. Definition mixture_theorem_checked : "
    "mixture_theorem_statement := mixture_theorem. "
    "Print Assumptions mixture_theorem.")
PAIRED_CHECK = (
    "From EllipsoidUniversality Require Import PairedStatement "
    "PairedTheorem. Definition paired_theorem_checked : "
    "paired_statement := paired_theorem. "
    "Print Assumptions paired_theorem.")
LATENT_CHECK = (
    "From EllipsoidUniversality Require Import LatentSignStatement "
    "LatentSignTheorem. Definition latent_sign_theorem_checked : "
    "latent_sign_statement := latent_sign_theorem. "
    "Print Assumptions latent_sign_theorem.")
COUNTABLE_CHECK = (
    "From EllipsoidUniversality Require Import CountableMixtureStatement "
    "CountableTheorem. Definition countable_theorem_checked : "
    "countable_theorem_statement := countable_theorem. "
    "Print Assumptions countable_theorem.")
CONDITION_CHECK = (
    "From EllipsoidUniversality Require Import ConditionStatement "
    "ConditionTheorem. Definition condition_theorem_checked : "
    "condition_theorem_statement := condition_theorem. "
    "Print Assumptions condition_theorem.")
LATENT_SCOPE_CHECK = (
    "From EllipsoidUniversality Require Import LatentSignScope "
    "LatentScopeTheorem. Definition latent_scope_theorem_checked : "
    "latent_scope_statement := latent_scope_theorem. "
    "Print Assumptions latent_scope_theorem.")
ROBUST_CHECK = (
    "From EllipsoidUniversality Require Import RobustStatement "
    "RobustTheorem. Definition robust_theorem_checked : "
    "robust_theorem_statement := robust_theorem. "
    "Print Assumptions robust_theorem.")
LATENT_TENSOR_CHECK = (
    "From EllipsoidUniversality Require Import LatentTensorization "
    "LatentTensorTheorem. Definition latent_tensor_theorem_checked : "
    "latent_tensorization_statement := latent_tensor_theorem. "
    "Print Assumptions latent_tensor_theorem.")
CONTINUOUS_LATENT_CHECK = (
    "From EllipsoidUniversality Require Import ContinuousLatent "
    "ContinuousLatentTheorem. Definition continuous_latent_theorem_checked : "
    "continuous_latent_statement := continuous_latent_theorem. "
    "Print Assumptions continuous_latent_theorem.")
CONDITION_ENDPOINTS_CHECK = (
    "From EllipsoidUniversality Require Import ConditionEndpoints "
    "ConditionEndpointsTheorem. Definition condition_endpoints_theorem_checked "
    ": condition_endpoints_statement := condition_endpoints_theorem. "
    "Print Assumptions condition_endpoints_theorem.")
CONDITION_ROBUST_CHECK = (
    "From EllipsoidUniversality Require Import ConditionRobustStatement "
    "ConditionRobustTheorem. Definition robust_condition_theorem_checked "
    ": robust_condition_theorem_statement := robust_condition_theorem. "
    "Print Assumptions robust_condition_theorem.")
LATENT_TENSOR_UPPER_CHECK = (
    "From EllipsoidUniversality Require Import LatentTensorUpper "
    "LatentTensorUpperTheorem. Definition latent_tensor_upper_theorem_checked "
    ": latent_tensor_upper_statement := latent_tensor_upper_theorem. "
    "Print Assumptions latent_tensor_upper_theorem.")
CONDITION_KAPPA_CURVE_CHECK = (
    "From EllipsoidUniversality Require Import ConditionKappaCurveStatement "
    "ConditionKappaCurveTheorem. Definition condition_kappa_curve_theorem_checked "
    ": condition_kappa_curve_statement := condition_kappa_curve_theorem. "
    "Print Assumptions condition_kappa_curve_theorem.")
CONDITION_KAPPA_CHECK = (
    "From EllipsoidUniversality Require Import ConditionKappaStatement "
    "ConditionKappaTheorem. Definition condition_kappa_theorem_checked "
    ": condition_kappa_theorem_statement := condition_kappa_theorem. "
    "Print Assumptions condition_kappa_theorem.")
CONDITION_KAPPA_ROBUST_CHECK = (
    "From EllipsoidUniversality Require Import ConditionKappaRobustStatement "
    "ConditionKappaRobustTheorem. Definition condition_kappa_robust_theorem_checked "
    ": condition_kappa_robust_theorem_statement := condition_kappa_robust_theorem. "
    "Print Assumptions condition_kappa_robust_theorem.")
# The theorems of phases 6 and 7: name, check file, its code, expected
# axioms; their reports are the third, fourth and fifth arguments.
PHASE6_THEOREMS = [
    ("mixture theorem", "check/MixtureAssumptions.v", MIXTURE_CHECK,
     "check/mixture_assumptions.expected"),
    ("paired theorem", "check/PairedAssumptions.v", PAIRED_CHECK,
     "check/paired_assumptions.expected"),
    ("latent-sign theorem", "check/LatentSignAssumptions.v", LATENT_CHECK,
     "check/latent_sign_assumptions.expected"),
]
# The theorems of phase 8; their reports are the sixth, seventh and eighth
# arguments.
PHASE8_THEOREMS = [
    ("countable-mixture theorem", "check/CountableAssumptions.v",
     COUNTABLE_CHECK, "check/countable_assumptions.expected"),
    ("condition-number theorem", "check/ConditionAssumptions.v",
     CONDITION_CHECK, "check/condition_assumptions.expected"),
    ("latent-sign scope theorem", "check/LatentScopeAssumptions.v",
     LATENT_SCOPE_CHECK, "check/latent_scope_assumptions.expected"),
]
# The theorems of phase 9; their reports are the ninth to twelfth
# arguments.
PHASE9_THEOREMS = [
    ("robustness theorem", "check/RobustAssumptions.v", ROBUST_CHECK,
     "check/robust_assumptions.expected"),
    ("tensorization theorem", "check/LatentTensorAssumptions.v",
     LATENT_TENSOR_CHECK, "check/latent_tensor_assumptions.expected"),
    ("continuous-latent theorem", "check/ContinuousLatentAssumptions.v",
     CONTINUOUS_LATENT_CHECK, "check/continuous_latent_assumptions.expected"),
    ("condition-endpoints theorem", "check/ConditionEndpointsAssumptions.v",
     CONDITION_ENDPOINTS_CHECK,
     "check/condition_endpoints_assumptions.expected"),
]
# The theorems of phase 10; their reports are the thirteenth and
# fourteenth arguments.
PHASE10_THEOREMS = [
    ("robust condition-number theorem", "check/ConditionRobustAssumptions.v",
     CONDITION_ROBUST_CHECK, "check/condition_robust_assumptions.expected"),
    ("tensorization upper bound", "check/LatentTensorUpperAssumptions.v",
     LATENT_TENSOR_UPPER_CHECK,
     "check/latent_tensor_upper_assumptions.expected"),
]
# The theorems of phase 11; their reports are the fifteenth to seventeenth
# arguments.
PHASE11_THEOREMS = [
    ("condition-number curve at kappa",
     "check/ConditionKappaCurveAssumptions.v", CONDITION_KAPPA_CURVE_CHECK,
     "check/condition_kappa_curve_assumptions.expected"),
    ("condition-number theorem at kappa", "check/ConditionKappaAssumptions.v",
     CONDITION_KAPPA_CHECK, "check/condition_kappa_assumptions.expected"),
    ("robust condition-number theorem at kappa",
     "check/ConditionKappaRobustAssumptions.v", CONDITION_KAPPA_ROBUST_CHECK,
     "check/condition_kappa_robust_assumptions.expected"),
]
# The axiom checks of phase 12: the code of each check file.
PHASE12_CHECKS = {
    "MatrixSeries": ("From GaussianApplications Require Import MatrixSeriesStatement "
        "MatrixSeriesTheorem. Definition matrix_series_theorem_checked "
        ": matrix_series_statement := matrix_series_theorem. "
        "Print Assumptions matrix_series_theorem."),
    "TensorPacking": ("From GaussianApplications Require Import TensorPackingStatement "
        "TensorPackingTheorem. Definition tensor_packing_theorem_checked "
        ": tensor_packing_statement := tensor_packing_theorem. "
        "Print Assumptions tensor_packing_theorem."),
    "GoeEdge": ("From GaussianApplications Require Import GoeEdgeStatement "
        "GoeEdgeTheorem. Definition goe_edge_theorem_checked "
        ": goe_edge_statement := goe_edge_theorem. "
        "Print Assumptions goe_edge_theorem."),
    "SKGap": ("From GaussianApplications Require Import SKGapStatement "
        "SKGapTheorem. Definition sk_gap_theorem_checked "
        ": sk_gap_statement := sk_gap_theorem. "
        "Print Assumptions sk_gap_theorem."),
    "PsdSplitting": ("From GaussianApplications Require Import PsdSplittingStatement "
        "PsdSplittingTheorem. Definition psd_splitting_theorem_checked "
        ": psd_splitting_statement := psd_splitting_theorem. "
        "Print Assumptions psd_splitting_theorem."),
    "PerceptronSign": ("From GaussianApplications Require Import PerceptronSignStatement "
        "PerceptronSignTheorem. Definition perceptron_sign_theorem_checked "
        ": perceptron_sign_statement := perceptron_sign_theorem. "
        "Print Assumptions perceptron_sign_theorem."),
    "SatVariance": ("From GaussianApplications Require Import SatVarianceStatement "
        "SatVarianceTheorem. Definition sat_variance_theorem_checked "
        ": sat_variance_statement := sat_variance_theorem. "
        "Print Assumptions sat_variance_theorem."),
}
PHASE12_THEOREMS = [
    ("Gaussian matrix series theorem", "check/MatrixSeriesAssumptions.v", PHASE12_CHECKS["MatrixSeries"],
     "check/matrix_series_assumptions.expected"),
    ("tensor packing theorem", "check/TensorPackingAssumptions.v", PHASE12_CHECKS["TensorPacking"],
     "check/tensor_packing_assumptions.expected"),
    ("GOE edge theorem", "check/GoeEdgeAssumptions.v", PHASE12_CHECKS["GoeEdge"],
     "check/goe_edge_assumptions.expected"),
    ("SK spectral gap theorem", "check/SKGapAssumptions.v", PHASE12_CHECKS["SKGap"],
     "check/sk_gap_assumptions.expected"),
    ("orthogonal splitting theorem", "check/PsdSplittingAssumptions.v", PHASE12_CHECKS["PsdSplitting"],
     "check/psd_splitting_assumptions.expected"),
    ("perceptron comparison theorem", "check/PerceptronSignAssumptions.v", PHASE12_CHECKS["PerceptronSign"],
     "check/perceptron_sign_assumptions.expected"),
    ("k-SAT variance theorem", "check/SatVarianceAssumptions.v", PHASE12_CHECKS["SatVariance"],
     "check/sat_variance_assumptions.expected"),
]
PHASE13_CHECKS = {
    "SatThreshold": ('Require GaussianApplications.SatThresholdStatement. Require Gaussian'
        'Applications.SatThresholdTheorem. Definition sat_threshold_identity '
        ': GaussianApplications.SatThresholdStatement.sat_threshold_statement'
        ' := GaussianApplications.SatThresholdTheorem.sat_threshold_theorem. '
        'Locate sat_threshold_identity. Print Assumptions sat_threshold_ident'
        'ity.'),
    "PsdNormalization": ('Require GaussianApplications.PsdNormalizationStatement. Require Gaus'
        'sianApplications.PsdNormalizationTheorem. Definition psd_normalizati'
        'on_identity : GaussianApplications.PsdNormalizationStatement.psd_nor'
        'malization_statement := GaussianApplications.PsdNormalizationTheorem'
        '.psd_normalization_theorem. Locate psd_normalization_identity. Print'
        ' Assumptions psd_normalization_identity.'),
    "ProductSmoothing": ('Require GaussianApplications.ProductSmoothingStatement. Require Gaus'
        'sianApplications.ProductSmoothingTheorem. Definition product_smoothi'
        'ng_identity : GaussianApplications.ProductSmoothingStatement.product'
        '_smoothing_statement := GaussianApplications.ProductSmoothingTheorem'
        '.product_smoothing_theorem. Locate product_smoothing_identity. Print'
        ' Assumptions product_smoothing_identity.'),
    "MinSuperadditive": ('Require GaussianApplications.MinSuperadditiveStatement. Require Gaus'
        'sianApplications.MinSuperadditiveTheorem. Definition min_superadditi'
        've_identity : GaussianApplications.MinSuperadditiveStatement.min_sup'
        'eradditive_statement := GaussianApplications.MinSuperadditiveTheorem'
        '.min_superadditive_theorem. Locate min_superadditive_identity. Print'
        ' Assumptions min_superadditive_identity.'),
}
PHASE13_THEOREMS = [
    ("satisfiability threshold theorem", "check/SatThresholdAssumptions.v", PHASE13_CHECKS["SatThreshold"],
     "check/sat_threshold_assumptions.expected"),
    ("PSD normalization theorem", "check/PsdNormalizationAssumptions.v", PHASE13_CHECKS["PsdNormalization"],
     "check/psd_normalization_assumptions.expected"),
    ("product smoothing theorem", "check/ProductSmoothingAssumptions.v", PHASE13_CHECKS["ProductSmoothing"],
     "check/product_smoothing_assumptions.expected"),
    ("min-superadditive convergence theorem", "check/MinSuperadditiveAssumptions.v", PHASE13_CHECKS["MinSuperadditive"],
     "check/min_superadditive_assumptions.expected"),
]
PHASE14_CHECKS = {
    "PsdRank": ('Require GaussianApplications.PsdRankStatement. Require GaussianAppli'
        'cations.PsdRankTheorem. Definition psd_rank_identity : GaussianAppli'
        'cations.PsdRankStatement.psd_rank_statement := GaussianApplications.'
        'PsdRankTheorem.psd_rank_theorem. Locate psd_rank_identity. Print Ass'
        'umptions psd_rank_identity.'),
    "PsdLift": ('Require GaussianApplications.PsdLiftStatement. Require GaussianAppli'
        'cations.PsdLiftTheorem. Definition psd_lift_identity : GaussianAppli'
        'cations.PsdLiftStatement.psd_lift_statement := GaussianApplications.'
        'PsdLiftTheorem.psd_lift_theorem. Locate psd_lift_identity. Print Ass'
        'umptions psd_lift_identity.'),
}
PHASE14_THEOREMS = [
    ("PSD rank theorem", "check/PsdRankAssumptions.v", PHASE14_CHECKS["PsdRank"],
     "check/psd_rank_assumptions.expected"),
    ("PSD lift corollary", "check/PsdLiftAssumptions.v", PHASE14_CHECKS["PsdLift"],
     "check/psd_lift_assumptions.expected"),
]
PHASE14_STATEMENTS = "check/Phase14Statements.v"
PHASE14_STATEMENTS_CHECK = ('Module accepted_multiplicity. From HB Require Import structures. Fro'
    'm mathcomp Require Import all_ssreflect_compat fingroup perm ssralg '
    'ssrnum. From mathcomp Require Import matrix sesquilinear reals. From'
    ' GaussianAnalysis.matrix Require Import euclidean psd_part psd_split'
    'ting. Import GRing.Theory Num.Theory. Local Open Scope ring_scope. R'
    'equire Import GaussianAnalysis.matrix.multiplicity. Lemma trace_mult'
    "iplicity_accepted : forall R : realType, forall (N m : nat) (K : 'M_"
    "N) (S0 : seq {perm 'I_N}), @psdmx R N K -> K *m (@const_mx R N 1 1 :"
    " 'cV_N) = @const_mx R N 1 1 -> (0 < m)%N -> (forall s : perm_perm_ty"
    "pe__canonical__eqtype_Equality 'I_N, s \\in S0 -> @perm_mx R N s *m K"
    " = K *m @perm_mx R N s) -> (forall Q : 'M_N, Q \\is symmetricmx -> Q "
    "*m Q = Q -> Q != 0 -> Q *m (@const_mx R N 1 1 : 'cV_N) = 0 -> (foral"
    "l s : perm_perm_type__canonical__eqtype_Equality 'I_N, s \\in S0 -> @"
    'perm_mx R N s *m Q = Q *m @perm_mx R N s) -> m%:R <= \\tr Q) -> foral'
    "l x : 'cV_N, @mxdot R N 1 x (@const_mx R N 1 1) = 0 -> @mxdot R N 1 "
    'x (K *m x) ^+ 2 <= (\\tr (K *m K) - 1) / m%:R * @mxdot R N 1 x x ^+ 2'
    '. Proof. exact: @trace_multiplicity. Qed. Lemma ksubset_multiplicity'
    "_accepted : forall R : realType, forall (k w : nat) (Q : 'M_#|{: ksu"
    'bset k w}|), ~~ odd k -> (5 < k)%N -> Q \\is symmetricmx -> Q *m Q = '
    "Q -> Q != 0 -> Q *m (@const_mx R #|{: ksubset k w}| 1 1 : 'cV_#|{: k"
    "subset k w}|) = 0 -> (forall s : {perm 'I_k}, @ksubset_mx R k w s *m"
    ' Q = Q *m @ksubset_mx R k w s) -> (k %/ 2)%:R <= \\tr Q. Proof. exact'
    ': @ksubset_multiplicity. Qed. End accepted_multiplicity. Module acce'
    'pted_harmonic. From mathcomp Require Import all_ssreflect_compat ssr'
    'alg ssrnum reals exp. Import GRing.Theory Num.Theory. Local Open Sco'
    'pe ring_scope. Require Import GaussianAnalysis.combinatorics.harmoni'
    'c. Lemma harmonic_ln_accepted : forall R : realType, forall n : nat,'
    ' (0 < n)%N -> \\sum_(i < n) i.+1%:R^-1 <= 1 + @ln R (n%:R : R). Proof'
    '. exact: @harmonic_ln. Qed. End accepted_harmonic. Module accepted_b'
    'inomial_bounds. From HB Require Import structures. From mathcomp Req'
    'uire Import all_ssreflect_compat ssralg ssrnum rat reals. From mathc'
    'omp Require Import sequences exp. From mathcomp Require Import arith'
    'metic_tactic ring_tactic. Import Order.TTheory GRing.Theory Num.Theo'
    'ry. Local Open Scope ring_scope. Require Import GaussianAnalysis.com'
    'binatorics.binomial_bounds. Lemma bin_mul_pow_accepted : forall b l '
    "s : nat, (b <= l)%N -> ('C(b, s) * l ^ s <= 'C(l, s) * b ^ s)%N. Pro"
    'of. exact: @bin_mul_pow. Qed. End accepted_binomial_bounds. Module a'
    'ccepted_expander. From mathcomp Require Import all_ssreflect_compat '
    'fingroup perm. Require Import GaussianAnalysis.combinatorics.expande'
    "r. Lemma expander_accepted : forall l : nat, 0 < l -> exists s : 'I_"
    "100 -> {perm 'I_l}, forall W : {set 'I_(l + l)}, minn #|W| (l + l - "
    '#|W|) <= #|@perm_cut 100 l s W|. Proof. exact: @expander. Qed. End a'
    'ccepted_expander. Definition phase14_statements_accepted := (accepte'
    'd_multiplicity.trace_multiplicity_accepted, accepted_multiplicity.ks'
    'ubset_multiplicity_accepted, accepted_harmonic.harmonic_ln_accepted,'
    ' accepted_binomial_bounds.bin_mul_pow_accepted, accepted_expander.ex'
    'pander_accepted). Print Assumptions phase14_statements_accepted.')
LIBRARY_STATEMENTS = "check/LibraryStatements.v"
LIBRARY_STATEMENTS_OUTPUT = "build/library_statements.txt"
LIBRARY_STATEMENTS_CHECK = ('Module accepted_finite_mean. From HB Require Import structures. From'
    ' mathcomp Require Import all_ssreflect_compat ssralg ssrnum. From ma'
    'thcomp Require Import arithmetic_tactic ring_tactic. Import Order.TT'
    'heory GRing.Theory Num.Theory. Local Open Scope ring_scope. Require '
    'Import GaussianAnalysis.probability.finite_mean. Lemma unif_mean_uni'
    'on_accepted : forall (R : realFieldType) (T I : finType) (P : I -> p'
    'red T), @unif_mean R T (fun x : T => [exists i, P i x]%:R : R) <= \\s'
    'um_i @unif_mean R T (fun x : T => (P i x)%:R : R). Proof. exact: @un'
    'if_mean_union. Qed. Lemma unif_mean_indicatorN_accepted : forall (R '
    ': realFieldType) (T : finType) (P : pred T), (0 < #|T|)%N -> @unif_m'
    'ean R T (fun x : T => (~~ P x)%:R : R) = 1 - @unif_mean R T (fun x :'
    ' T => (P x)%:R : R). Proof. exact: @unif_mean_indicatorN. Qed. Lemma'
    ' unif_mean_markov_accepted : forall (R : realFieldType) (T : finType'
    ') (f : T -> R) (t : R), (forall x : T, 0 <= f x) -> t * @unif_mean R'
    ' T (fun x : T => (t <= f x)%R%:R : R) <= @unif_mean R T f. Proof. ex'
    'act: @unif_mean_markov. Qed. Lemma unif_mean_cutoff_accepted : foral'
    'l (R : realFieldType) (T : finType) (f : T -> R) (M t : R), 0 <= t -'
    '> (forall x : T, f x <= M) -> @unif_mean R T f <= t + M * @unif_mean'
    ' R T (fun x : T => (t <= f x)%R%:R : R). Proof. exact: @unif_mean_cu'
    'toff. Qed. Lemma unif_chebyshev_accepted : forall (R : realFieldType'
    ') (T : finType) (f : T -> R) (t : R), 0 < t -> @unif_mean R T (fun x'
    ' : T => (t <= `|f x - @unif_mean R T f|)%R%:R : R) <= @unif_var R T '
    'f / t ^+ 2. Proof. exact: @unif_chebyshev. Qed. Lemma unif_mean_tupl'
    'e_prod_ord_accepted : forall (R : realFieldType) (T : finType) (m : '
    "nat) (g : 'I_m -> T -> R), @unif_mean R (tuple_tuple_of__canonical__"
    'fintype_Finite m T) (fun t : m.-tuple T => \\prod_(i < m) g i (@tnth '
    'm T t i)) = \\prod_(i < m) @unif_mean R T (g i). Proof. exact: @unif_'
    'mean_tuple_prod_ord. Qed. Lemma unif_mean_tuple_prod_set_accepted : '
    "forall (R : realFieldType) (T : finType) (m : nat) (J : {set 'I_m}) "
    '(g : T -> R), (0 < #|T|)%N -> @unif_mean R (tuple_tuple_of__canonica'
    'l__fintype_Finite m T) (fun t : m.-tuple T => \\prod_(i in J) g (@tnt'
    'h m T t i)) = @unif_mean R T g ^+ #|J|. Proof. exact: @unif_mean_tup'
    'le_prod_set. Qed. End accepted_finite_mean. Module accepted_binomial'
    '_mean. From HB Require Import structures. From mathcomp Require Impo'
    'rt all_ssreflect_compat ssralg ssrnum. From mathcomp Require Import '
    'boolp classical_sets reals ereal measure numfun. From mathcomp Requi'
    're Import lebesgue_integral binomial_distribution. From mathcomp Req'
    'uire Import ring_tactic. From GaussianAnalysis.probability Require I'
    'mport finite_mean. Import Order.TTheory GRing.Theory Num.Theory. Loc'
    'al Open Scope ring_scope. Require Import GaussianAnalysis.probabilit'
    'y.binomial_mean. Lemma binomial_mean0_accepted : forall (R : numDoma'
    'inType) (p : R) (f : nat -> R), @binomial_mean R 0 p f = f 0%N. Proo'
    'f. exact: @binomial_mean0. Qed. Lemma binomial_meanS_accepted : fora'
    'll (R : numDomainType) (m : nat) (p : R) (f : nat -> R), @binomial_m'
    'ean R m.+1 p f = (1 - p) * @binomial_mean R m p f + p * @binomial_me'
    'an R m p (fun j : nat => f j.+1). Proof. exact: @binomial_meanS. Qed'
    '. Lemma eq_binomial_mean_accepted : forall (R : numDomainType) (m : '
    'nat) (p : R) (f g : nat -> R), (forall j : nat, (j <= m)%N -> f j = '
    'g j) -> @binomial_mean R m p f = @binomial_mean R m p g. Proof. exac'
    't: @eq_binomial_mean. Qed. Lemma binomial_mean_cst_accepted : forall'
    ' (R : numDomainType) (m : nat) (p c : R), @binomial_mean R m p (fun='
    '> c) = c. Proof. exact: @binomial_mean_cst. Qed. Lemma binomial_mean'
    'D_accepted : forall (R : numDomainType) (m : nat) (p : R) (f g : nat'
    ' -> R), @binomial_mean R m p (fun j : nat => f j + g j) = @binomial_'
    'mean R m p f + @binomial_mean R m p g. Proof. exact: @binomial_meanD'
    '. Qed. Lemma binomial_meanZ_accepted : forall (R : numDomainType) (m'
    ' : nat) (p c : R) (f : nat -> R), @binomial_mean R m p (fun j : nat '
    '=> c * f j) = c * @binomial_mean R m p f. Proof. exact: @binomial_me'
    'anZ. Qed. Lemma ler_binomial_mean_accepted : forall (R : numDomainTy'
    'pe) (m : nat) (p : R) (f g : nat -> R), 0 <= p <= 1 -> (forall j : n'
    'at, (j <= m)%N -> f j <= g j) -> @binomial_mean R m p f <= @binomial'
    '_mean R m p g. Proof. exact: @ler_binomial_mean. Qed. Lemma binomial'
    '_mean_id_accepted : forall (R : numDomainType) (m : nat) (p : R), @b'
    'inomial_mean R m p [eta @Algebra.natmul R 1] = m%:R * p. Proof. exac'
    't: @binomial_mean_id. Qed. Lemma binomial_mean_sqr_dev_accepted : fo'
    'rall (R : numDomainType) (m : nat) (p : R), @binomial_mean R m p (fu'
    'n j : nat => (j%:R - m%:R * p) ^+ 2) = m%:R * p * (1 - p). Proof. ex'
    'act: @binomial_mean_sqr_dev. Qed. Lemma binomial_chebyshev_accepted '
    ': forall (R : realFieldType) (m : nat) (p t : R), 0 <= p <= 1 -> 0 <'
    ' t -> @binomial_mean R m p (fun j : nat => (t <= `|j%:R - m%:R * p|)'
    '%R%:R) <= m%:R * p * (1 - p) / t ^+ 2. Proof. exact: @binomial_cheby'
    'shev. Qed. Lemma binomial_mean_last_accepted : forall (R : numDomain'
    'Type) (m : nat) (p : R) (f : nat -> R), 0 <= p <= 1 -> (forall j : n'
    'at, (j <= m)%N -> 0 <= f j) -> p ^+ m * f m <= @binomial_mean R m p '
    'f. Proof. exact: @binomial_mean_last. Qed. Lemma binomial_mean_trial'
    "s_accepted : forall (R : numDomainType) (m m' : nat) (p : R) (f : na"
    't -> R), 0 <= p <= 1 -> {homo f : i j / (i <= j)%N >-> i <= j} -> (m'
    " <= m')%N -> @binomial_mean R m p f <= @binomial_mean R m' p f. Proo"
    'f. exact: @binomial_mean_trials. Qed. Lemma unif_mean_binomial_mean_'
    'accepted : forall (R : realFieldType) (T : finType) (m : nat) (p : R'
    ') (f : nat -> T -> R), @unif_mean R T (fun x : T => @binomial_mean R'
    ' m p (f^~ x)) = @binomial_mean R m p (fun j : nat => @unif_mean R T '
    '(f j)). Proof. exact: @unif_mean_binomial_mean. Qed. Lemma binomial_'
    'meanE_accepted : forall (R : realType) (m : nat) (p : R) (f : nat ->'
    ' R), @binomial_mean R m p f = \\sum_(j < m.+1) @binomial_pmf R m p (n'
    'at_of_ord j) * f (nat_of_ord j). Proof. exact: @binomial_meanE. Qed.'
    ' Lemma integral_binomial_mean_accepted : forall (R : realType) (m : '
    'nat) (p : R) (f : nat -> R), 0 <= p <= 1 -> (\\int[@binomial_prob R m'
    ' p]_j (f j)%:E)%E = (@binomial_mean R m p f)%:E. Proof. exact: @inte'
    'gral_binomial_mean. Qed. End accepted_binomial_mean. Module accepted'
    '_commuting_operators. From HB Require Import structures. From mathco'
    'mp Require Import all_ssreflect_compat ssralg ssrnum boolp. From Gau'
    'ssianAnalysis.probability Require Import finite_mean binomial_mean. '
    'Import Order.TTheory GRing.Theory Num.Theory. Local Open Scope ring_'
    'scope. Require Import GaussianAnalysis.probability.commuting_operato'
    'rs. Lemma homo_iter_accepted : forall (disp : Order.disp_t) (T : pre'
    'orderType disp) (A : T -> T) (m : nat), {homo A : x y / (x <= y)%O} '
    '-> {homo @iter T m A : x y / (x <= y)%O}. Proof. exact: @homo_iter. '
    'Qed. Lemma iter_le_subcomm_accepted : forall (disp : Order.disp_t) ('
    'T : preorderType disp) (A B : T -> T) (x : T), {homo A : y z / (y <='
    ' z)%O} -> {homo B : y z / (y <= z)%O} -> (forall y : T, (B (A y) <= '
    'A (B y))%O) -> (B x <= A x)%O -> forall m : nat, (@iter T m B x <= @'
    'iter T m A x)%O. Proof. exact: @iter_le_subcomm. Qed. Lemma monotone'
    '_iter_le_accepted : forall (R : numDomainType) (X : Type) (A B : (X '
    '-> R) -> X -> R) (f : X -> R), @monotone_op R X A -> @monotone_op R '
    'X B -> (forall (g : X -> R) (x : X), B (A g) x <= A (B g) x) -> (for'
    'all x : X, B f x <= A f x) -> forall (m : nat) (x : X), @iter (X -> '
    'R) m B f x <= @iter (X -> R) m A f x. Proof. exact: @monotone_iter_l'
    'e. Qed. Lemma iter_scale_accepted : forall (R : numDomainType) (X : '
    'Type) (A : (X -> R) -> X -> R) (c : R), @linear_op R X A -> forall ('
    'm : nat) (f : X -> R) (x : X), @iter (X -> R) m (fun (g : X -> R) (y'
    ' : X) => c * A g y) f x = c ^+ m * @iter (X -> R) m A f x. Proof. ex'
    'act: @iter_scale. Qed. Lemma iter_mix_binomial_accepted : forall (R '
    ': numDomainType) (X : Type) (A B : (X -> R) -> X -> R) (p : R), @lin'
    'ear_op R X A -> @linear_op R X B -> (forall f : X -> R, A (B f) = B '
    '(A f)) -> forall (m : nat) (f : X -> R) (x : X), @iter (X -> R) m (f'
    'un (g : X -> R) (y : X) => p * A g y + (1 - p) * B g y) f x = @binom'
    'ial_mean R m p (fun j : nat => @iter (X -> R) j A (@iter (X -> R) (m'
    ' - j) B f) x). Proof. exact: @iter_mix_binomial. Qed. Lemma binomial'
    '_mix_le_iter_accepted : forall (R : numDomainType) (X : Type) (A B C'
    ' : (X -> R) -> X -> R) (p : R) (f : X -> R), 0 <= p <= 1 -> @linear_'
    'op R X A -> @linear_op R X B -> @linear_op R X C -> @monotone_op R X'
    ' A -> @monotone_op R X B -> @monotone_op R X C -> (forall g : X -> R'
    ', A (B g) = B (A g)) -> (forall (g : X -> R) (x : X), A (C g) x <= C'
    ' (A g) x) -> (forall (g : X -> R) (x : X), B (C g) x <= C (B g) x) -'
    '> (forall x : X, p * A f x + (1 - p) * B f x <= C f x) -> forall (m '
    ': nat) (x : X), @binomial_mean R m p (fun j : nat => @iter (X -> R) '
    'j A (@iter (X -> R) (m - j) B f) x) <= @iter (X -> R) m C f x. Proof'
    '. exact: @binomial_mix_le_iter. Qed. Lemma meet_avg_linear_accepted '
    ': forall (R : realFieldType) (T C : finType) (E : C -> {set T}), @li'
    'near_op R {set T} (@meet_avg R T C E). Proof. exact: @meet_avg_linea'
    'r. Qed. Lemma meet_avg_monotone_accepted : forall (R : realFieldType'
    ') (T C : finType) (E : C -> {set T}), @monotone_op R {set T} (@meet_'
    'avg R T C E). Proof. exact: @meet_avg_monotone. Qed. Lemma meet_avg_'
    'cst_accepted : forall (R : realFieldType) (T C : finType) (E : C -> '
    '{set T}) (a : R) (S0 : {set T}), (0 < #|C|)%N -> @meet_avg R T C E ('
    'fun=> a) S0 = a. Proof. exact: @meet_avg_cst. Qed. Lemma meet_avgC_a'
    'ccepted : forall (R : realFieldType) (T C D : finType) (E : C -> {se'
    't T}) (F : D -> {set T}) (f : {set T} -> R), @meet_avg R T C E (@mee'
    't_avg R T D F f) = @meet_avg R T D F (@meet_avg R T C E f). Proof. e'
    'xact: @meet_avgC. Qed. Lemma iter_meet_avg_accepted : forall (R : re'
    'alFieldType) (T C : finType) (E : C -> {set T}) (m : nat) (f : {set '
    'T} -> R) (S : {set T}), @iter ({set T} -> R) m (@meet_avg R T C E) f'
    ' S = @unif_mean R (tuple_tuple_of__canonical__fintype_Finite m C) (f'
    'un t : m.-tuple C => f (S :&: \\bigcap_(c <- t) E c)). Proof. exact: '
    '@iter_meet_avg. Qed. End accepted_commuting_operators. Module accept'
    'ed_boolean_fourier. From HB Require Import structures. From mathcomp'
    ' Require Import all_ssreflect_compat ssralg ssrnum ssrint zmodp. Fro'
    'm mathcomp Require Import matrix. From GaussianAnalysis.matrix Requi'
    're Import euclidean. Import Order.TTheory GRing.Theory Num.Theory. L'
    'ocal Open Scope ring_scope. Require Import GaussianAnalysis.fourier.'
    'boolean_fourier. Lemma bchar_algebra_accepted : forall (t a : nat) ('
    "R : pzRingType), [/\\ forall y : matrix 'F_2 t a, @bchar t a R 0 y = "
    "1, forall p q y : matrix 'F_2 t a, @bchar t a R (p + q) y = @bchar t"
    " a R p y * @bchar t a R q y, forall p y : matrix 'F_2 t a, @bchar t "
    "a R p y = @bchar t a R y p & forall p y : matrix 'F_2 t a, @bchar t "
    'a R p y = 1 \\/ @bchar t a R p y = -1]. Proof. exact: @bchar_algebra.'
    ' Qed. Lemma bchar_orthogonal_accepted : forall (t a : nat) (R : pzRi'
    "ngType), forall p q : matrix 'F_2 t a, \\sum_y @bchar t a R p y * @bc"
    "har t a R q y = (if p == q then #|{: matrix 'F_2 t a}|%:R else 0). P"
    'roof. exact: @bchar_orthogonal. Qed. Lemma bchar_delta_accepted : fo'
    "rall (t a : nat) (R : pzRingType), forall (i : 'I_t) (j : 'I_a) (y :"
    " matrix 'F_2 t a), @bchar t a R (@delta_mx (fintype_ordinal__canonic"
    'al__GRing_PzSemiRing (Zp_trunc (pdiv 2))) t a i j) y = (-1) ^+ nat_o'
    'f_ord (y i j). Proof. exact: @bchar_delta. Qed. Lemma blk_dist_metri'
    "c_accepted : forall t a : nat, [/\\ forall p q : matrix 'F_2 t a, @bl"
    "k_dist t a p q = @blk_deg t a (p + q), forall p q : matrix 'F_2 t a,"
    " @blk_dist t a p q = 0%N <-> p = q, forall p q : matrix 'F_2 t a, @b"
    "lk_dist t a p q = @blk_dist t a q p, forall p q s : matrix 'F_2 t a,"
    ' (@blk_dist t a p s <= @blk_dist t a p q + @blk_dist t a q s)%N & fo'
    "rall p q s : matrix 'F_2 t a, @blk_dist t a (p + s) (q + s) = @blk_d"
    'ist t a p q]. Proof. exact: @blk_dist_metric. Qed. Lemma fcoef_inver'
    'sion_accepted : forall (t a : nat) (R : numFieldType), forall (V : l'
    "modType R) (f : matrix 'F_2 t a -> V) (y : matrix 'F_2 t a), f y = \\"
    'sum_p @bchar t a R p y *: @fcoef t a R V f p. Proof. exact: @fcoef_i'
    'nversion. Qed. Lemma fcoef_expansion_accepted : forall (t a : nat) ('
    "R : numFieldType), forall (V : lmodType R) (c : matrix 'F_2 t a -> V"
    ") (q : matrix 'F_2 t a), @fcoef t a R V (fun y : matrix 'F_2 t a => "
    '\\sum_p @bchar t a R p y *: c p) q = c q. Proof. exact: @fcoef_expans'
    'ion. Qed. Lemma fcoef_plancherel_accepted : forall (t a : nat) (R : '
    'numFieldType), forall (V W Z : lmodType R) (b : V -> W -> Z), (foral'
    'l w : W, linear (b^~ w)) -> (forall v : V, linear (b v)) -> forall ('
    "f : matrix 'F_2 t a -> V) (g : matrix 'F_2 t a -> W), #|{: matrix 'F"
    '_2 t a}|%:R^-1 *: \\sum_y b (f y) (g y) = \\sum_p b (@fcoef t a R V f '
    'p) (@fcoef t a R W g p). Proof. exact: @fcoef_plancherel. Qed. Lemma'
    ' fcoef_linear_accepted : forall (t a : nat) (R : numFieldType), fora'
    "ll (V : lmodType R) (c : R) (f g : matrix 'F_2 t a -> V) (p : matrix"
    " 'F_2 t a), @fcoef t a R V (fun y : matrix 'F_2 t a => c *: f y + g "
    'y) p = c *: @fcoef t a R V f p + @fcoef t a R V g p. Proof. exact: @'
    'fcoef_linear. Qed. Lemma fcoef_comp_linear_accepted : forall (t a : '
    'nat) (R : numFieldType), forall (V W : lmodType R) (h : V -> W), lin'
    "ear h -> forall (f : matrix 'F_2 t a -> V) (p : matrix 'F_2 t a), @f"
    "coef t a R W (fun y : matrix 'F_2 t a => h (f y)) p = h (@fcoef t a "
    'R V f p). Proof. exact: @fcoef_comp_linear. Qed. Lemma fcoef_mulmx_a'
    'ccepted : forall (t a : nat) (R : numFieldType), forall (m n k l : n'
    "at) (A : matrix R m n) (f : matrix 'F_2 t a -> matrix R n k) (B : ma"
    "trix R k l) (p : matrix 'F_2 t a), @fcoef t a R (matrix_matrix__cano"
    "nical__GRing_Lmodule R m l) (fun y : matrix 'F_2 t a => A *m f y *m "
    'B) p = A *m @fcoef t a R (matrix_matrix__canonical__GRing_Lmodule R '
    'n k) f p *m B. Proof. exact: @fcoef_mulmx. Qed. Lemma fcoef_norm_le_'
    'accepted : forall (t a : nat) (R : numFieldType), forall (f : matrix'
    " 'F_2 t a -> R^o) (c : R) (p : matrix 'F_2 t a), (forall y : matrix "
    "'F_2 t a, `|f y : R| <= c) -> `|@fcoef t a R (GRing.GRing_regular__c"
    'anonical__GRing_Lmodule R) f p : R| <= c. Proof. exact: @fcoef_norm_'
    'le. Qed. Lemma fcoef_translate_accepted : forall (t a : nat) (R : nu'
    "mFieldType), forall (V : lmodType R) (f : matrix 'F_2 t a -> V) (p q"
    " : matrix 'F_2 t a), @fcoef t a R V (fun y : matrix 'F_2 t a => @bch"
    'ar t a R q y *: f y) (p + q) = @fcoef t a R V f p. Proof. exact: @fc'
    'oef_translate. Qed. Lemma low_blk_deg_expansion_accepted : forall (t'
    ' a : nat) (R : numFieldType), forall (V : lmodType R) (D : nat) (f :'
    " matrix 'F_2 t a -> V), @low_blk_deg t a R V D f <-> (forall y : mat"
    "rix 'F_2 t a, f y = \\sum_(p | (@blk_deg t a p <= D)%N) @bchar t a R "
    'p y *: @fcoef t a R V f p). Proof. exact: @low_blk_deg_expansion. Qe'
    'd. Lemma low_blk_deg_translate_accepted : forall (t a : nat) (R : nu'
    "mFieldType), forall (V : lmodType R) (D : nat) (f : matrix 'F_2 t a "
    "-> V) (q : matrix 'F_2 t a), (forall p : matrix 'F_2 t a, (D < @blk_"
    'dist t a p q)%N -> @fcoef t a R V f p = 0) -> @low_blk_deg t a R V D'
    " (fun y : matrix 'F_2 t a => @bchar t a R q y *: f y). Proof. exact:"
    ' @low_blk_deg_translate. Qed. Lemma blk_dist_row_accepted : forall ('
    "a : nat) (s z : matrix 'F_2 1 a), @blk_dist 1 a s z = (s != z). Proo"
    'f. exact: @blk_dist_row. Qed. Lemma bchar_col_mx_accepted : forall t'
    "1 t2 a : nat, forall (R : pzRingType) (p1 y1 : matrix 'F_2 t1 a) (p2"
    " y2 : matrix 'F_2 t2 a), @bchar (t1 + t2) a R (@col_mx 'F_2 t1 t2 a "
    "p1 p2) (@col_mx 'F_2 t1 t2 a y1 y2) = @bchar t1 a R p1 y1 * @bchar t"
    '2 a R p2 y2. Proof. exact: @bchar_col_mx. Qed. Lemma blk_col_mx_acce'
    "pted : forall t1 t2 a : nat, forall (p1 q1 : matrix 'F_2 t1 a) (p2 q"
    "2 : matrix 'F_2 t2 a), @blk_deg (t1 + t2) a (@col_mx 'F_2 t1 t2 a p1"
    ' p2) = (@blk_deg t1 a p1 + @blk_deg t2 a p2)%N /\\ @blk_dist (t1 + t2'
    ") a (@col_mx 'F_2 t1 t2 a p1 p2) (@col_mx 'F_2 t1 t2 a q1 q2) = (@bl"
    'k_dist t1 a p1 q1 + @blk_dist t2 a p2 q2)%N. Proof. exact: @blk_col_'
    'mx. Qed. Lemma fcoef_col_mx_accepted : forall t1 t2 a : nat, forall '
    "(R : numFieldType) (V : lmodType R) (f : matrix 'F_2 (t1 + t2) a -> "
    "V) (p1 : matrix 'F_2 t1 a) (p2 : matrix 'F_2 t2 a), @fcoef (t1 + t2)"
    " a R V f (@col_mx 'F_2 t1 t2 a p1 p2) = @fcoef t1 a R V (fun y1 : ma"
    "trix 'F_2 t1 a => @fcoef t2 a R V (fun y2 : matrix 'F_2 t2 a => f (@"
    "col_mx 'F_2 t1 t2 a y1 y2)) p2) p1. Proof. exact: @fcoef_col_mx. Qed"
    '. End accepted_boolean_fourier. Module accepted_psd_factorization. F'
    'rom HB Require Import structures. From mathcomp Require Import all_s'
    'sreflect_compat fingroup perm ssralg ssrnum. From mathcomp Require I'
    'mport matrix sesquilinear boolp classical_sets reals. From mathcomp '
    'Require Import topology normedtype derive exp. From mathcomp Require'
    ' Import arithmetic_tactic ring_tactic. From GaussianAnalysis.matrix '
    'Require Import euclidean real_spectral psd_part. From GaussianAnalys'
    'is.matrix Require Import psd_splitting. From GaussianAnalysis.convex'
    ' Require Import logdet_barrier moreau. Import GRing.Theory Num.Theor'
    'y Order.TTheory. Import numFieldTopology.Exports numFieldNormedType.'
    'Exports. Local Open Scope ring_scope. Local Open Scope classical_set'
    '_scope. Require Import GaussianAnalysis.matrix.psd_factorization. Le'
    'mma psd_factorization_ge0_accepted : forall (R : realType) (I J : fi'
    'nType) (A : I -> J -> R) (r : nat), @psd_factorization R I J A r -> '
    'forall (i : I) (j : J), 0 <= A i j. Proof. exact: @psd_factorization'
    '_ge0. Qed. Lemma psd_factorization_size_gt0_accepted : forall (R : r'
    'ealType) (I J : finType) (A : I -> J -> R) (r : nat), @psd_factoriza'
    'tion R I J A r -> (exists (i : I) (j : J), A i j != 0) -> (0 < r)%N.'
    ' Proof. exact: @psd_factorization_size_gt0. Qed. Lemma psd_factoriza'
    "tion_restrict_accepted : forall (R : realType) (I J I' J' : finType)"
    " (A : I -> J -> R) (r : nat) (f : I' -> I) (g : J' -> J), @psd_facto"
    "rization R I J A r -> @psd_factorization R I' J' (fun (i : I') (j : "
    "J') => A (f i) (g j)) r. Proof. exact: @psd_factorization_restrict. "
    'Qed. Lemma psd_factorization_widen_accepted : forall (R : realType) '
    '(I J : finType) (A : I -> J -> R) (r s : nat), (r <= s)%N -> @psd_fa'
    'ctorization R I J A r -> @psd_factorization R I J A s. Proof. exact:'
    ' @psd_factorization_widen. Qed. Lemma psd_factorization_shift_accept'
    'ed : forall (R : realType) (I J : finType) (A : I -> J -> R) (r : na'
    't) (rho : R), 0 <= rho -> @psd_factorization R I J A r -> @psd_facto'
    'rization R I J (fun (i : I) (j : J) => A i j + rho) r.+1. Proof. exa'
    'ct: @psd_factorization_shift. Qed. Lemma psd_factorization_nonneg_ac'
    "cepted : forall (R : realType) (I J : finType) (r : nat) (a : I -> '"
    "I_r -> R) (b : J -> 'I_r -> R), (forall (i : I) (k : 'I_r), 0 <= a i"
    " k) -> (forall (j : J) (k : 'I_r), 0 <= b j k) -> @psd_factorization"
    ' R I J (fun (i : I) (j : J) => \\sum_(k < r) a i k * b j k) r. Proof.'
    ' exact: @psd_factorization_nonneg. Qed. End accepted_psd_factorizati'
    'on. Module accepted_binomial_bounds. From HB Require Import structur'
    'es. From mathcomp Require Import all_ssreflect_compat ssralg ssrnum '
    'rat reals. From mathcomp Require Import sequences exp. From mathcomp'
    ' Require Import arithmetic_tactic ring_tactic. Import Order.TTheory '
    'GRing.Theory Num.Theory. Local Open Scope ring_scope. Local Open Sco'
    'pe nat_scope. Require Import GaussianAnalysis.combinatorics.binomial'
    '_bounds. Lemma central_bin_le_accepted : forall n : nat, (3 * n).+1 '
    "* 'C(2 * n, n) ^ 2 <= 16 ^ n. Proof. exact: @central_bin_le. Qed. Le"
    'mma central_bin_ge_accepted : forall n : nat, 0 < n -> 16 ^ n <= 4 *'
    " n * 'C(2 * n, n) ^ 2. Proof. exact: @central_bin_ge. Qed. Lemma hal"
    "f_bin_ge_accepted : forall h : nat, 4 ^ h <= 2 * h.+1 * 'C(h, h./2) "
    '^ 2. Proof. exact: @half_bin_ge. Qed. Lemma leq_bin_half_accepted : '
    "forall n k : nat, 'C(n, k) <= 'C(n, n./2). Proof. exact: @leq_bin_ha"
    'lf. Qed. Lemma bin_near_half_accepted : forall h g T : nat, 6 * T <='
    " h -> h <= 2 * (g + T) -> 2 * g <= h + 2 * T -> 'C(h, h./2) <= 2 ^ T"
    ".+1 * 'C(h, g). Proof. exact: @bin_near_half. Qed. Lemma bin_sqr_cen"
    "tral_accepted : forall u j : nat, j <= u -> 'C(u, j) ^ 2 * 'C(2 * u,"
    " u) = 'C(2 * j, j) * 'C(2 * (u - j), u - j) * 'C(2 * u, 2 * j). Proo"
    'f. exact: @bin_sqr_central. Qed. Lemma bin_sqr_ratio_accepted : fora'
    "ll u j : nat, j <= u -> 'C(u, j) ^ 4 * j.+1 * (u - j).+1 <= 4 * u.+1"
    " * 'C(2 * u, 2 * j) ^ 2. Proof. exact: @bin_sqr_ratio. Qed. Lemma bi"
    'n_partial_sum_accepted : forall (R : realType) (N M : nat), M <= N -'
    "> ((\\sum_(j < M.+1) 'C(N, nat_of_ord j)%:R : R) <= ((@expR R 1 * N%:"
    'R / M%:R) ^+ M : R))%R. Proof. exact: @bin_partial_sum. Qed. End acc'
    'epted_binomial_bounds. Module accepted_psd_duality. From HB Require '
    'Import structures. From mathcomp Require Import all_ssreflect_compat'
    ' ssralg ssrnum matrix. From mathcomp Require Import sesquilinear boo'
    'lp classical_sets reals. From mathcomp Require Import topology norme'
    'dtype. From mathcomp Require Import arithmetic_tactic ring_tactic. F'
    'rom GaussianAnalysis.matrix Require Import euclidean real_spectral p'
    'sd_part. From GaussianAnalysis.matrix Require Import psd_splitting p'
    'sd_factorization. From GaussianAnalysis.matrix Require Import nuclea'
    'r condition_cone. From GaussianAnalysis.gaussian Require Import meas'
    'urable_matrix. From GaussianAnalysis.convex Require Import logdet_ba'
    'rrier moreau. Import GRing.Theory Num.Theory Order.TTheory. Import n'
    'umFieldTopology.Exports numFieldNormedType.Exports. Local Open Scope'
    ' ring_scope. Local Open Scope classical_set_scope. Require Import Ga'
    'ussianAnalysis.matrix.psd_duality. Lemma psd_eval_cone_closed_accept'
    "ed : forall (R : realType) (n N : nat) (G : 'I_N -> matrix R n n), ("
    "forall j : 'I_N, @psdmx R n (G j)) -> @closed (matrix_matrix__canoni"
    'cal__topology_structure_Topological 1 N (numFieldTopology.Real_sort_'
    '_canonical__topology_structure_Topological R)) (@psd_eval_cone R n N'
    ' G). Proof. exact: @psd_eval_cone_closed. Qed. Lemma psdmx_dual_acce'
    'pted : forall (R : realType) (n : nat) (S : matrix R n n), S \\is sym'
    'metricmx -> @psdmx R n S <-> (forall F : matrix R n n, @psdmx R n F '
    '-> 0 <= \\tr (F *m S)). Proof. exact: @psdmx_dual. Qed. Lemma psd_far'
    "kas_accepted : forall (R : realType) (n N : nat) (G : 'I_N -> matrix"
    " R n n) (y : matrix R 1 N), (forall j : 'I_N, @psdmx R n (G j)) -> @"
    'psd_eval_cone R n N G y <-> (forall c : matrix R 1 N, @psdmx R n (\\s'
    'um_j c 0 j *: G j) -> 0 <= @mxdot R 1 N c y). Proof. exact: @psd_far'
    'kas. Qed. Lemma psd_slack_certificate_accepted : forall (R : realTyp'
    'e) (n : nat) (I : finType) (B : I -> matrix R n n) (s : I -> R) (i0 '
    ': I), (forall i : I, @psdmx R n (B i)) -> s i0 = 0 -> (exists2 A : m'
    'atrix R n n, @psdmx R n A & forall i : I, \\tr (A *m B i) = s i) <-> '
    '(forall w : I -> R, \\sum_i w i = 1 -> @psdmx R n (\\sum_i w i *: B i)'
    ' -> 0 <= \\sum_i w i * s i). Proof. exact: @psd_slack_certificate. Qe'
    'd. Lemma psd_slack_certificate_affine_accepted : forall (R : realTyp'
    "e) (n m : nat) (I : finType) (C : 'I_m -> matrix R n n) (c : 'I_m ->"
    ' R) (D : matrix R n n) (d : R) (B : I -> matrix R n n) (i0 : I), (fo'
    "rall i : I, @psdmx R n (B i)) -> (forall (i : I) (l : 'I_m), \\tr (C "
    'l *m B i) = c l) -> (forall X : matrix R n n, @psdmx R n X -> (foral'
    "l l : 'I_m, \\tr (C l *m X) = c l) -> 0 <= \\tr (D *m X) + d) -> \\tr ("
    'D *m B i0) + d = 0 -> exists2 A : matrix R n n, @psdmx R n A & foral'
    'l i : I, \\tr (A *m B i) = \\tr (D *m B i) + d. Proof. exact: @psd_sla'
    'ck_certificate_affine. Qed. End accepted_psd_duality. Definition lib'
    'rary_statements_accepted := (accepted_finite_mean.unif_mean_union_ac'
    'cepted, accepted_finite_mean.unif_mean_indicatorN_accepted, accepted'
    '_finite_mean.unif_mean_markov_accepted, accepted_finite_mean.unif_me'
    'an_cutoff_accepted, accepted_finite_mean.unif_chebyshev_accepted, ac'
    'cepted_finite_mean.unif_mean_tuple_prod_ord_accepted, accepted_finit'
    'e_mean.unif_mean_tuple_prod_set_accepted, accepted_binomial_mean.bin'
    'omial_mean0_accepted, accepted_binomial_mean.binomial_meanS_accepted'
    ', accepted_binomial_mean.eq_binomial_mean_accepted, accepted_binomia'
    'l_mean.binomial_mean_cst_accepted, accepted_binomial_mean.binomial_m'
    'eanD_accepted, accepted_binomial_mean.binomial_meanZ_accepted, accep'
    'ted_binomial_mean.ler_binomial_mean_accepted, accepted_binomial_mean'
    '.binomial_mean_id_accepted, accepted_binomial_mean.binomial_mean_sqr'
    '_dev_accepted, accepted_binomial_mean.binomial_chebyshev_accepted, a'
    'ccepted_binomial_mean.binomial_mean_last_accepted, accepted_binomial'
    '_mean.binomial_mean_trials_accepted, accepted_binomial_mean.unif_mea'
    'n_binomial_mean_accepted, accepted_binomial_mean.binomial_meanE_acce'
    'pted, accepted_binomial_mean.integral_binomial_mean_accepted, accept'
    'ed_commuting_operators.homo_iter_accepted, accepted_commuting_operat'
    'ors.iter_le_subcomm_accepted, accepted_commuting_operators.monotone_'
    'iter_le_accepted, accepted_commuting_operators.iter_scale_accepted, '
    'accepted_commuting_operators.iter_mix_binomial_accepted, accepted_co'
    'mmuting_operators.binomial_mix_le_iter_accepted, accepted_commuting_'
    'operators.meet_avg_linear_accepted, accepted_commuting_operators.mee'
    't_avg_monotone_accepted, accepted_commuting_operators.meet_avg_cst_a'
    'ccepted, accepted_commuting_operators.meet_avgC_accepted, accepted_c'
    'ommuting_operators.iter_meet_avg_accepted, accepted_boolean_fourier.'
    'bchar_algebra_accepted, accepted_boolean_fourier.bchar_orthogonal_ac'
    'cepted, accepted_boolean_fourier.bchar_delta_accepted, accepted_bool'
    'ean_fourier.blk_dist_metric_accepted, accepted_boolean_fourier.fcoef'
    '_inversion_accepted, accepted_boolean_fourier.fcoef_expansion_accept'
    'ed, accepted_boolean_fourier.fcoef_plancherel_accepted, accepted_boo'
    'lean_fourier.fcoef_linear_accepted, accepted_boolean_fourier.fcoef_c'
    'omp_linear_accepted, accepted_boolean_fourier.fcoef_mulmx_accepted, '
    'accepted_boolean_fourier.fcoef_norm_le_accepted, accepted_boolean_fo'
    'urier.fcoef_translate_accepted, accepted_boolean_fourier.low_blk_deg'
    '_expansion_accepted, accepted_boolean_fourier.low_blk_deg_translate_'
    'accepted, accepted_boolean_fourier.blk_dist_row_accepted, accepted_b'
    'oolean_fourier.bchar_col_mx_accepted, accepted_boolean_fourier.blk_c'
    'ol_mx_accepted, accepted_boolean_fourier.fcoef_col_mx_accepted, acce'
    'pted_psd_factorization.psd_factorization_ge0_accepted, accepted_psd_'
    'factorization.psd_factorization_size_gt0_accepted, accepted_psd_fact'
    'orization.psd_factorization_restrict_accepted, accepted_psd_factoriz'
    'ation.psd_factorization_widen_accepted, accepted_psd_factorization.p'
    'sd_factorization_shift_accepted, accepted_psd_factorization.psd_fact'
    'orization_nonneg_accepted, accepted_binomial_bounds.central_bin_le_a'
    'ccepted, accepted_binomial_bounds.central_bin_ge_accepted, accepted_'
    'binomial_bounds.half_bin_ge_accepted, accepted_binomial_bounds.leq_b'
    'in_half_accepted, accepted_binomial_bounds.bin_near_half_accepted, a'
    'ccepted_binomial_bounds.bin_sqr_central_accepted, accepted_binomial_'
    'bounds.bin_sqr_ratio_accepted, accepted_binomial_bounds.bin_partial_'
    'sum_accepted, accepted_psd_duality.psd_eval_cone_closed_accepted, ac'
    'cepted_psd_duality.psdmx_dual_accepted, accepted_psd_duality.psd_far'
    'kas_accepted, accepted_psd_duality.psd_slack_certificate_accepted, a'
    'ccepted_psd_duality.psd_slack_certificate_affine_accepted). Print As'
    'sumptions library_statements_accepted.')
# Rules 36 and 37: the shifted-Gaussian extension.
SHIFTED_DEFINITIONS = "check/ShiftedDefinitions.v"
SHIFTED_DEFINITIONS_CHECK = ('From Stdlib Require Import Reals. From mathcomp Require Import all_s'
    'sreflect_compat ssralg ssrnum matrix. From mathcomp Require Import c'
    'lassical_sets reals Rstruct. From mathcomp Require Import ereal topo'
    'logy sequences measure lebesgue_measure. From mathcomp Require Impor'
    't probability. Require GaussianAnalysis.gaussian.measurable_matrix. '
    'Require GaussianAnalysis.analysis.family_reindexing. Require Gaussia'
    'nAnalysis.matrix.euclidean. Require GaussianAnalysis.matrix.coordina'
    'te_blocks. Require GaussianAnalysis.matrix.quadric_certificate. Requ'
    'ire GaussianAnalysis.probability.lindeberg. Require GaussianAnalysis'
    '.probability.tuple_rows. Require GaussianAnalysis.probability.mixtur'
    'e. Require GaussianAnalysis.probability.countable_mixture. Require G'
    'aussianAnalysis.probability.symmetric_shift. Require EllipsoidFittin'
    'g.PaperMainDefinitions. Require EllipsoidFitting.Gaussian.Law.Librar'
    'yBridge. Require EllipsoidUniversality.UniversalityDefinitions. Requ'
    'ire EllipsoidUniversality.MixtureDefinitions. Require EllipsoidUnive'
    'rsality.CountableMixtureDefinitions. Require EllipsoidUniversality.S'
    'at.AprioriSparse. Require EllipsoidUniversality.Shifted.GaussianRows'
    '. Require EllipsoidUniversality.Shifted.Translations. Require Ellips'
    'oidUniversality.Shifted.TranslationError. Require EllipsoidUniversal'
    'ity.Shifted.GaussianCondition. Require EllipsoidUniversality.Shifted'
    '.MixtureRows. Require EllipsoidUniversality.Shifted.SignMixture. Imp'
    'ort (canonicals) GaussianAnalysis.gaussian.measurable_matrix. Import'
    ' (canonicals) GaussianAnalysis.probability.mixture. Import (canonica'
    'ls) GaussianAnalysis.probability.countable_mixture. Local Open Scope'
    ' ring_scope. Local Open Scope classical_set_scope. Local Notation RR'
    ' := (R : realType). Lemma family_sequence_limit_characterization (R '
    ': realType) (u : nat -> R) (a : R) : GaussianAnalysis.analysis.famil'
    'y_reindexing.family_sequence_limit u a <-> forall eps : R, 0 < eps -'
    '> exists D : nat, forall d : nat, (D <= d)%N -> `|u d - a| < eps. Pr'
    'oof. by []. Qed. Lemma coordinate_support_characterization (R : real'
    "Type) (d : nat) (m : 'cV[R]_d) : GaussianAnalysis.matrix.coordinate_"
    "blocks.coordinate_support m = [set i : 'I_d | m i 0 != 0]%SET. Proof"
    '. by []. Qed. Lemma quadric_eval_characterization (R : realType) (n '
    ": nat) (Q : 'M[R]_n) (v : 'cV[R]_n) (c : R) (x : 'cV[R]_n) : Gaussia"
    'nAnalysis.matrix.quadric_certificate.quadric_eval Q v c x = Gaussian'
    'Analysis.matrix.euclidean.mxdot x (Q *m x) + GaussianAnalysis.matrix'
    '.euclidean.mxdot v x + c. Proof. by []. Qed. Lemma tuple_map_charact'
    "erization d d' (T : measurableType d) (T' : measurableType d') (g : "
    "nat -> T -> T') (n : nat) (x : n.-tuple T) : GaussianAnalysis.probab"
    'ility.tuple_rows.tuple_map g x = [tuple g i (tnth x i) | i < n]. Pro'
    'of. by []. Qed. Lemma mixture_weights_characterization (I : finType)'
    ' (R : realType) (w : I -> R) : GaussianAnalysis.probability.mixture.'
    'mixture_weights w <-> (forall i, 0 <= w i) /\\ \\sum_i w i = 1. Proof.'
    ' by []. Qed. Lemma mixture_characterization d (T : measurableType d)'
    ' (R : realType) (I : finType) (w : I -> R) (P : I -> probability T R'
    ') (hw : GaussianAnalysis.probability.mixture.mixture_weights w) (A :'
    ' set T) : (GaussianAnalysis.probability.mixture.mixture P hw : proba'
    'bility T R) A = (\\sum_i (w i)%:E * P i A)%E. Proof. by []. Qed. Lemm'
    'a cmixture_weights_characterization (R : realType) (p : nat -> R) : '
    'GaussianAnalysis.probability.countable_mixture.cmixture_weights p <-'
    '> (forall s, 0 <= p s) /\\ (\\sum_(s <oo) (p s)%:E = 1)%E. Proof. by ['
    ']. Qed. Lemma cmixture_characterization d (T : measurableType d) (R '
    ': realType) (P : nat -> probability T R) (p : nat -> R) (hp : Gaussi'
    'anAnalysis.probability.countable_mixture.cmixture_weights p) (A : se'
    't T) : (GaussianAnalysis.probability.countable_mixture.cmixture P hp'
    ' : probability T R) A = (\\sum_(s <oo) (p s)%:E * P s A)%E. Proof. by'
    ' []. Qed. Lemma row_symmetric_law_characterization (R : realType) (d'
    " : nat) (P : probability 'rV[R]_d R) : GaussianAnalysis.probability."
    "symmetric_shift.row_symmetric_law P <-> forall A : set 'rV[R]_d, mea"
    'surable A -> P ((fun x => - x) @^-1` A) = P A. Proof. by []. Qed. Le'
    "mma row_shift_characterization (R : realType) (d : nat) (m x : 'rV[R"
    ']_d) : GaussianAnalysis.probability.symmetric_shift.row_shift m x = '
    'x + m. Proof. by []. Qed. Lemma row_shift_law_characterization (R : '
    "realType) (d : nat) (P : probability 'rV[R]_d R) (m : 'rV[R]_d) (A :"
    " set 'rV[R]_d) : (GaussianAnalysis.probability.symmetric_shift.row_s"
    "hift_law P m : probability 'rV[R]_d R) A = P [set x | A (x + m)]. Pr"
    'oof. by []. Qed. Lemma sign_shift_weights_characterization (R : real'
    'Type) (w : R) (b : bool) : GaussianAnalysis.probability.symmetric_sh'
    'ift.sign_shift_weights w b = if b then w else 1 - w. Proof. by []. Q'
    'ed. Lemma sign_shift_law_characterization (R : realType) (d : nat) ('
    "P : probability 'rV[R]_d R) (m : 'rV[R]_d) (w : R) (hw : 0 <= w <= 1"
    ") (A : set 'rV[R]_d) : (GaussianAnalysis.probability.symmetric_shift"
    ".sign_shift_law P m hw : probability 'rV[R]_d R) A = (\\sum_(b : bool"
    ') (if b then w else 1 - w)%:E * P [set x | A (x + if b then m else -'
    ' m)%R])%E. Proof. by []. Qed. Lemma row_outer_characterization (R : '
    "realType) (d : nat) (x : 'rV[R]_d) : GaussianAnalysis.probability.sy"
    'mmetric_shift.row_outer x = x^T *m x. Proof. by []. Qed. Lemma row_o'
    'f_tuple_characterization (d : nat) (t : d.-tuple (measurableTypeR R)'
    ') : EllipsoidFitting.Gaussian.Law.LibraryBridge.row_of_tuple d t = \\'
    'row_i (tnth t i : R). Proof. by []. Qed. Lemma point_law_characteriz'
    'ation (d : nat) (nu : nat -> probability (measurableTypeR R) R) (A :'
    " set 'rV[RR]_d) : EllipsoidUniversality.Sat.AprioriSparse.point_law "
    'd nu A = GaussianAnalysis.probability.lindeberg.tuple_prod nu d [set'
    ' t | A (\\row_i (tnth t i : R))]. Proof. by []. Qed. Lemma sample_row'
    '_tuple_characterization (n d : nat) (x : (n * d).-tuple (measurableT'
    'ypeR R)) : @EllipsoidUniversality.Shifted.GaussianRows.sample_row_tu'
    'ple n d x = [tuple (EllipsoidFitting.PaperMainDefinitions.paper_main'
    '_point x i)^T | i < n]. Proof. by []. Qed. Lemma sample_flat_row_cha'
    "racterization (n d : nat) (k : 'I_(n * d)) : nat_of_ord (@EllipsoidU"
    'niversality.Shifted.GaussianRows.sample_flat_row n d k) = (k %/ d)%N'
    '. Proof. by []. Qed. Lemma sample_flat_col_characterization (n d : n'
    "at) (k : 'I_(n * d)) : nat_of_ord (@EllipsoidUniversality.Shifted.Ga"
    'ussianRows.sample_flat_col n d k) = (k %% d)%N. Proof. by []. Qed. L'
    'emma sample_of_row_tuple_characterization (n d : nat) (x : n.-tuple '
    "'rV[RR]_d) : @EllipsoidUniversality.Shifted.GaussianRows.sample_of_r"
    'ow_tuple n d x = [tuple tnth x (EllipsoidUniversality.Shifted.Gaussi'
    'anRows.sample_flat_row k) 0 (EllipsoidUniversality.Shifted.GaussianR'
    'ows.sample_flat_col k) | k < n * d]. Proof. by []. Qed. Lemma sample'
    "_translate_characterization (n d : nat) (m : 'cV[RR]_d) (x : (n * d)"
    '.-tuple (measurableTypeR R)) : @EllipsoidUniversality.Shifted.Transl'
    'ations.sample_translate n d m x = @EllipsoidUniversality.Shifted.Gau'
    'ssianRows.sample_of_row_tuple n d [tuple tnth (EllipsoidUniversality'
    '.Shifted.GaussianRows.sample_row_tuple x) i + m^T | i < n]. Proof. b'
    'y []. Qed. Lemma translation_fitting_error_characterization (n d : n'
    'at) (x : (n * d).-tuple (measurableTypeR R)) : EllipsoidUniversality'
    '.Shifted.TranslationError.translation_fitting_error n d x = inf [set'
    ' EllipsoidUniversality.UniversalityDefinitions.universality_fitting_'
    'error n d (EllipsoidUniversality.Shifted.Translations.sample_transla'
    "te m x) | m in [set: 'cV[RR]_d]]. Proof. by []. Qed. Lemma gaussian_"
    "small_shift_characterization (m : forall d : nat, 'cV[R]_d) : Ellips"
    'oidUniversality.Shifted.GaussianCondition.gaussian_small_shift m <->'
    ' forall e : R, 0 < e -> exists D : nat, forall d : nat, (D <= d)%N -'
    '> GaussianAnalysis.matrix.euclidean.frobenius (m d) <= e * Num.sqrt '
    'd%:R. Proof. by []. Qed. Lemma finite_row_law_characterization (K : '
    'R) (N : nat -> nat) (w : nat -> nat -> R) (mu : nat -> nat -> nat ->'
    ' probability (measurableTypeR R) R) (hfam : EllipsoidUniversality.Mi'
    "xtureDefinitions.mixture_family K N w mu) (d : nat) (A : set 'rV[RR]"
    '_d) : EllipsoidUniversality.Shifted.MixtureRows.finite_row_law hfam '
    'd A = (\\sum_(s < N d) (w d s)%:E * EllipsoidUniversality.Sat.Apriori'
    'Sparse.point_law d (mu d s) A)%E. Proof. by []. Qed. Lemma countable'
    '_row_law_characterization (K : R) (w : nat -> nat -> R) (mu : nat ->'
    ' nat -> nat -> probability (measurableTypeR R) R) (hfam : EllipsoidU'
    'niversality.CountableMixtureDefinitions.countable_mixture_family K w'
    " mu) (d : nat) (A : set 'rV[RR]_d) : EllipsoidUniversality.Shifted.M"
    'ixtureRows.countable_row_law hfam d A = (\\sum_(s <oo) (w d s)%:E * E'
    'llipsoidUniversality.Sat.AprioriSparse.point_law d (mu d s) A)%E. Pr'
    'oof. by []. Qed. Lemma row_sample_map_characterization (n d : nat) ('
    "x : n.-tuple 'rV[RR]_d) : EllipsoidUniversality.Shifted.SignMixture."
    'row_sample_map n d x = @EllipsoidUniversality.Shifted.GaussianRows.s'
    'ample_of_row_tuple n d x. Proof. by []. Qed. Lemma iid_row_sample_la'
    "w_characterization (d : nat) (P : probability 'rV[RR]_d RR) (n : nat"
    ') (A : set ((n * d).-tuple (measurableTypeR R))) : EllipsoidUniversa'
    'lity.Shifted.SignMixture.iid_row_sample_law P n A = GaussianAnalysis'
    '.probability.lindeberg.tuple_prod (fun _ => P) n (@EllipsoidUniversa'
    'lity.Shifted.GaussianRows.sample_of_row_tuple n d @^-1` A). Proof. b'
    'y []. Qed. Lemma shifted_iid_sample_law_characterization (d : nat) ('
    "P : probability 'rV[RR]_d RR) (m : 'cV[R]_d) (n : nat) (A : set ((n "
    '* d).-tuple (measurableTypeR R))) : EllipsoidUniversality.Shifted.Si'
    'gnMixture.shifted_iid_sample_law P m n A = GaussianAnalysis.probabil'
    'ity.lindeberg.tuple_prod (fun _ => GaussianAnalysis.probability.symm'
    'etric_shift.row_shift_law P m^T) n (@EllipsoidUniversality.Shifted.G'
    'aussianRows.sample_of_row_tuple n d @^-1` A). Proof. by []. Qed. Lem'
    'ma sign_mixture_sample_law_characterization (d : nat) (P : probabili'
    "ty 'rV[RR]_d RR) (m : 'cV[R]_d) (w : R) (hw : 0 <= w <= 1) (n : nat)"
    ' (A : set ((n * d).-tuple (measurableTypeR R))) : EllipsoidUniversal'
    'ity.Shifted.SignMixture.sign_mixture_sample_law P m hw n A = Gaussia'
    'nAnalysis.probability.lindeberg.tuple_prod (fun _ => GaussianAnalysi'
    's.probability.symmetric_shift.sign_shift_law P m^T hw) n (@Ellipsoid'
    'Universality.Shifted.GaussianRows.sample_of_row_tuple n d @^-1` A). '
    'Proof. by []. Qed. Definition shifted_characterizations := (@family_'
    'sequence_limit_characterization, @coordinate_support_characterizatio'
    'n, @quadric_eval_characterization, @tuple_map_characterization, @mix'
    'ture_weights_characterization, @mixture_characterization, @cmixture_'
    'weights_characterization, @cmixture_characterization, @row_symmetric'
    '_law_characterization, @row_shift_characterization, @row_shift_law_c'
    'haracterization, @sign_shift_weights_characterization, @sign_shift_l'
    'aw_characterization, @row_outer_characterization, @row_of_tuple_char'
    'acterization, @point_law_characterization, @sample_row_tuple_charact'
    'erization, @sample_flat_row_characterization, @sample_flat_col_chara'
    'cterization, @sample_of_row_tuple_characterization, @sample_translat'
    'e_characterization, @translation_fitting_error_characterization, @ga'
    'ussian_small_shift_characterization, @finite_row_law_characterizatio'
    'n, @countable_row_law_characterization, @row_sample_map_characteriza'
    'tion, @iid_row_sample_law_characterization, @shifted_iid_sample_law_'
    'characterization, @sign_mixture_sample_law_characterization). Print '
    'Assumptions shifted_characterizations.')
SHIFTED_CHECKS = {
    "Condition": ('Require EllipsoidUniversality.ShiftedConditionStatement. Require Ell'
        'ipsoidUniversality.Shifted.ConditionTheorem. Definition shifted_cond'
        'ition_identity : EllipsoidUniversality.ShiftedConditionStatement.shi'
        'fted_condition_statement := EllipsoidUniversality.Shifted.ConditionT'
        'heorem.shifted_condition_theorem. Locate shifted_condition_identity.'
        ' Print Assumptions shifted_condition_identity.'),
    "Gaussian": ('Require EllipsoidUniversality.ShiftedGaussianStatement. Require Elli'
        'psoidUniversality.Shifted.GaussianTheorem. Definition shifted_gaussi'
        'an_identity : EllipsoidUniversality.ShiftedGaussianStatement.shifted'
        '_gaussian_statement := EllipsoidUniversality.Shifted.GaussianTheorem'
        '.shifted_gaussian_theorem. Locate shifted_gaussian_identity. Print A'
        'ssumptions shifted_gaussian_identity.'),
    "Quadric": ('Require EllipsoidUniversality.ShiftedQuadricStatement. Require Ellip'
        'soidUniversality.Shifted.QuadricTheorem. Definition shifted_quadric_'
        'identity : EllipsoidUniversality.ShiftedQuadricStatement.shifted_qua'
        'dric_statement := EllipsoidUniversality.Shifted.QuadricTheorem.shift'
        'ed_quadric_theorem. Locate shifted_quadric_identity. Print Assumptio'
        'ns shifted_quadric_identity.'),
    "Error": ('Require EllipsoidUniversality.ShiftedErrorStatement. Require Ellipso'
        'idUniversality.Shifted.ErrorTheorem. Definition shifted_error_identi'
        'ty : EllipsoidUniversality.ShiftedErrorStatement.shifted_error_state'
        'ment := EllipsoidUniversality.Shifted.ErrorTheorem.shifted_error_the'
        'orem. Locate shifted_error_identity. Print Assumptions shifted_error'
        '_identity.'),
    "MixtureUnsat": ('Require EllipsoidUniversality.ShiftedMixtureUnsatStatement. Require '
        'EllipsoidUniversality.Shifted.MixtureUnsatTheorem. Definition shifte'
        'd_mixture_unsat_identity : EllipsoidUniversality.ShiftedMixtureUnsat'
        'Statement.shifted_mixture_unsat_statement := EllipsoidUniversality.S'
        'hifted.MixtureUnsatTheorem.shifted_mixture_unsat_theorem. Locate shi'
        'fted_mixture_unsat_identity. Print Assumptions shifted_mixture_unsat'
        '_identity.'),
    "MixtureSat": ('Require EllipsoidUniversality.ShiftedMixtureSatStatement. Require El'
        'lipsoidUniversality.Shifted.MixtureSatTheorem. Definition shifted_mi'
        'xture_sat_identity : EllipsoidUniversality.ShiftedMixtureSatStatemen'
        't.shifted_mixture_sat_statement := EllipsoidUniversality.Shifted.Mix'
        'tureSatTheorem.shifted_mixture_sat_theorem. Locate shifted_mixture_s'
        'at_identity. Print Assumptions shifted_mixture_sat_identity.'),
    "Sign": ('Require EllipsoidUniversality.ShiftedSignStatement. Require Ellipsoi'
        'dUniversality.Shifted.SignTheorem. Definition shifted_sign_identity '
        ': EllipsoidUniversality.ShiftedSignStatement.shifted_sign_statement '
        ':= EllipsoidUniversality.Shifted.SignTheorem.shifted_sign_theorem. L'
        'ocate shifted_sign_identity. Print Assumptions shifted_sign_identity'
        '.'),
}
SHIFTED_THEOREMS = [
    ("shifted condition theorem", "check/ShiftedConditionAssumptions.v", SHIFTED_CHECKS["Condition"],
     "check/shifted_condition_assumptions.expected"),
    ("shifted Gaussian theorem", "check/ShiftedGaussianAssumptions.v", SHIFTED_CHECKS["Gaussian"],
     "check/shifted_gaussian_assumptions.expected"),
    ("shifted quadric theorem", "check/ShiftedQuadricAssumptions.v", SHIFTED_CHECKS["Quadric"],
     "check/shifted_quadric_assumptions.expected"),
    ("shifted error theorem", "check/ShiftedErrorAssumptions.v", SHIFTED_CHECKS["Error"],
     "check/shifted_error_assumptions.expected"),
    ("shifted mixture nonexistence theorem", "check/ShiftedMixtureUnsatAssumptions.v", SHIFTED_CHECKS["MixtureUnsat"],
     "check/shifted_mixture_unsat_assumptions.expected"),
    ("shifted mixture existence theorem", "check/ShiftedMixtureSatAssumptions.v", SHIFTED_CHECKS["MixtureSat"],
     "check/shifted_mixture_sat_assumptions.expected"),
    ("shifted sign theorem", "check/ShiftedSignAssumptions.v", SHIFTED_CHECKS["Sign"],
     "check/shifted_sign_assumptions.expected"),
]
# Every theorem whose axiom report the script takes, in the order of its
# arguments, and the path of its report: the arguments must be exactly the
# paths of REPORTS.
THEOREMS = (["main theorem", "universality theorem"]
            + [name for name, _, _, _ in PHASE6_THEOREMS + PHASE8_THEOREMS
               + PHASE9_THEOREMS + PHASE10_THEOREMS + PHASE11_THEOREMS
               + PHASE12_THEOREMS + PHASE13_THEOREMS + PHASE14_THEOREMS
               + SHIFTED_THEOREMS])
REPORTS = [
    "build/assumptions.txt",
    "build/universality_assumptions.txt",
    "build/mixture_assumptions.txt",
    "build/paired_assumptions.txt",
    "build/latent_sign_assumptions.txt",
    "build/countable_assumptions.txt",
    "build/condition_assumptions.txt",
    "build/latent_scope_assumptions.txt",
    "build/robust_assumptions.txt",
    "build/latent_tensor_assumptions.txt",
    "build/continuous_latent_assumptions.txt",
    "build/condition_endpoints_assumptions.txt",
    "build/condition_robust_assumptions.txt",
    "build/latent_tensor_upper_assumptions.txt",
    "build/condition_kappa_curve_assumptions.txt",
    "build/condition_kappa_assumptions.txt",
    "build/condition_kappa_robust_assumptions.txt",
    "build/matrix_series_assumptions.txt",
    "build/tensor_packing_assumptions.txt",
    "build/goe_edge_assumptions.txt",
    "build/sk_gap_assumptions.txt",
    "build/psd_splitting_assumptions.txt",
    "build/perceptron_sign_assumptions.txt",
    "build/sat_variance_assumptions.txt",
    "build/sat_threshold_assumptions.txt",
    "build/psd_normalization_assumptions.txt",
    "build/product_smoothing_assumptions.txt",
    "build/min_superadditive_assumptions.txt",
    "build/psd_rank_assumptions.txt",
    "build/psd_lift_assumptions.txt",
    "build/shifted_condition_assumptions.txt",
    "build/shifted_gaussian_assumptions.txt",
    "build/shifted_quadric_assumptions.txt",
    "build/shifted_error_assumptions.txt",
    "build/shifted_mixture_unsat_assumptions.txt",
    "build/shifted_mixture_sat_assumptions.txt",
    "build/shifted_sign_assumptions.txt",
]
assert len(REPORTS) == len(THEOREMS)
# Rule 30. The check files that scripts/run_checks.py compiles, with their
# flags, their outputs, their stage (stage 2 requires compiled check files of
# stage 1) and what each output must hold: ("empty",), nothing; ("reports",
# n, list), n complete reports within the list; ("marked", pairs), for each
# pair (marker, list, label) the marker line of the name (none for the
# pinned check files of phases 1 to 12, identified by the runner's record)
# followed by one complete report within the list; ("snapshot", reference,
# SHA-256), exactly the reference.
class CheckFile(NamedTuple):
    source: str
    flags: tuple
    output: str
    stage: int
    expect: tuple


LIB_CHECK_FLAGS = ("-w", "-notation-overridden", "-w", "-ambiguous-paths", "-w", "-notation-incompatible-prefix", "-w", "-hiding-delimiting-key", "-Q", "library", "GaussianAnalysis")
PAPER_CHECK_FLAGS = ("-Q", "library", "GaussianAnalysis", "-Q", "theories", "EllipsoidFitting")
EXTENSION_CHECK_FLAGS = PAPER_CHECK_FLAGS + ("-Q", "extension", "EllipsoidUniversality")
APPLICATION_CHECK_FLAGS = ("-Q", "library", "GaussianAnalysis",
                           "-Q", "applications", "GaussianApplications")
ALL_CHECK_FLAGS = LIB_CHECK_FLAGS + ("-Q", "theories", "EllipsoidFitting",
                                     "-Q", "extension", "EllipsoidUniversality",
                                     "-Q", "applications", "GaussianApplications")
SEVEN_AXIOMS = "check/sat_variance_assumptions.expected"
EXPECTED_LISTS = dict([("main theorem", "check/assumptions.expected"),
                       ("universality theorem", "check/universality_assumptions.expected")]
                      + [(name, expected) for name, _, _, expected in
                         PHASE6_THEOREMS + PHASE8_THEOREMS + PHASE9_THEOREMS
                         + PHASE10_THEOREMS + PHASE11_THEOREMS + PHASE12_THEOREMS
                         + PHASE13_THEOREMS + PHASE14_THEOREMS + SHIFTED_THEOREMS])
# check/TheoremIdentities.v: the full name of each identity, its list, its label.
THEOREM_IDENTITIES = [
    ("Checks.TheoremIdentities.ellipsoid_fitting_main_identity", EXPECTED_LISTS["main theorem"], "main theorem"),
    ("Checks.TheoremIdentities.universality_theorem_identity", EXPECTED_LISTS["universality theorem"], "universality theorem"),
    ("Checks.TheoremIdentities.mixture_theorem_identity", EXPECTED_LISTS["mixture theorem"], "mixture theorem"),
    ("Checks.TheoremIdentities.paired_theorem_identity", EXPECTED_LISTS["paired theorem"], "paired theorem"),
    ("Checks.TheoremIdentities.latent_sign_theorem_identity", EXPECTED_LISTS["latent-sign theorem"], "latent-sign theorem"),
    ("Checks.TheoremIdentities.countable_theorem_identity", EXPECTED_LISTS["countable-mixture theorem"], "countable-mixture theorem"),
    ("Checks.TheoremIdentities.condition_theorem_identity", EXPECTED_LISTS["condition-number theorem"], "condition-number theorem"),
    ("Checks.TheoremIdentities.latent_scope_theorem_identity", EXPECTED_LISTS["latent-sign scope theorem"], "latent-sign scope theorem"),
    ("Checks.TheoremIdentities.robust_theorem_identity", EXPECTED_LISTS["robustness theorem"], "robustness theorem"),
    ("Checks.TheoremIdentities.latent_tensor_theorem_identity", EXPECTED_LISTS["tensorization theorem"], "tensorization theorem"),
    ("Checks.TheoremIdentities.continuous_latent_theorem_identity", EXPECTED_LISTS["continuous-latent theorem"], "continuous-latent theorem"),
    ("Checks.TheoremIdentities.condition_endpoints_theorem_identity", EXPECTED_LISTS["condition-endpoints theorem"], "condition-endpoints theorem"),
    ("Checks.TheoremIdentities.robust_condition_theorem_identity", EXPECTED_LISTS["robust condition-number theorem"], "robust condition-number theorem"),
    ("Checks.TheoremIdentities.latent_tensor_upper_theorem_identity", EXPECTED_LISTS["tensorization upper bound"], "tensorization upper bound"),
    ("Checks.TheoremIdentities.condition_kappa_curve_theorem_identity", EXPECTED_LISTS["condition-number curve at kappa"], "condition-number curve at kappa"),
    ("Checks.TheoremIdentities.condition_kappa_theorem_identity", EXPECTED_LISTS["condition-number theorem at kappa"], "condition-number theorem at kappa"),
    ("Checks.TheoremIdentities.condition_kappa_robust_theorem_identity", EXPECTED_LISTS["robust condition-number theorem at kappa"], "robust condition-number theorem at kappa"),
    ("Checks.TheoremIdentities.matrix_series_theorem_identity", EXPECTED_LISTS["Gaussian matrix series theorem"], "Gaussian matrix series theorem"),
    ("Checks.TheoremIdentities.tensor_packing_theorem_identity", EXPECTED_LISTS["tensor packing theorem"], "tensor packing theorem"),
    ("Checks.TheoremIdentities.goe_edge_theorem_identity", EXPECTED_LISTS["GOE edge theorem"], "GOE edge theorem"),
    ("Checks.TheoremIdentities.sk_gap_theorem_identity", EXPECTED_LISTS["SK spectral gap theorem"], "SK spectral gap theorem"),
    ("Checks.TheoremIdentities.psd_splitting_theorem_identity", EXPECTED_LISTS["orthogonal splitting theorem"], "orthogonal splitting theorem"),
    ("Checks.TheoremIdentities.perceptron_sign_theorem_identity", EXPECTED_LISTS["perceptron comparison theorem"], "perceptron comparison theorem"),
    ("Checks.TheoremIdentities.sat_variance_theorem_identity", EXPECTED_LISTS["k-SAT variance theorem"], "k-SAT variance theorem"),
    ("Checks.TheoremIdentities.sat_threshold_theorem_identity", EXPECTED_LISTS["satisfiability threshold theorem"], "satisfiability threshold theorem"),
    ("Checks.TheoremIdentities.psd_normalization_theorem_identity", EXPECTED_LISTS["PSD normalization theorem"], "PSD normalization theorem"),
    ("Checks.TheoremIdentities.product_smoothing_theorem_identity", EXPECTED_LISTS["product smoothing theorem"], "product smoothing theorem"),
    ("Checks.TheoremIdentities.min_superadditive_theorem_identity", EXPECTED_LISTS["min-superadditive convergence theorem"], "min-superadditive convergence theorem"),
]
# check/Reports.v: the full name of each lemma, its list, its label.
MARKED_REPORTS = [
    ("Checks.ApplicationsDefinitions.mxdot_characterization", SEVEN_AXIOMS, "Checks.ApplicationsDefinitions.mxdot_characterization"),
    ("Checks.ApplicationsDefinitions.frobenius_characterization", SEVEN_AXIOMS, "Checks.ApplicationsDefinitions.frobenius_characterization"),
    ("Checks.ApplicationsDefinitions.opnorm_characterization", SEVEN_AXIOMS, "Checks.ApplicationsDefinitions.opnorm_characterization"),
    ("Checks.ApplicationsDefinitions.psdmx_characterization", SEVEN_AXIOMS, "Checks.ApplicationsDefinitions.psdmx_characterization"),
    ("Checks.ApplicationsDefinitions.goe_mx_characterization", SEVEN_AXIOMS, "Checks.ApplicationsDefinitions.goe_mx_characterization"),
    ("Checks.ApplicationsDefinitions.matrix_measurable_characterization", SEVEN_AXIOMS, "Checks.ApplicationsDefinitions.matrix_measurable_characterization"),
    ("Checks.ApplicationsDefinitions.gauss_characterization", SEVEN_AXIOMS, "Checks.ApplicationsDefinitions.gauss_characterization"),
    ("Checks.ApplicationsDefinitions.gauss_determined", SEVEN_AXIOMS, "Checks.ApplicationsDefinitions.gauss_determined"),
    ("Checks.MatrixSigmaRing.matrix_sigma_ring_characterization", SEVEN_AXIOMS, "Checks.MatrixSigmaRing.matrix_sigma_ring_characterization"),
    ("Checks.Phase13Definitions.unif_mean_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.unif_mean_characterization"),
    ("Checks.Phase13Definitions.unif_var_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.unif_var_characterization"),
    ("Checks.Phase13Definitions.binomial_mean_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.binomial_mean_characterization"),
    ("Checks.Phase13Definitions.linear_op_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.linear_op_characterization"),
    ("Checks.Phase13Definitions.monotone_op_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.monotone_op_characterization"),
    ("Checks.Phase13Definitions.meet_avg_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.meet_avg_characterization"),
    ("Checks.Phase13Definitions.bdot_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.bdot_characterization"),
    ("Checks.Phase13Definitions.bchar_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.bchar_characterization"),
    ("Checks.Phase13Definitions.blk_deg_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.blk_deg_characterization"),
    ("Checks.Phase13Definitions.blk_dist_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.blk_dist_characterization"),
    ("Checks.Phase13Definitions.fcoef_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.fcoef_characterization"),
    ("Checks.Phase13Definitions.low_blk_deg_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.low_blk_deg_characterization"),
    ("Checks.Phase13Definitions.prob_vec_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.prob_vec_characterization"),
    ("Checks.Phase13Definitions.prod_avg_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.prod_avg_characterization"),
    ("Checks.Phase13Definitions.smoothing_hyps_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.smoothing_hyps_characterization"),
    ("Checks.Phase13Definitions.weighted_gram_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.weighted_gram_characterization"),
    ("Checks.Phase13Definitions.psd_factorization_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.psd_factorization_characterization"),
    ("Checks.Phase13Definitions.psd_eval_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.psd_eval_characterization"),
    ("Checks.Phase13Definitions.psd_eval_cone_characterization", SEVEN_AXIOMS, "Checks.Phase13Definitions.psd_eval_cone_characterization"),
    ("Checks.LibraryStatements.accepted_finite_mean.unif_mean_union_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_finite_mean.unif_mean_union_accepted"),
    ("Checks.LibraryStatements.accepted_finite_mean.unif_mean_indicatorN_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_finite_mean.unif_mean_indicatorN_accepted"),
    ("Checks.LibraryStatements.accepted_finite_mean.unif_mean_markov_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_finite_mean.unif_mean_markov_accepted"),
    ("Checks.LibraryStatements.accepted_finite_mean.unif_mean_cutoff_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_finite_mean.unif_mean_cutoff_accepted"),
    ("Checks.LibraryStatements.accepted_finite_mean.unif_chebyshev_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_finite_mean.unif_chebyshev_accepted"),
    ("Checks.LibraryStatements.accepted_finite_mean.unif_mean_tuple_prod_ord_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_finite_mean.unif_mean_tuple_prod_ord_accepted"),
    ("Checks.LibraryStatements.accepted_finite_mean.unif_mean_tuple_prod_set_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_finite_mean.unif_mean_tuple_prod_set_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.binomial_mean0_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean0_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.binomial_meanS_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.binomial_meanS_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.eq_binomial_mean_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.eq_binomial_mean_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_cst_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_cst_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.binomial_meanD_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.binomial_meanD_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.binomial_meanZ_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.binomial_meanZ_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.ler_binomial_mean_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.ler_binomial_mean_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_id_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_id_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_sqr_dev_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_sqr_dev_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.binomial_chebyshev_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.binomial_chebyshev_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_last_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_last_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_trials_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_trials_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.unif_mean_binomial_mean_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.unif_mean_binomial_mean_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.binomial_meanE_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.binomial_meanE_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_mean.integral_binomial_mean_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_mean.integral_binomial_mean_accepted"),
    ("Checks.LibraryStatements.accepted_commuting_operators.homo_iter_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_commuting_operators.homo_iter_accepted"),
    ("Checks.LibraryStatements.accepted_commuting_operators.iter_le_subcomm_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_commuting_operators.iter_le_subcomm_accepted"),
    ("Checks.LibraryStatements.accepted_commuting_operators.monotone_iter_le_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_commuting_operators.monotone_iter_le_accepted"),
    ("Checks.LibraryStatements.accepted_commuting_operators.iter_scale_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_commuting_operators.iter_scale_accepted"),
    ("Checks.LibraryStatements.accepted_commuting_operators.iter_mix_binomial_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_commuting_operators.iter_mix_binomial_accepted"),
    ("Checks.LibraryStatements.accepted_commuting_operators.binomial_mix_le_iter_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_commuting_operators.binomial_mix_le_iter_accepted"),
    ("Checks.LibraryStatements.accepted_commuting_operators.meet_avg_linear_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_commuting_operators.meet_avg_linear_accepted"),
    ("Checks.LibraryStatements.accepted_commuting_operators.meet_avg_monotone_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_commuting_operators.meet_avg_monotone_accepted"),
    ("Checks.LibraryStatements.accepted_commuting_operators.meet_avg_cst_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_commuting_operators.meet_avg_cst_accepted"),
    ("Checks.LibraryStatements.accepted_commuting_operators.meet_avgC_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_commuting_operators.meet_avgC_accepted"),
    ("Checks.LibraryStatements.accepted_commuting_operators.iter_meet_avg_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_commuting_operators.iter_meet_avg_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.bchar_algebra_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.bchar_algebra_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.bchar_orthogonal_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.bchar_orthogonal_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.bchar_delta_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.bchar_delta_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.blk_dist_metric_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.blk_dist_metric_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.fcoef_inversion_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_inversion_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.fcoef_expansion_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_expansion_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.fcoef_plancherel_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_plancherel_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.fcoef_linear_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_linear_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.fcoef_comp_linear_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_comp_linear_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.fcoef_mulmx_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_mulmx_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.fcoef_norm_le_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_norm_le_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.fcoef_translate_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_translate_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.low_blk_deg_expansion_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.low_blk_deg_expansion_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.low_blk_deg_translate_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.low_blk_deg_translate_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.blk_dist_row_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.blk_dist_row_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.bchar_col_mx_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.bchar_col_mx_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.blk_col_mx_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.blk_col_mx_accepted"),
    ("Checks.LibraryStatements.accepted_boolean_fourier.fcoef_col_mx_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_boolean_fourier.fcoef_col_mx_accepted"),
    ("Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_ge0_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_ge0_accepted"),
    ("Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_size_gt0_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_size_gt0_accepted"),
    ("Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_restrict_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_restrict_accepted"),
    ("Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_widen_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_widen_accepted"),
    ("Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_shift_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_shift_accepted"),
    ("Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_nonneg_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_nonneg_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_bounds.central_bin_le_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_bounds.central_bin_le_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_bounds.central_bin_ge_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_bounds.central_bin_ge_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_bounds.half_bin_ge_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_bounds.half_bin_ge_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_bounds.leq_bin_half_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_bounds.leq_bin_half_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_bounds.bin_near_half_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_bounds.bin_near_half_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_bounds.bin_sqr_central_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_bounds.bin_sqr_central_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_bounds.bin_sqr_ratio_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_bounds.bin_sqr_ratio_accepted"),
    ("Checks.LibraryStatements.accepted_binomial_bounds.bin_partial_sum_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_binomial_bounds.bin_partial_sum_accepted"),
    ("Checks.LibraryStatements.accepted_psd_duality.psd_eval_cone_closed_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_psd_duality.psd_eval_cone_closed_accepted"),
    ("Checks.LibraryStatements.accepted_psd_duality.psdmx_dual_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_psd_duality.psdmx_dual_accepted"),
    ("Checks.LibraryStatements.accepted_psd_duality.psd_farkas_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_psd_duality.psd_farkas_accepted"),
    ("Checks.LibraryStatements.accepted_psd_duality.psd_slack_certificate_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_psd_duality.psd_slack_certificate_accepted"),
    ("Checks.LibraryStatements.accepted_psd_duality.psd_slack_certificate_affine_accepted", SEVEN_AXIOMS, "Checks.LibraryStatements.accepted_psd_duality.psd_slack_certificate_affine_accepted"),
]
# check/Phase14Identities.v and check/Phase14Reports.v (rule 33), beside the
# pinned check/TheoremIdentities.v and check/Reports.v.
PHASE14_IDENTITIES = [
    ("Checks.Phase14Identities.psd_rank_theorem_identity", EXPECTED_LISTS["PSD rank theorem"], "PSD rank theorem"),
    ("Checks.Phase14Identities.psd_lift_theorem_identity", EXPECTED_LISTS["PSD lift corollary"], "PSD lift corollary"),
]
PHASE14_REPORTS = [
    ("Checks.Phase14Definitions.ksubset_characterization", SEVEN_AXIOMS, "Checks.Phase14Definitions.ksubset_characterization"),
    ("Checks.Phase14Definitions.ksubset_mx_characterization", SEVEN_AXIOMS, "Checks.Phase14Definitions.ksubset_mx_characterization"),
    ("Checks.Phase14Definitions.perm_cut_characterization", SEVEN_AXIOMS, "Checks.Phase14Definitions.perm_cut_characterization"),
    ("Checks.Phase14Statements.accepted_multiplicity.trace_multiplicity_accepted", SEVEN_AXIOMS, "Checks.Phase14Statements.accepted_multiplicity.trace_multiplicity_accepted"),
    ("Checks.Phase14Statements.accepted_multiplicity.ksubset_multiplicity_accepted", SEVEN_AXIOMS, "Checks.Phase14Statements.accepted_multiplicity.ksubset_multiplicity_accepted"),
    ("Checks.Phase14Statements.accepted_harmonic.harmonic_ln_accepted", SEVEN_AXIOMS, "Checks.Phase14Statements.accepted_harmonic.harmonic_ln_accepted"),
    ("Checks.Phase14Statements.accepted_binomial_bounds.bin_mul_pow_accepted", SEVEN_AXIOMS, "Checks.Phase14Statements.accepted_binomial_bounds.bin_mul_pow_accepted"),
    ("Checks.Phase14Statements.accepted_expander.expander_accepted", SEVEN_AXIOMS, "Checks.Phase14Statements.accepted_expander.expander_accepted"),
]
# check/ShiftedIdentities.v and check/ShiftedReports.v (rule 37): the seven
# identities, then the joint identity of the seven, and the characterization
# lemmas of check/ShiftedDefinitions.v.
SHIFTED_IDENTITIES = [
    ("Checks.ShiftedIdentities.shifted_condition_identity", EXPECTED_LISTS["shifted condition theorem"], "shifted condition theorem"),
    ("Checks.ShiftedIdentities.shifted_gaussian_identity", EXPECTED_LISTS["shifted Gaussian theorem"], "shifted Gaussian theorem"),
    ("Checks.ShiftedIdentities.shifted_quadric_identity", EXPECTED_LISTS["shifted quadric theorem"], "shifted quadric theorem"),
    ("Checks.ShiftedIdentities.shifted_error_identity", EXPECTED_LISTS["shifted error theorem"], "shifted error theorem"),
    ("Checks.ShiftedIdentities.shifted_mixture_unsat_identity", EXPECTED_LISTS["shifted mixture nonexistence theorem"], "shifted mixture nonexistence theorem"),
    ("Checks.ShiftedIdentities.shifted_mixture_sat_identity", EXPECTED_LISTS["shifted mixture existence theorem"], "shifted mixture existence theorem"),
    ("Checks.ShiftedIdentities.shifted_sign_identity", EXPECTED_LISTS["shifted sign theorem"], "shifted sign theorem"),
]
SHIFTED_JOINT_IDENTITY = ("Checks.ShiftedIdentities.shifted_identities", SEVEN_AXIOMS,
                          "Checks.ShiftedIdentities.shifted_identities")
SHIFTED_REPORTS = [
    ("Checks.ShiftedDefinitions.family_sequence_limit_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.family_sequence_limit_characterization"),
    ("Checks.ShiftedDefinitions.coordinate_support_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.coordinate_support_characterization"),
    ("Checks.ShiftedDefinitions.quadric_eval_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.quadric_eval_characterization"),
    ("Checks.ShiftedDefinitions.tuple_map_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.tuple_map_characterization"),
    ("Checks.ShiftedDefinitions.mixture_weights_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.mixture_weights_characterization"),
    ("Checks.ShiftedDefinitions.mixture_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.mixture_characterization"),
    ("Checks.ShiftedDefinitions.cmixture_weights_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.cmixture_weights_characterization"),
    ("Checks.ShiftedDefinitions.cmixture_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.cmixture_characterization"),
    ("Checks.ShiftedDefinitions.row_symmetric_law_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.row_symmetric_law_characterization"),
    ("Checks.ShiftedDefinitions.row_shift_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.row_shift_characterization"),
    ("Checks.ShiftedDefinitions.row_shift_law_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.row_shift_law_characterization"),
    ("Checks.ShiftedDefinitions.sign_shift_weights_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.sign_shift_weights_characterization"),
    ("Checks.ShiftedDefinitions.sign_shift_law_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.sign_shift_law_characterization"),
    ("Checks.ShiftedDefinitions.row_outer_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.row_outer_characterization"),
    ("Checks.ShiftedDefinitions.row_of_tuple_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.row_of_tuple_characterization"),
    ("Checks.ShiftedDefinitions.point_law_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.point_law_characterization"),
    ("Checks.ShiftedDefinitions.sample_row_tuple_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.sample_row_tuple_characterization"),
    ("Checks.ShiftedDefinitions.sample_flat_row_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.sample_flat_row_characterization"),
    ("Checks.ShiftedDefinitions.sample_flat_col_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.sample_flat_col_characterization"),
    ("Checks.ShiftedDefinitions.sample_of_row_tuple_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.sample_of_row_tuple_characterization"),
    ("Checks.ShiftedDefinitions.sample_translate_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.sample_translate_characterization"),
    ("Checks.ShiftedDefinitions.translation_fitting_error_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.translation_fitting_error_characterization"),
    ("Checks.ShiftedDefinitions.gaussian_small_shift_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.gaussian_small_shift_characterization"),
    ("Checks.ShiftedDefinitions.finite_row_law_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.finite_row_law_characterization"),
    ("Checks.ShiftedDefinitions.countable_row_law_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.countable_row_law_characterization"),
    ("Checks.ShiftedDefinitions.row_sample_map_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.row_sample_map_characterization"),
    ("Checks.ShiftedDefinitions.iid_row_sample_law_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.iid_row_sample_law_characterization"),
    ("Checks.ShiftedDefinitions.shifted_iid_sample_law_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.shifted_iid_sample_law_characterization"),
    ("Checks.ShiftedDefinitions.sign_mixture_sample_law_characterization", SEVEN_AXIOMS, "Checks.ShiftedDefinitions.sign_mixture_sample_law_characterization"),
]
CHECK_FILES = [
    CheckFile("check/ApplicationsDefinitions.v", LIB_CHECK_FLAGS,
              "build/checks/ApplicationsDefinitions.out", 1, ("empty",)),
    CheckFile("check/MatrixSigmaRing.v", LIB_CHECK_FLAGS,
              "build/checks/MatrixSigmaRing.out", 1, ("empty",)),
    CheckFile("check/Phase13Definitions.v", LIB_CHECK_FLAGS,
              "build/checks/Phase13Definitions.out", 1, ("reports", 3, SEVEN_AXIOMS)),
    CheckFile("check/LibraryStatements.v", LIB_CHECK_FLAGS,
              "build/checks/LibraryStatements.out", 1, ("reports", 1, SEVEN_AXIOMS)),
    CheckFile("check/Phase14Definitions.v", LIB_CHECK_FLAGS,
              "build/checks/Phase14Definitions.out", 1, ("reports", 1, SEVEN_AXIOMS)),
    CheckFile("check/Phase14Statements.v", LIB_CHECK_FLAGS,
              "build/checks/Phase14Statements.out", 1, ("reports", 1, SEVEN_AXIOMS)),
    CheckFile("check/ShiftedDefinitions.v", ALL_CHECK_FLAGS,
              "build/checks/ShiftedDefinitions.out", 1, ("reports", 1, SEVEN_AXIOMS)),
    CheckFile("check/Assumptions.v", PAPER_CHECK_FLAGS, "build/checks/Assumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["main theorem"], "main theorem")])),
    CheckFile("check/UniversalityAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/UniversalityAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["universality theorem"], "universality theorem")])),
    CheckFile("check/MixtureAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/MixtureAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["mixture theorem"], "mixture theorem")])),
    CheckFile("check/PairedAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/PairedAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["paired theorem"], "paired theorem")])),
    CheckFile("check/LatentSignAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/LatentSignAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["latent-sign theorem"], "latent-sign theorem")])),
    CheckFile("check/CountableAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/CountableAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["countable-mixture theorem"], "countable-mixture theorem")])),
    CheckFile("check/ConditionAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ConditionAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["condition-number theorem"], "condition-number theorem")])),
    CheckFile("check/LatentScopeAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/LatentScopeAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["latent-sign scope theorem"], "latent-sign scope theorem")])),
    CheckFile("check/RobustAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/RobustAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["robustness theorem"], "robustness theorem")])),
    CheckFile("check/LatentTensorAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/LatentTensorAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["tensorization theorem"], "tensorization theorem")])),
    CheckFile("check/ContinuousLatentAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ContinuousLatentAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["continuous-latent theorem"], "continuous-latent theorem")])),
    CheckFile("check/ConditionEndpointsAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ConditionEndpointsAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["condition-endpoints theorem"], "condition-endpoints theorem")])),
    CheckFile("check/ConditionRobustAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ConditionRobustAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["robust condition-number theorem"], "robust condition-number theorem")])),
    CheckFile("check/LatentTensorUpperAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/LatentTensorUpperAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["tensorization upper bound"], "tensorization upper bound")])),
    CheckFile("check/ConditionKappaCurveAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ConditionKappaCurveAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["condition-number curve at kappa"], "condition-number curve at kappa")])),
    CheckFile("check/ConditionKappaAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ConditionKappaAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["condition-number theorem at kappa"], "condition-number theorem at kappa")])),
    CheckFile("check/ConditionKappaRobustAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ConditionKappaRobustAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["robust condition-number theorem at kappa"], "robust condition-number theorem at kappa")])),
    CheckFile("check/MatrixSeriesAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/MatrixSeriesAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["Gaussian matrix series theorem"], "Gaussian matrix series theorem")])),
    CheckFile("check/TensorPackingAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/TensorPackingAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["tensor packing theorem"], "tensor packing theorem")])),
    CheckFile("check/GoeEdgeAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/GoeEdgeAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["GOE edge theorem"], "GOE edge theorem")])),
    CheckFile("check/SKGapAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/SKGapAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["SK spectral gap theorem"], "SK spectral gap theorem")])),
    CheckFile("check/PsdSplittingAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/PsdSplittingAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["orthogonal splitting theorem"], "orthogonal splitting theorem")])),
    CheckFile("check/PerceptronSignAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/PerceptronSignAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["perceptron comparison theorem"], "perceptron comparison theorem")])),
    CheckFile("check/SatVarianceAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/SatVarianceAssumptions.out", 1,
              ("marked", [(None, EXPECTED_LISTS["k-SAT variance theorem"], "k-SAT variance theorem")])),
    CheckFile("check/SatThresholdAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/SatThresholdAssumptions.out", 1,
              ("marked", [("Checks.SatThresholdAssumptions.sat_threshold_identity", EXPECTED_LISTS["satisfiability threshold theorem"], "satisfiability threshold theorem")])),
    CheckFile("check/PsdNormalizationAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/PsdNormalizationAssumptions.out", 1,
              ("marked", [("Checks.PsdNormalizationAssumptions.psd_normalization_identity", EXPECTED_LISTS["PSD normalization theorem"], "PSD normalization theorem")])),
    CheckFile("check/ProductSmoothingAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/ProductSmoothingAssumptions.out", 1,
              ("marked", [("Checks.ProductSmoothingAssumptions.product_smoothing_identity", EXPECTED_LISTS["product smoothing theorem"], "product smoothing theorem")])),
    CheckFile("check/MinSuperadditiveAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/MinSuperadditiveAssumptions.out", 1,
              ("marked", [("Checks.MinSuperadditiveAssumptions.min_superadditive_identity", EXPECTED_LISTS["min-superadditive convergence theorem"], "min-superadditive convergence theorem")])),
    CheckFile("check/PsdRankAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/PsdRankAssumptions.out", 1,
              ("marked", [("Checks.PsdRankAssumptions.psd_rank_identity", EXPECTED_LISTS["PSD rank theorem"], "PSD rank theorem")])),
    CheckFile("check/PsdLiftAssumptions.v", APPLICATION_CHECK_FLAGS, "build/checks/PsdLiftAssumptions.out", 1,
              ("marked", [("Checks.PsdLiftAssumptions.psd_lift_identity", EXPECTED_LISTS["PSD lift corollary"], "PSD lift corollary")])),
    CheckFile("check/ShiftedConditionAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ShiftedConditionAssumptions.out", 1,
              ("marked", [("Checks.ShiftedConditionAssumptions.shifted_condition_identity", EXPECTED_LISTS["shifted condition theorem"], "shifted condition theorem")])),
    CheckFile("check/ShiftedGaussianAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ShiftedGaussianAssumptions.out", 1,
              ("marked", [("Checks.ShiftedGaussianAssumptions.shifted_gaussian_identity", EXPECTED_LISTS["shifted Gaussian theorem"], "shifted Gaussian theorem")])),
    CheckFile("check/ShiftedQuadricAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ShiftedQuadricAssumptions.out", 1,
              ("marked", [("Checks.ShiftedQuadricAssumptions.shifted_quadric_identity", EXPECTED_LISTS["shifted quadric theorem"], "shifted quadric theorem")])),
    CheckFile("check/ShiftedErrorAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ShiftedErrorAssumptions.out", 1,
              ("marked", [("Checks.ShiftedErrorAssumptions.shifted_error_identity", EXPECTED_LISTS["shifted error theorem"], "shifted error theorem")])),
    CheckFile("check/ShiftedMixtureUnsatAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ShiftedMixtureUnsatAssumptions.out", 1,
              ("marked", [("Checks.ShiftedMixtureUnsatAssumptions.shifted_mixture_unsat_identity", EXPECTED_LISTS["shifted mixture nonexistence theorem"], "shifted mixture nonexistence theorem")])),
    CheckFile("check/ShiftedMixtureSatAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ShiftedMixtureSatAssumptions.out", 1,
              ("marked", [("Checks.ShiftedMixtureSatAssumptions.shifted_mixture_sat_identity", EXPECTED_LISTS["shifted mixture existence theorem"], "shifted mixture existence theorem")])),
    CheckFile("check/ShiftedSignAssumptions.v", EXTENSION_CHECK_FLAGS, "build/checks/ShiftedSignAssumptions.out", 1,
              ("marked", [("Checks.ShiftedSignAssumptions.shifted_sign_identity", EXPECTED_LISTS["shifted sign theorem"], "shifted sign theorem")])),
    CheckFile("check/TheoremIdentities.v", ALL_CHECK_FLAGS,
              "build/checks/TheoremIdentities.out", 1, ("marked", THEOREM_IDENTITIES)),
    CheckFile("check/Phase14Identities.v", ALL_CHECK_FLAGS,
              "build/checks/Phase14Identities.out", 1, ("marked", PHASE14_IDENTITIES)),
    CheckFile("check/ShiftedIdentities.v", ALL_CHECK_FLAGS, "build/checks/ShiftedIdentities.out", 1,
              ("marked", SHIFTED_IDENTITIES + [SHIFTED_JOINT_IDENTITY])),
    CheckFile("check/Reports.v", LIB_CHECK_FLAGS, "build/checks/Reports.out", 2,
              ("marked", MARKED_REPORTS)),
    CheckFile("check/Phase14Reports.v", LIB_CHECK_FLAGS, "build/checks/Phase14Reports.out", 2,
              ("marked", PHASE14_REPORTS)),
    CheckFile("check/ShiftedReports.v", EXTENSION_CHECK_FLAGS, "build/checks/ShiftedReports.out", 2,
              ("marked", SHIFTED_REPORTS)),
    CheckFile("check/snapshots/SnapshotApplicationsDefinitions.v", ALL_CHECK_FLAGS, "build/checks/SnapshotApplicationsDefinitions.out", 2,
              ("snapshot", "check/snapshots/SnapshotApplicationsDefinitions.txt",
               "a49e2f982ab315e9fb882ba4a570426837c943181761292e0519778b1c486b49")),
    CheckFile("check/snapshots/SnapshotMatrixSigmaRing.v", ALL_CHECK_FLAGS, "build/checks/SnapshotMatrixSigmaRing.out", 2,
              ("snapshot", "check/snapshots/SnapshotMatrixSigmaRing.txt",
               "12a4befb2cc46242ec9185482341765071a6950f19889ac633bbb8ad56a8467a")),
    CheckFile("check/snapshots/SnapshotPhase1.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase1.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase1.txt",
               "58c6d6f2ddf409319275a9fc499709317e4f472e2dad0fdba2812b9404424b7d")),
    CheckFile("check/snapshots/SnapshotPhase10.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase10.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase10.txt",
               "87dd3babad8f996192bb2c64b5b846cfcbb3471124f55834d042b5f925b877aa")),
    CheckFile("check/snapshots/SnapshotPhase11.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase11.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase11.txt",
               "fc54f0c72f0abe5fd353acbca1b2ffabfaf814e2ebf199ed274459c291045c8d")),
    CheckFile("check/snapshots/SnapshotPhase12Batch1.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase12Batch1.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase12Batch1.txt",
               "e89954a3dff1f2a66793bd58f26917b412c28d16b4461ecb12af84914ebd4d30")),
    CheckFile("check/snapshots/SnapshotPhase12Batch2.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase12Batch2.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase12Batch2.txt",
               "3e6646c9444f1ca8b32fd208d3281a1ba3190b5b949285eb05cc6a22ae610528")),
    CheckFile("check/snapshots/SnapshotPhase13.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase13.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase13.txt",
               "3ce0300d7bf9489448666d822b0ef813c7b8969a16788473852380afeeeed4f2")),
    CheckFile("check/snapshots/SnapshotPhase13Freeze1.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase13Freeze1.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase13Freeze1.txt",
               "98263a2d0d2f80d8d09d160c6932989e40c9c4a9e18b90dcb4728c818f325ade")),
    CheckFile("check/snapshots/SnapshotPhase13Freeze2.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase13Freeze2.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase13Freeze2.txt",
               "b9557b735a093fa58442bf1de97c1e880fc9cbfb96c66fce53b58e6333afdb0d")),
    CheckFile("check/snapshots/SnapshotPhase13Freeze3.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase13Freeze3.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase13Freeze3.txt",
               "2e416b6067853b04def20fb4445600cd6295c1f276c49be26af648dc9ff46584")),
    CheckFile("check/snapshots/SnapshotPhase14.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase14.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase14.txt",
               "8f8ada537ed08545c3ae55bee6aa22beb85bfa1606c38ecbc1ce98d3c7bf71b9")),
    CheckFile("check/snapshots/SnapshotPhase14Definitions.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase14Definitions.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase14Definitions.txt",
               "0c9f8d4fe5d7868db5316769a8e7831dbb984629b4bf48d45a9d586945f88ce1")),
    CheckFile("check/snapshots/SnapshotPhase14Statements.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase14Statements.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase14Statements.txt",
               "48797bba7ec7ed1d935bf8e4f6cd81a18c0d25889e288928622e6575cd7dd8e3")),
    CheckFile("check/snapshots/SnapshotShifted.v", ALL_CHECK_FLAGS, "build/checks/SnapshotShifted.out", 2,
              ("snapshot", "check/snapshots/SnapshotShifted.txt",
               "ffac6279e722c4108e638569d938645f283a6727cc677451d6f8216b1eb3068a")),
    CheckFile("check/snapshots/SnapshotShiftedDefinitions.v", ALL_CHECK_FLAGS, "build/checks/SnapshotShiftedDefinitions.out", 2,
              ("snapshot", "check/snapshots/SnapshotShiftedDefinitions.txt",
               "078194b172c277c7e8319208136cd8b3fb6ec0d3ce508d9b2a56f339fc8ec745")),
    CheckFile("check/snapshots/SnapshotPhase1Theorems.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase1Theorems.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase1Theorems.txt",
               "c3a56779f6550c334a007c3c164129b4c9aebb332a7a0825f02d2ce9ba35a444")),
    CheckFile("check/snapshots/SnapshotPhase5.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase5.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase5.txt",
               "21052c338dbf3e5bf062992d50ffe6830cf556db94b12906814874969bb98972")),
    CheckFile("check/snapshots/SnapshotPhase6.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase6.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase6.txt",
               "7f9b2627834ceff603c268f33fcd8d3ad779b5025271bb686110c01808b10617")),
    CheckFile("check/snapshots/SnapshotPhase7.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase7.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase7.txt",
               "033dc24da294a4b36dec738207f4292d3b6d718e3328925f69df5f489898c580")),
    CheckFile("check/snapshots/SnapshotPhase8.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase8.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase8.txt",
               "de5980786ab6ab0072546565d5d89623c5c8e1725d3f70fa00cb345934b4260b")),
    CheckFile("check/snapshots/SnapshotPhase9.v", ALL_CHECK_FLAGS, "build/checks/SnapshotPhase9.out", 2,
              ("snapshot", "check/snapshots/SnapshotPhase9.txt",
               "9b3ad498de48743b32c2eaeff613507b36dc5ff11a63127b76710cfc230f4aea")),
    CheckFile("check/snapshots/SnapshotTupleProd.v", ALL_CHECK_FLAGS, "build/checks/SnapshotTupleProd.out", 2,
              ("snapshot", "check/snapshots/SnapshotTupleProd.txt",
               "b4cb555fb7227baa39700d072f9888d02d8908f3dee4cd4fed078ecd346fb039")),
]
# Rule 30 (e): the identity drivers of the snapshots that print a
# declaration, and the SHA-256 of their references.
IDENTITY_INVENTORY = "check/identity/inventory.json"
IDENTITY_META = "check/identity/REFERENCES.json"
IDENTITY_QUERIES = 494
IDENTITY_PARTS = 751
OCAML_VERSION = "5.3.0"
FINDLIB_VERSION = "1.9.8"
IDENTITY_REFERENCES = {'SnapshotApplicationsDefinitions': 'f7a833bf5ce806aa52cc3ec5253209cf025d111033c06051adf709b74cd34100', 'SnapshotMatrixSigmaRing': '3d8e3e9761c9d2995833406821faecdabebe4330a1dd1e2094bff0ab367b6c10', 'SnapshotPhase1': 'a303085aa9e270242a1cdb03ab9c64524dcc6af766745b7291030acbc59b1e1e', 'SnapshotPhase10': 'bc5aa8533d8bc6f6f7b17a127bb75471c9908583123ca7e0f5e4292c0eb1a31c', 'SnapshotPhase11': 'a76aa824b4b56515bbf4ebf6099d9dbd00c83a7b9b864135ef7e8114249e1463', 'SnapshotPhase12Batch1': '4a238335bae99e561dedb781d04e578231e478ab77c07142130a1f2769ad2126', 'SnapshotPhase12Batch2': 'c377fcd42ed952d95d47ac7670e901350c5912894795c846e296b8e61b3dd2d3', 'SnapshotPhase13': 'f8af26f895707a1910d5745be9a673ee0f5387c629e6f493cab876c2302fb2d7', 'SnapshotPhase13Freeze1': 'c9e5aa896927b557fea9ff700b4d078b0c0811323437bb10692b231f873f710f', 'SnapshotPhase13Freeze2': 'e1fa6fc56442e2a35e6206454a60a32d1f8ac8fe747848c700114bd58920e51d', 'SnapshotPhase13Freeze3': '011b8682d1335c45e34262910fd39b098612041df1f7ddbdb6a5fb2f4810a627', 'SnapshotPhase14': 'a6dbe585d3d4d8e977ee54361235f3df61239e3cf298ed389392b5645bd897f3', 'SnapshotPhase14Definitions': '4d3bd64b07280d307609e69c44ffec5a55a0b9d10ca903ed57c889c62aeace4e', 'SnapshotPhase14Statements': '1f9802222e56696ac1623ef17db51ed18fccae4839d322e421e61db16fa7545c', 'SnapshotPhase1Theorems': 'e4f63bab1dc796b4da7c1ce7b3722c4c636124573d6d45723beadc7ddf9b9b80', 'SnapshotPhase5': '16bee76d38cfd63468d126a397e1e37ffa02df2714e6c7c49c6595eaebedb1bf', 'SnapshotPhase6': 'a19527f75fa5fdeced6244bbbde6f28bf43c7f898f7a7bc63174fd5e395cc78b', 'SnapshotPhase7': '6658ee672f2736ebe13d8316d509dd6e6fb87c164d02ebbfe14c91fbfa35bcf8', 'SnapshotPhase8': '625f21020e8f382a0494039f06efc4f56825fa64738bf2c3f8857d206d2cb1e9', 'SnapshotPhase9': 'fbf85e3917cb1a94548c67ff090be950b627a0adc37acc446a37695b49aa101b', 'SnapshotShifted': '7c4f885d8d76280ba8d1495b08caa2c50927f5f0278fd330cb18448c53c8e886', 'SnapshotShiftedDefinitions': 'f282c08ee89e02b58c397cb8e696aa0ab30429e6dded38228665f480a85a6e47', 'SnapshotTupleProd': 'dee8f3e84871f77ce10663e2dfca87480f93c2f74c1e89004bd00bb4c444f479'}
CHECK_FILES += [CheckFile(f"check/identity/Identity{name}.v", ALL_CHECK_FLAGS,
                          f"build/checks/Identity{name}.out", 2,
                          ("identity", f"check/identity/Identity{name}.json", digest))
                for name, digest in IDENTITY_REFERENCES.items()]
MANIFEST = "build/checks/manifest.json"
REFERENCES = "check/snapshots/REFERENCES.json"
# The snapshots of characterization lemmas, the other snapshots being those
# of frozen statements, pinned sections and accepted statements.
CHARACTERIZATION_SNAPSHOTS = ["SnapshotApplicationsDefinitions", "SnapshotMatrixSigmaRing",
                              "SnapshotPhase13Freeze1", "SnapshotPhase13Freeze2",
                              "SnapshotPhase13Freeze3", "SnapshotPhase14Definitions",
                              "SnapshotShiftedDefinitions"]
# The names that each snapshot file prints by its own commands.
SNAPSHOT_SUBJECTS = {'SnapshotAcceptedStatements': ['GaussianAnalysis.combinatorics.binomial_bounds.bin_near_half_statement', 'GaussianAnalysis.combinatorics.binomial_bounds.bin_partial_sum_statement', 'GaussianAnalysis.combinatorics.binomial_bounds.bin_sqr_central_statement', 'GaussianAnalysis.combinatorics.binomial_bounds.bin_sqr_ratio_statement', 'GaussianAnalysis.combinatorics.binomial_bounds.central_bin_ge_statement', 'GaussianAnalysis.combinatorics.binomial_bounds.central_bin_le_statement', 'GaussianAnalysis.combinatorics.binomial_bounds.half_bin_ge_statement', 'GaussianAnalysis.combinatorics.binomial_bounds.leq_bin_half_statement', 'GaussianAnalysis.fourier.boolean_fourier.bchar_algebra_statement', 'GaussianAnalysis.fourier.boolean_fourier.bchar_col_mx_statement', 'GaussianAnalysis.fourier.boolean_fourier.bchar_delta_statement', 'GaussianAnalysis.fourier.boolean_fourier.bchar_orthogonal_statement', 'GaussianAnalysis.fourier.boolean_fourier.blk_col_mx_statement', 'GaussianAnalysis.fourier.boolean_fourier.blk_dist_metric_statement', 'GaussianAnalysis.fourier.boolean_fourier.blk_dist_row_statement', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_col_mx_statement', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_comp_linear_statement', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_expansion_statement', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_inversion_statement', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_linear_statement', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_mulmx_statement', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_norm_le_statement', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_plancherel_statement', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_translate_statement', 'GaussianAnalysis.fourier.boolean_fourier.low_blk_deg_expansion_statement', 'GaussianAnalysis.fourier.boolean_fourier.low_blk_deg_translate_statement', 'GaussianAnalysis.matrix.psd_duality.psd_eval_cone_closed_statement', 'GaussianAnalysis.matrix.psd_duality.psd_farkas_statement', 'GaussianAnalysis.matrix.psd_duality.psd_slack_certificate_affine_statement', 'GaussianAnalysis.matrix.psd_duality.psd_slack_certificate_statement', 'GaussianAnalysis.matrix.psd_duality.psdmx_dual_statement', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_ge0_statement', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_nonneg_statement', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_restrict_statement', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_shift_statement', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_size_gt0_statement', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_widen_statement', 'GaussianAnalysis.probability.binomial_mean.binomial_chebyshev_statement', 'GaussianAnalysis.probability.binomial_mean.binomial_mean0_statement', 'GaussianAnalysis.probability.binomial_mean.binomial_meanD_statement', 'GaussianAnalysis.probability.binomial_mean.binomial_meanE_statement', 'GaussianAnalysis.probability.binomial_mean.binomial_meanS_statement', 'GaussianAnalysis.probability.binomial_mean.binomial_meanZ_statement', 'GaussianAnalysis.probability.binomial_mean.binomial_mean_cst_statement', 'GaussianAnalysis.probability.binomial_mean.binomial_mean_id_statement', 'GaussianAnalysis.probability.binomial_mean.binomial_mean_last_statement', 'GaussianAnalysis.probability.binomial_mean.binomial_mean_sqr_dev_statement', 'GaussianAnalysis.probability.binomial_mean.binomial_mean_trials_statement', 'GaussianAnalysis.probability.binomial_mean.eq_binomial_mean_statement', 'GaussianAnalysis.probability.binomial_mean.integral_binomial_mean_statement', 'GaussianAnalysis.probability.binomial_mean.ler_binomial_mean_statement', 'GaussianAnalysis.probability.binomial_mean.unif_mean_binomial_mean_statement', 'GaussianAnalysis.probability.commuting_operators.binomial_mix_le_iter_statement', 'GaussianAnalysis.probability.commuting_operators.homo_iter_statement', 'GaussianAnalysis.probability.commuting_operators.iter_le_subcomm_statement', 'GaussianAnalysis.probability.commuting_operators.iter_meet_avg_statement', 'GaussianAnalysis.probability.commuting_operators.iter_mix_binomial_statement', 'GaussianAnalysis.probability.commuting_operators.iter_scale_statement', 'GaussianAnalysis.probability.commuting_operators.meet_avgC_statement', 'GaussianAnalysis.probability.commuting_operators.meet_avg_cst_statement', 'GaussianAnalysis.probability.commuting_operators.meet_avg_linear_statement', 'GaussianAnalysis.probability.commuting_operators.meet_avg_monotone_statement', 'GaussianAnalysis.probability.commuting_operators.monotone_iter_le_statement', 'GaussianAnalysis.probability.finite_mean.unif_chebyshev_statement', 'GaussianAnalysis.probability.finite_mean.unif_mean_cutoff_statement', 'GaussianAnalysis.probability.finite_mean.unif_mean_indicatorN_statement', 'GaussianAnalysis.probability.finite_mean.unif_mean_markov_statement', 'GaussianAnalysis.probability.finite_mean.unif_mean_tuple_prod_ord_statement', 'GaussianAnalysis.probability.finite_mean.unif_mean_tuple_prod_set_statement', 'GaussianAnalysis.probability.finite_mean.unif_mean_union_statement'], 'SnapshotAcceptedStatements14': ['GaussianAnalysis.combinatorics.binomial_bounds.bin_mul_pow_statement', 'GaussianAnalysis.combinatorics.expander.expander_statement', 'GaussianAnalysis.combinatorics.harmonic.harmonic_ln_statement', 'GaussianAnalysis.matrix.multiplicity.ksubset_multiplicity_statement', 'GaussianAnalysis.matrix.multiplicity.trace_multiplicity_statement'], 'SnapshotApplicationsDefinitions': ['Checks.ApplicationsDefinitions.frobenius_characterization', 'Checks.ApplicationsDefinitions.gauss_characterization', 'Checks.ApplicationsDefinitions.gauss_determined', 'Checks.ApplicationsDefinitions.goe_mx_characterization', 'Checks.ApplicationsDefinitions.matrix_measurable_characterization', 'Checks.ApplicationsDefinitions.mxdot_characterization', 'Checks.ApplicationsDefinitions.opnorm_characterization', 'Checks.ApplicationsDefinitions.psdmx_characterization'], 'SnapshotMatrixSigmaRing': ['Checks.MatrixSigmaRing.matrix_sigma_ring_characterization'], 'SnapshotPhase1': ['EllipsoidFitting.AnalysisIntegralDefinitions.continuity_2d_pt', 'EllipsoidFitting.AnalysisIntegralDefinitions.oriented_has_integral', 'EllipsoidFitting.AnalysisIntegralDefinitions.oriented_integral', 'EllipsoidFitting.AnalysisIntegralDefinitions.segment_integrable', 'EllipsoidFitting.AnalysisIntegralDefinitions.whole_line_has_integral', 'EllipsoidFitting.AnalysisIntegralDefinitions.whole_line_integrable', 'EllipsoidFitting.AnalysisIntegralDefinitions.whole_line_integral', 'EllipsoidFitting.GaussianDefinitions.gaussian_absolutely_integrable', 'EllipsoidFitting.GaussianDefinitions.gaussian_density', 'EllipsoidFitting.GaussianDefinitions.gaussian_expectation', 'EllipsoidFitting.GaussianDefinitions.gaussian_has_integral', 'EllipsoidFitting.GaussianDefinitions.gaussian_integral', 'EllipsoidFitting.GaussianDefinitions.gaussian_integral_exists', 'EllipsoidFitting.GaussianDefinitions.gaussian_kernel', 'EllipsoidFitting.GaussianDefinitions.gaussian_mass', 'EllipsoidFitting.GaussianDefinitions.gaussian_primitive', 'EllipsoidFitting.GaussianDefinitions.gaussian_stein_integrand', 'EllipsoidFitting.GaussianDefinitions.moment_factor', 'EllipsoidFitting.GaussianProbabilityDefinitions.gaussian_law', 'EllipsoidFitting.GaussianProbabilityDefinitions.gaussian_law_density', 'EllipsoidFitting.GaussianProbabilityDefinitions.gaussian_law_expectation', 'EllipsoidFitting.GaussianProbabilityDefinitions.gaussian_law_integrable', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.GaussianProbabilityProductDefinitions_gaussian_cons_tuple__canonical__measurable_function_MeasurableFun', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.HB_unnamed_factory_1', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.HB_unnamed_factory_7', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_cons_tuple', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_cons_tuple_measurable', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_law_probability', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_pair_probability', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_pair_probability_setT_subproof', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.gaussian_product_law', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.probability_measure_Measure_isProbability__to__measure_function_isFinite', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.probability_measure_Measure_isProbability__to__measure_function_isSFinite', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.probability_measure_Measure_isProbability__to__measure_function_isSigmaFinite', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.probability_measure_Measure_isProbability__to__probability_measure_isProbability', 'EllipsoidFitting.GaussianProbabilityProductDefinitions.probability_measure_Measure_isProbability__to__probability_measure_isSubProbability', 'EllipsoidFitting.MainStatement.main_statement', 'EllipsoidFitting.PaperMainDefinitions.paper_main_balanced_pd_event', 'EllipsoidFitting.PaperMainDefinitions.paper_main_conditioned_event', 'EllipsoidFitting.PaperMainDefinitions.paper_main_density', 'EllipsoidFitting.PaperMainDefinitions.paper_main_eventually_ge', 'EllipsoidFitting.PaperMainDefinitions.paper_main_eventually_le', 'EllipsoidFitting.PaperMainDefinitions.paper_main_fit_event', 'EllipsoidFitting.PaperMainDefinitions.paper_main_liminf_gt', 'EllipsoidFitting.PaperMainDefinitions.paper_main_limsup_le', 'EllipsoidFitting.PaperMainDefinitions.paper_main_limsup_lt', 'EllipsoidFitting.PaperMainDefinitions.paper_main_loewner_le', 'EllipsoidFitting.PaperMainDefinitions.paper_main_pd', 'EllipsoidFitting.PaperMainDefinitions.paper_main_point', 'EllipsoidFitting.PaperMainDefinitions.paper_main_probability', 'EllipsoidFitting.PaperMainDefinitions.paper_main_psd', 'EllipsoidFitting.PaperMainDefinitions.paper_main_quadratic_form', 'EllipsoidFitting.PaperMainDefinitions.paper_main_symmetric', 'EllipsoidFitting.PaperMainDefinitions.paper_main_tends_to', 'EllipsoidFitting.PaperMainDefinitions.paper_main_trace'], 'SnapshotPhase10': ['EllipsoidUniversality.ConditionRobustStatement.robust_condition_number_statement', 'EllipsoidUniversality.ConditionRobustStatement.robust_condition_statement', 'EllipsoidUniversality.ConditionRobustStatement.robust_condition_theorem_statement', 'EllipsoidUniversality.LatentTensorUpper.latent_tensor_constant', 'EllipsoidUniversality.LatentTensorUpper.latent_tensor_upper_statement'], 'SnapshotPhase11': ['EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_curve_statement', 'EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_integral', 'EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_inverse', 'EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_range', 'EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_root', 'EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_three', 'EllipsoidUniversality.ConditionKappaCurveStatement.condition_kappa_variational', 'EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_F', 'EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_J', 'EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_L', 'EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_alpha', 'EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_ell', 'EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_objective', 'EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_profile', 'EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_star', 'EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_u', 'EllipsoidUniversality.ConditionKappaDefinitions.condition_kappa_value', 'EllipsoidUniversality.ConditionKappaRobustStatement.condition_kappa_robust_theorem_statement', 'EllipsoidUniversality.ConditionKappaRobustStatement.finite_robust_condition_kappa_number_statement', 'EllipsoidUniversality.ConditionKappaRobustStatement.finite_robust_condition_kappa_statement', 'EllipsoidUniversality.ConditionKappaRobustStatement.robust_condition_kappa_number_statement', 'EllipsoidUniversality.ConditionKappaRobustStatement.robust_condition_kappa_statement', 'EllipsoidUniversality.ConditionKappaStatement.condition_kappa_number_statement', 'EllipsoidUniversality.ConditionKappaStatement.condition_kappa_statement', 'EllipsoidUniversality.ConditionKappaStatement.condition_kappa_theorem_statement', 'EllipsoidUniversality.ConditionKappaStatement.countable_condition_kappa_number_statement', 'EllipsoidUniversality.ConditionKappaStatement.countable_condition_kappa_statement'], 'SnapshotPhase12Batch1': ['GaussianAnalysis.matrix.lambda_max.lambda_max', 'GaussianApplications.GoeEdgeStatement.goe_edge_statement', 'GaussianApplications.MatrixSeriesStatement.matrix_series_statement', 'GaussianApplications.PsdSplittingStatement.psd_splitting_statement'], 'SnapshotPhase12Batch2': ['GaussianApplications.PerceptronSignDefinitions.bounded_C3', 'GaussianApplications.PerceptronSignDefinitions.gauss_pressure', 'GaussianApplications.PerceptronSignDefinitions.perceptron_pressure', 'GaussianApplications.PerceptronSignDefinitions.sign_pressure', 'GaussianApplications.PerceptronSignDefinitions.spin_col', 'GaussianApplications.PerceptronSignStatement.perceptron_sign_statement', 'GaussianApplications.SKGapDefinitions.half_diff', 'GaussianApplications.SKGapDefinitions.ising_cond_mean', 'GaussianApplications.SKGapDefinitions.ising_cond_var', 'GaussianApplications.SKGapDefinitions.ising_cov', 'GaussianApplications.SKGapDefinitions.ising_dirichlet', 'GaussianApplications.SKGapDefinitions.ising_mass', 'GaussianApplications.SKGapDefinitions.ising_mean', 'GaussianApplications.SKGapDefinitions.ising_var', 'GaussianApplications.SKGapDefinitions.ising_weight', 'GaussianApplications.SKGapDefinitions.sk_coupling', 'GaussianApplications.SKGapDefinitions.spin', 'GaussianApplications.SKGapDefinitions.spin_set', 'GaussianApplications.SKGapDefinitions.spin_vec', 'GaussianApplications.SKGapStatement.sk_gap_statement', 'GaussianApplications.SatVarianceDefinitions.clause', 'GaussianApplications.SatVarianceDefinitions.clause_sat', 'GaussianApplications.SatVarianceDefinitions.prefix_sat', 'GaussianApplications.SatVarianceDefinitions.proper_clause', 'GaussianApplications.SatVarianceDefinitions.sat_cap', 'GaussianApplications.SatVarianceDefinitions.sat_capped_var', 'GaussianApplications.SatVarianceDefinitions.sat_mean', 'GaussianApplications.SatVarianceDefinitions.sat_prefix_len', 'GaussianApplications.SatVarianceDefinitions.sat_var', 'GaussianApplications.SatVarianceStatement.sat_variance_statement', 'GaussianApplications.TensorPackingStatement.tensor_packing_statement'], 'SnapshotPhase13': ['Checks.LibraryStatements.accepted_binomial_bounds.bin_near_half_accepted', 'Checks.LibraryStatements.accepted_binomial_bounds.bin_partial_sum_accepted', 'Checks.LibraryStatements.accepted_binomial_bounds.bin_sqr_central_accepted', 'Checks.LibraryStatements.accepted_binomial_bounds.bin_sqr_ratio_accepted', 'Checks.LibraryStatements.accepted_binomial_bounds.central_bin_ge_accepted', 'Checks.LibraryStatements.accepted_binomial_bounds.central_bin_le_accepted', 'Checks.LibraryStatements.accepted_binomial_bounds.half_bin_ge_accepted', 'Checks.LibraryStatements.accepted_binomial_bounds.leq_bin_half_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.binomial_chebyshev_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.binomial_mean0_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.binomial_meanD_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.binomial_meanE_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.binomial_meanS_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.binomial_meanZ_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_cst_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_id_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_last_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_sqr_dev_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.binomial_mean_trials_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.eq_binomial_mean_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.integral_binomial_mean_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.ler_binomial_mean_accepted', 'Checks.LibraryStatements.accepted_binomial_mean.unif_mean_binomial_mean_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.bchar_algebra_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.bchar_col_mx_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.bchar_delta_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.bchar_orthogonal_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.blk_col_mx_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.blk_dist_metric_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.blk_dist_row_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.fcoef_col_mx_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.fcoef_comp_linear_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.fcoef_expansion_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.fcoef_inversion_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.fcoef_linear_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.fcoef_mulmx_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.fcoef_norm_le_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.fcoef_plancherel_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.fcoef_translate_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.low_blk_deg_expansion_accepted', 'Checks.LibraryStatements.accepted_boolean_fourier.low_blk_deg_translate_accepted', 'Checks.LibraryStatements.accepted_commuting_operators.binomial_mix_le_iter_accepted', 'Checks.LibraryStatements.accepted_commuting_operators.homo_iter_accepted', 'Checks.LibraryStatements.accepted_commuting_operators.iter_le_subcomm_accepted', 'Checks.LibraryStatements.accepted_commuting_operators.iter_meet_avg_accepted', 'Checks.LibraryStatements.accepted_commuting_operators.iter_mix_binomial_accepted', 'Checks.LibraryStatements.accepted_commuting_operators.iter_scale_accepted', 'Checks.LibraryStatements.accepted_commuting_operators.meet_avgC_accepted', 'Checks.LibraryStatements.accepted_commuting_operators.meet_avg_cst_accepted', 'Checks.LibraryStatements.accepted_commuting_operators.meet_avg_linear_accepted', 'Checks.LibraryStatements.accepted_commuting_operators.meet_avg_monotone_accepted', 'Checks.LibraryStatements.accepted_commuting_operators.monotone_iter_le_accepted', 'Checks.LibraryStatements.accepted_finite_mean.unif_chebyshev_accepted', 'Checks.LibraryStatements.accepted_finite_mean.unif_mean_cutoff_accepted', 'Checks.LibraryStatements.accepted_finite_mean.unif_mean_indicatorN_accepted', 'Checks.LibraryStatements.accepted_finite_mean.unif_mean_markov_accepted', 'Checks.LibraryStatements.accepted_finite_mean.unif_mean_tuple_prod_ord_accepted', 'Checks.LibraryStatements.accepted_finite_mean.unif_mean_tuple_prod_set_accepted', 'Checks.LibraryStatements.accepted_finite_mean.unif_mean_union_accepted', 'Checks.LibraryStatements.accepted_psd_duality.psd_eval_cone_closed_accepted', 'Checks.LibraryStatements.accepted_psd_duality.psd_farkas_accepted', 'Checks.LibraryStatements.accepted_psd_duality.psd_slack_certificate_accepted', 'Checks.LibraryStatements.accepted_psd_duality.psd_slack_certificate_affine_accepted', 'Checks.LibraryStatements.accepted_psd_duality.psdmx_dual_accepted', 'Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_ge0_accepted', 'Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_nonneg_accepted', 'Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_restrict_accepted', 'Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_shift_accepted', 'Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_size_gt0_accepted', 'Checks.LibraryStatements.accepted_psd_factorization.psd_factorization_widen_accepted', 'GaussianAnalysis.combinatorics.binomial_bounds.bin_near_half', 'GaussianAnalysis.combinatorics.binomial_bounds.bin_partial_sum', 'GaussianAnalysis.combinatorics.binomial_bounds.bin_sqr_central', 'GaussianAnalysis.combinatorics.binomial_bounds.bin_sqr_ratio', 'GaussianAnalysis.combinatorics.binomial_bounds.central_bin_ge', 'GaussianAnalysis.combinatorics.binomial_bounds.central_bin_le', 'GaussianAnalysis.combinatorics.binomial_bounds.half_bin_ge', 'GaussianAnalysis.combinatorics.binomial_bounds.leq_bin_half', 'GaussianAnalysis.fourier.boolean_fourier.bchar_algebra', 'GaussianAnalysis.fourier.boolean_fourier.bchar_col_mx', 'GaussianAnalysis.fourier.boolean_fourier.bchar_delta', 'GaussianAnalysis.fourier.boolean_fourier.bchar_orthogonal', 'GaussianAnalysis.fourier.boolean_fourier.blk_col_mx', 'GaussianAnalysis.fourier.boolean_fourier.blk_dist_metric', 'GaussianAnalysis.fourier.boolean_fourier.blk_dist_row', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_col_mx', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_comp_linear', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_expansion', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_inversion', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_linear', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_mulmx', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_norm_le', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_plancherel', 'GaussianAnalysis.fourier.boolean_fourier.fcoef_translate', 'GaussianAnalysis.fourier.boolean_fourier.low_blk_deg_expansion', 'GaussianAnalysis.fourier.boolean_fourier.low_blk_deg_translate', 'GaussianAnalysis.matrix.psd_duality.psd_eval_cone_closed', 'GaussianAnalysis.matrix.psd_duality.psd_farkas', 'GaussianAnalysis.matrix.psd_duality.psd_slack_certificate', 'GaussianAnalysis.matrix.psd_duality.psd_slack_certificate_affine', 'GaussianAnalysis.matrix.psd_duality.psdmx_dual', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_ge0', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_nonneg', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_restrict', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_shift', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_size_gt0', 'GaussianAnalysis.matrix.psd_factorization.psd_factorization_widen', 'GaussianAnalysis.probability.binomial_mean.binomial_chebyshev', 'GaussianAnalysis.probability.binomial_mean.binomial_mean0', 'GaussianAnalysis.probability.binomial_mean.binomial_meanD', 'GaussianAnalysis.probability.binomial_mean.binomial_meanE', 'GaussianAnalysis.probability.binomial_mean.binomial_meanS', 'GaussianAnalysis.probability.binomial_mean.binomial_meanZ', 'GaussianAnalysis.probability.binomial_mean.binomial_mean_cst', 'GaussianAnalysis.probability.binomial_mean.binomial_mean_id', 'GaussianAnalysis.probability.binomial_mean.binomial_mean_last', 'GaussianAnalysis.probability.binomial_mean.binomial_mean_sqr_dev', 'GaussianAnalysis.probability.binomial_mean.binomial_mean_trials', 'GaussianAnalysis.probability.binomial_mean.eq_binomial_mean', 'GaussianAnalysis.probability.binomial_mean.integral_binomial_mean', 'GaussianAnalysis.probability.binomial_mean.ler_binomial_mean', 'GaussianAnalysis.probability.binomial_mean.unif_mean_binomial_mean', 'GaussianAnalysis.probability.commuting_operators.binomial_mix_le_iter', 'GaussianAnalysis.probability.commuting_operators.homo_iter', 'GaussianAnalysis.probability.commuting_operators.iter_le_subcomm', 'GaussianAnalysis.probability.commuting_operators.iter_meet_avg', 'GaussianAnalysis.probability.commuting_operators.iter_mix_binomial', 'GaussianAnalysis.probability.commuting_operators.iter_scale', 'GaussianAnalysis.probability.commuting_operators.meet_avgC', 'GaussianAnalysis.probability.commuting_operators.meet_avg_cst', 'GaussianAnalysis.probability.commuting_operators.meet_avg_linear', 'GaussianAnalysis.probability.commuting_operators.meet_avg_monotone', 'GaussianAnalysis.probability.commuting_operators.monotone_iter_le', 'GaussianAnalysis.probability.finite_mean.unif_chebyshev', 'GaussianAnalysis.probability.finite_mean.unif_mean_cutoff', 'GaussianAnalysis.probability.finite_mean.unif_mean_indicatorN', 'GaussianAnalysis.probability.finite_mean.unif_mean_markov', 'GaussianAnalysis.probability.finite_mean.unif_mean_tuple_prod_ord', 'GaussianAnalysis.probability.finite_mean.unif_mean_tuple_prod_set', 'GaussianAnalysis.probability.finite_mean.unif_mean_union', 'GaussianApplications.MinSuperadditiveStatement.min_superadditive_statement', 'GaussianApplications.ProductSmoothingStatement.product_smoothing_statement', 'GaussianApplications.PsdNormalizationStatement.psd_normalization_statement', 'GaussianApplications.PsdRankDefinitions.crossing', 'GaussianApplications.PsdRankDefinitions.edge_cut', 'GaussianApplications.PsdRankDefinitions.is_perfect_matching', 'GaussianApplications.PsdRankDefinitions.kn_edge', 'GaussianApplications.PsdRankDefinitions.odd_set', 'GaussianApplications.PsdRankDefinitions.perfect_matching', 'GaussianApplications.PsdRankDefinitions.shifted_matching_mx', 'GaussianApplications.PsdRankStatement.psd_rank_statement', 'GaussianApplications.SatThresholdDefinitions.sat_prob', 'GaussianApplications.SatThresholdStatement.sat_threshold_statement'], 'SnapshotPhase13Freeze1': ['Checks.Phase13Definitions.binomial_mean_characterization', 'Checks.Phase13Definitions.linear_op_characterization', 'Checks.Phase13Definitions.meet_avg_characterization', 'Checks.Phase13Definitions.monotone_op_characterization', 'Checks.Phase13Definitions.unif_mean_characterization', 'Checks.Phase13Definitions.unif_var_characterization'], 'SnapshotPhase13Freeze2': ['Checks.Phase13Definitions.bchar_characterization', 'Checks.Phase13Definitions.bdot_characterization', 'Checks.Phase13Definitions.binomial_mean_characterization', 'Checks.Phase13Definitions.blk_deg_characterization', 'Checks.Phase13Definitions.blk_dist_characterization', 'Checks.Phase13Definitions.fcoef_characterization', 'Checks.Phase13Definitions.linear_op_characterization', 'Checks.Phase13Definitions.low_blk_deg_characterization', 'Checks.Phase13Definitions.meet_avg_characterization', 'Checks.Phase13Definitions.monotone_op_characterization', 'Checks.Phase13Definitions.prob_vec_characterization', 'Checks.Phase13Definitions.prod_avg_characterization', 'Checks.Phase13Definitions.psd_factorization_characterization', 'Checks.Phase13Definitions.smoothing_hyps_characterization', 'Checks.Phase13Definitions.unif_mean_characterization', 'Checks.Phase13Definitions.unif_var_characterization', 'Checks.Phase13Definitions.weighted_gram_characterization'], 'SnapshotPhase13Freeze3': ['Checks.Phase13Definitions.bchar_characterization', 'Checks.Phase13Definitions.bdot_characterization', 'Checks.Phase13Definitions.binomial_mean_characterization', 'Checks.Phase13Definitions.blk_deg_characterization', 'Checks.Phase13Definitions.blk_dist_characterization', 'Checks.Phase13Definitions.fcoef_characterization', 'Checks.Phase13Definitions.linear_op_characterization', 'Checks.Phase13Definitions.low_blk_deg_characterization', 'Checks.Phase13Definitions.meet_avg_characterization', 'Checks.Phase13Definitions.monotone_op_characterization', 'Checks.Phase13Definitions.prob_vec_characterization', 'Checks.Phase13Definitions.prod_avg_characterization', 'Checks.Phase13Definitions.psd_eval_characterization', 'Checks.Phase13Definitions.psd_eval_cone_characterization', 'Checks.Phase13Definitions.psd_factorization_characterization', 'Checks.Phase13Definitions.smoothing_hyps_characterization', 'Checks.Phase13Definitions.unif_mean_characterization', 'Checks.Phase13Definitions.unif_var_characterization', 'Checks.Phase13Definitions.weighted_gram_characterization'], 'SnapshotPhase14': ['GaussianApplications.PsdLiftDefinitions.in_matching_polytope', 'GaussianApplications.PsdLiftDefinitions.kn_edges', 'GaussianApplications.PsdLiftDefinitions.matching_slack_mx', 'GaussianApplications.PsdLiftDefinitions.semidefinite_lift', 'GaussianApplications.PsdLiftStatement.psd_lift_statement'], 'SnapshotPhase14Definitions': ['Checks.Phase14Definitions.ksubset_characterization', 'Checks.Phase14Definitions.ksubset_mx_characterization', 'Checks.Phase14Definitions.perm_cut_characterization'], 'SnapshotPhase14Statements': ['Checks.Phase14Statements.accepted_binomial_bounds.bin_mul_pow_accepted', 'Checks.Phase14Statements.accepted_expander.expander_accepted', 'Checks.Phase14Statements.accepted_harmonic.harmonic_ln_accepted', 'Checks.Phase14Statements.accepted_multiplicity.ksubset_multiplicity_accepted', 'Checks.Phase14Statements.accepted_multiplicity.trace_multiplicity_accepted', 'GaussianAnalysis.combinatorics.binomial_bounds.bin_mul_pow', 'GaussianAnalysis.combinatorics.expander.expander', 'GaussianAnalysis.combinatorics.harmonic.harmonic_ln', 'GaussianAnalysis.matrix.multiplicity.ksubset_multiplicity', 'GaussianAnalysis.matrix.multiplicity.trace_multiplicity'], 'SnapshotPhase1Theorems': ['EllipsoidFitting.MainTheorem.ellipsoid_fitting_main', 'EllipsoidFitting.PaperMainResults.paper_main_results'], 'SnapshotPhase5': ['EllipsoidUniversality.UniversalityDefinitions.universality_alpha_star', 'EllipsoidUniversality.UniversalityDefinitions.universality_alpha_star_variational', 'EllipsoidUniversality.UniversalityDefinitions.universality_conditioned_fit_event', 'EllipsoidUniversality.UniversalityDefinitions.universality_coordinate_law', 'EllipsoidUniversality.UniversalityDefinitions.universality_cutoff', 'EllipsoidUniversality.UniversalityDefinitions.universality_density_tends_to', 'EllipsoidUniversality.UniversalityDefinitions.universality_e_star', 'EllipsoidUniversality.UniversalityDefinitions.universality_energy', 'EllipsoidUniversality.UniversalityDefinitions.universality_error_event', 'EllipsoidUniversality.UniversalityDefinitions.universality_fitting_error', 'EllipsoidUniversality.UniversalityDefinitions.universality_level_cutoff', 'EllipsoidUniversality.UniversalityDefinitions.universality_m', 'EllipsoidUniversality.UniversalityDefinitions.universality_pd_fit_event', 'EllipsoidUniversality.UniversalityDefinitions.universality_positive_part', 'EllipsoidUniversality.UniversalityDefinitions.universality_power', 'EllipsoidUniversality.UniversalityDefinitions.universality_probability', 'EllipsoidUniversality.UniversalityDefinitions.universality_product_law', 'EllipsoidUniversality.UniversalityDefinitions.universality_s', 'EllipsoidUniversality.UniversalityDefinitions.universality_sample_law', 'EllipsoidUniversality.UniversalityDefinitions.universality_semicircle_density', 'EllipsoidUniversality.UniversalityDefinitions.universality_semicircle_integrable', 'EllipsoidUniversality.UniversalityDefinitions.universality_semicircle_integral', 'EllipsoidUniversality.UniversalityDefinitions.universality_subgaussian_test', 'EllipsoidUniversality.UniversalityStatement.universality_statement'], 'SnapshotPhase6': ['EllipsoidUniversality.MixtureDefinitions.mixture_component_law', 'EllipsoidUniversality.MixtureDefinitions.mixture_family', 'EllipsoidUniversality.MixtureDefinitions.mixture_fourth_moment', 'EllipsoidUniversality.MixtureDefinitions.mixture_interpolation', 'EllipsoidUniversality.MixtureDefinitions.mixture_label', 'EllipsoidUniversality.MixtureDefinitions.mixture_labelled_law', 'EllipsoidUniversality.MixtureDefinitions.mixture_probability', 'EllipsoidUniversality.MixtureStatement.mixture_interpolation_statement', 'EllipsoidUniversality.MixtureStatement.mixture_statement', 'EllipsoidUniversality.MixtureStatement.mixture_theorem_statement', 'EllipsoidUniversality.PairedDefinitions.paired_kernel', 'EllipsoidUniversality.PairedDefinitions.paired_pair_density', 'EllipsoidUniversality.PairedDefinitions.paired_probability', 'EllipsoidUniversality.PairedDefinitions.paired_sample_density', 'EllipsoidUniversality.PairedDefinitions.paired_uniform_spec', 'EllipsoidUniversality.PairedStatement.paired_statement'], 'SnapshotPhase7': ['EllipsoidUniversality.LatentSignDefinitions.latent_probability', 'EllipsoidUniversality.LatentSignDefinitions.latent_sample_density', 'EllipsoidUniversality.LatentSignStatement.latent_sign_statement'], 'SnapshotPhase8': ['EllipsoidUniversality.ConditionDefinitions.condition_alpha', 'EllipsoidUniversality.ConditionDefinitions.condition_star', 'EllipsoidUniversality.ConditionDefinitions.condition_t', 'EllipsoidUniversality.ConditionDefinitions.data_condition_number', 'EllipsoidUniversality.ConditionStatement.condition_number_statement', 'EllipsoidUniversality.ConditionStatement.condition_statement', 'EllipsoidUniversality.ConditionStatement.condition_theorem_statement', 'EllipsoidUniversality.ConditionStatement.countable_condition_number_statement', 'EllipsoidUniversality.ConditionStatement.countable_condition_statement', 'EllipsoidUniversality.CountableMixtureDefinitions.countable_fourth_moment', 'EllipsoidUniversality.CountableMixtureDefinitions.countable_labelled_law', 'EllipsoidUniversality.CountableMixtureDefinitions.countable_mixture_family', 'EllipsoidUniversality.CountableMixtureDefinitions.countable_mixture_probability', 'EllipsoidUniversality.CountableMixtureStatement.countable_interpolation_statement', 'EllipsoidUniversality.CountableMixtureStatement.countable_mixture_statement', 'EllipsoidUniversality.CountableMixtureStatement.countable_theorem_statement', 'EllipsoidUniversality.LatentSignScope.latent_covariance_statement', 'EllipsoidUniversality.LatentSignScope.latent_point_expectation', 'EllipsoidUniversality.LatentSignScope.latent_scope_statement', 'EllipsoidUniversality.LatentSignScope.latent_variance_statement'], 'SnapshotPhase9': ['EllipsoidUniversality.ConditionEndpoints.condition_alpha_near_infinity', 'EllipsoidUniversality.ConditionEndpoints.condition_alpha_near_one', 'EllipsoidUniversality.ConditionEndpoints.condition_endpoints_statement', 'EllipsoidUniversality.ConditionEndpoints.condition_star_near_quarter', 'EllipsoidUniversality.ConditionEndpoints.condition_star_near_zero', 'EllipsoidUniversality.ContinuousLatent.cl_moment', 'EllipsoidUniversality.ContinuousLatent.cl_point_law', 'EllipsoidUniversality.ContinuousLatent.cl_value', 'EllipsoidUniversality.ContinuousLatent.cl_weight', 'EllipsoidUniversality.ContinuousLatent.continuous_latent_statement', 'EllipsoidUniversality.LatentTensorization.latent_cond_expectation', 'EllipsoidUniversality.LatentTensorization.latent_cond_variance', 'EllipsoidUniversality.LatentTensorization.latent_replace', 'EllipsoidUniversality.LatentTensorization.latent_tensorization', 'EllipsoidUniversality.LatentTensorization.latent_tensorization_statement', 'EllipsoidUniversality.LatentTensorization.latent_variance', 'EllipsoidUniversality.RobustDefinitions.contaminated_laws', 'EllipsoidUniversality.RobustDefinitions.contaminated_weights', 'EllipsoidUniversality.RobustDefinitions.finite_weights', 'EllipsoidUniversality.RobustDefinitions.robust_close', 'EllipsoidUniversality.RobustDefinitions.robust_point_law', 'EllipsoidUniversality.RobustDefinitions.robust_points', 'EllipsoidUniversality.RobustDefinitions.robust_sample_law', 'EllipsoidUniversality.RobustDefinitions.robust_tv', 'EllipsoidUniversality.RobustStatement.contamination_statement', 'EllipsoidUniversality.RobustStatement.robust_interpolation_statement', 'EllipsoidUniversality.RobustStatement.robust_statement', 'EllipsoidUniversality.RobustStatement.robust_theorem_statement'], 'SnapshotShifted': ['EllipsoidUniversality.ShiftedConditionStatement.shifted_condition_measurability_statement', 'EllipsoidUniversality.ShiftedConditionStatement.shifted_condition_number_statement', 'EllipsoidUniversality.ShiftedConditionStatement.shifted_condition_statement', 'EllipsoidUniversality.ShiftedConditionStatement.shifted_condition_threshold_statement', 'EllipsoidUniversality.ShiftedErrorStatement.shifted_error_limit_statement', 'EllipsoidUniversality.ShiftedErrorStatement.shifted_error_measurable_statement', 'EllipsoidUniversality.ShiftedErrorStatement.shifted_error_statement', 'EllipsoidUniversality.ShiftedGaussianStatement.shifted_gaussian_bounds_statement', 'EllipsoidUniversality.ShiftedGaussianStatement.shifted_gaussian_measurability_statement', 'EllipsoidUniversality.ShiftedGaussianStatement.shifted_gaussian_statement', 'EllipsoidUniversality.ShiftedGaussianStatement.shifted_gaussian_uniform_lower_statement', 'EllipsoidUniversality.ShiftedMixtureSatStatement.countable_shifted_mixture_sat_statement', 'EllipsoidUniversality.ShiftedMixtureSatStatement.finite_shifted_mixture_sat_statement', 'EllipsoidUniversality.ShiftedMixtureSatStatement.shifted_mixture_sat_statement', 'EllipsoidUniversality.ShiftedMixtureUnsatStatement.countable_shifted_mixture_unsat_statement', 'EllipsoidUniversality.ShiftedMixtureUnsatStatement.finite_shifted_mixture_unsat_statement', 'EllipsoidUniversality.ShiftedMixtureUnsatStatement.shifted_mixture_unsat_statement', 'EllipsoidUniversality.ShiftedQuadricStatement.shifted_quadric_statement', 'EllipsoidUniversality.ShiftedSignStatement.shifted_sign_gaussian_statement', 'EllipsoidUniversality.ShiftedSignStatement.shifted_sign_mixture_statement', 'EllipsoidUniversality.ShiftedSignStatement.shifted_sign_observables_statement', 'EllipsoidUniversality.ShiftedSignStatement.shifted_sign_outer_statement', 'EllipsoidUniversality.ShiftedSignStatement.shifted_sign_statement'], 'SnapshotShiftedDefinitions': ['Checks.ShiftedDefinitions.cmixture_characterization', 'Checks.ShiftedDefinitions.cmixture_weights_characterization', 'Checks.ShiftedDefinitions.coordinate_support_characterization', 'Checks.ShiftedDefinitions.countable_row_law_characterization', 'Checks.ShiftedDefinitions.family_sequence_limit_characterization', 'Checks.ShiftedDefinitions.finite_row_law_characterization', 'Checks.ShiftedDefinitions.gaussian_small_shift_characterization', 'Checks.ShiftedDefinitions.iid_row_sample_law_characterization', 'Checks.ShiftedDefinitions.mixture_characterization', 'Checks.ShiftedDefinitions.mixture_weights_characterization', 'Checks.ShiftedDefinitions.point_law_characterization', 'Checks.ShiftedDefinitions.quadric_eval_characterization', 'Checks.ShiftedDefinitions.row_of_tuple_characterization', 'Checks.ShiftedDefinitions.row_outer_characterization', 'Checks.ShiftedDefinitions.row_sample_map_characterization', 'Checks.ShiftedDefinitions.row_shift_characterization', 'Checks.ShiftedDefinitions.row_shift_law_characterization', 'Checks.ShiftedDefinitions.row_symmetric_law_characterization', 'Checks.ShiftedDefinitions.sample_flat_col_characterization', 'Checks.ShiftedDefinitions.sample_flat_row_characterization', 'Checks.ShiftedDefinitions.sample_of_row_tuple_characterization', 'Checks.ShiftedDefinitions.sample_row_tuple_characterization', 'Checks.ShiftedDefinitions.sample_translate_characterization', 'Checks.ShiftedDefinitions.shifted_iid_sample_law_characterization', 'Checks.ShiftedDefinitions.sign_mixture_sample_law_characterization', 'Checks.ShiftedDefinitions.sign_shift_law_characterization', 'Checks.ShiftedDefinitions.sign_shift_weights_characterization', 'Checks.ShiftedDefinitions.translation_fitting_error_characterization', 'Checks.ShiftedDefinitions.tuple_map_characterization'], 'SnapshotTupleProd': ['GaussianAnalysis.probability.lindeberg.HB_unnamed_factory_2', 'GaussianAnalysis.probability.lindeberg.lindeberg_tuple_cons__canonical__measurable_function_MeasurableFun', 'GaussianAnalysis.probability.lindeberg.measurable_tuple_cons', 'GaussianAnalysis.probability.lindeberg.tuple_cons', 'GaussianAnalysis.probability.lindeberg.tuple_prod']}
# The declarations of the pinned sections tuple_prod and lambda_max.
PINNED_NAMES = ['GaussianAnalysis.probability.lindeberg.HB_unnamed_factory_2', 'GaussianAnalysis.probability.lindeberg.lindeberg_tuple_cons__canonical__measurable_function_MeasurableFun', 'GaussianAnalysis.probability.lindeberg.measurable_tuple_cons', 'GaussianAnalysis.probability.lindeberg.tuple_cons', 'GaussianAnalysis.probability.lindeberg.tuple_prod', 'GaussianAnalysis.matrix.lambda_max.lambda_max']
# The frozen modules (58 files).
FROZEN_MODULES = ['EllipsoidFitting.AnalysisIntegralDefinitions', 'EllipsoidFitting.GaussianDefinitions', 'EllipsoidFitting.GaussianProbabilityDefinitions', 'EllipsoidFitting.GaussianProbabilityProductDefinitions', 'EllipsoidFitting.MainStatement', 'EllipsoidFitting.MainTheorem', 'EllipsoidFitting.PaperMainDefinitions', 'EllipsoidFitting.PaperMainResults', 'EllipsoidUniversality.ConditionDefinitions', 'EllipsoidUniversality.ConditionEndpoints', 'EllipsoidUniversality.ConditionKappaCurveStatement', 'EllipsoidUniversality.ConditionKappaDefinitions', 'EllipsoidUniversality.ConditionKappaRobustStatement', 'EllipsoidUniversality.ConditionKappaStatement', 'EllipsoidUniversality.ConditionRobustStatement', 'EllipsoidUniversality.ConditionStatement', 'EllipsoidUniversality.ContinuousLatent', 'EllipsoidUniversality.CountableMixtureDefinitions', 'EllipsoidUniversality.CountableMixtureStatement', 'EllipsoidUniversality.LatentSignDefinitions', 'EllipsoidUniversality.LatentSignScope', 'EllipsoidUniversality.LatentSignStatement', 'EllipsoidUniversality.LatentTensorUpper', 'EllipsoidUniversality.LatentTensorization', 'EllipsoidUniversality.MixtureDefinitions', 'EllipsoidUniversality.MixtureStatement', 'EllipsoidUniversality.PairedDefinitions', 'EllipsoidUniversality.PairedStatement', 'EllipsoidUniversality.RobustDefinitions', 'EllipsoidUniversality.RobustStatement', 'EllipsoidUniversality.ShiftedConditionStatement', 'EllipsoidUniversality.ShiftedErrorStatement', 'EllipsoidUniversality.ShiftedGaussianStatement', 'EllipsoidUniversality.ShiftedMixtureSatStatement', 'EllipsoidUniversality.ShiftedMixtureUnsatStatement', 'EllipsoidUniversality.ShiftedQuadricStatement', 'EllipsoidUniversality.ShiftedSignStatement', 'EllipsoidUniversality.UniversalityDefinitions', 'EllipsoidUniversality.UniversalityStatement', 'GaussianApplications.GoeEdgeStatement', 'GaussianApplications.MatrixSeriesStatement', 'GaussianApplications.MinSuperadditiveStatement', 'GaussianApplications.PerceptronSignDefinitions', 'GaussianApplications.PerceptronSignStatement', 'GaussianApplications.ProductSmoothingStatement', 'GaussianApplications.PsdLiftDefinitions', 'GaussianApplications.PsdLiftStatement', 'GaussianApplications.PsdNormalizationStatement', 'GaussianApplications.PsdRankDefinitions', 'GaussianApplications.PsdRankStatement', 'GaussianApplications.PsdSplittingStatement', 'GaussianApplications.SKGapDefinitions', 'GaussianApplications.SKGapStatement', 'GaussianApplications.SatThresholdDefinitions', 'GaussianApplications.SatThresholdStatement', 'GaussianApplications.SatVarianceDefinitions', 'GaussianApplications.SatVarianceStatement', 'GaussianApplications.TensorPackingStatement']
ROCQ_VERSION = "The Rocq Prover, version 9.1.1"
PACKAGES = {"rocq-core": "9.1.1", "rocq-mathcomp-ssreflect": "2.6.0",
            "rocq-mathcomp-analysis": "1.16.0"}
# The code of the check files added by rule 30 (SHA-256 of code()).
NEW_CHECK_CODE = {'check/TheoremIdentities.v': '2c8e1cc75f38b8f9bd7cc2f333acf7e5219326fbf5ba2f664ce1e5fb97a52950', 'check/Reports.v': '40a413e2c0235f58a4f99a03ecd7603937688dbbee237c7779bbda8f3672b059', 'check/MatrixSigmaRing.v': '93dcba7c2db44a36e92cad5479110fa92eb6d874a268f25ccc942edc6303f8e3', 'check/snapshots/SnapshotApplicationsDefinitions.v': '7efe8576613e770bac68ceec7e1da1685af7cc2ba478e7630c686ef3328da5fa', 'check/snapshots/SnapshotMatrixSigmaRing.v': '69dbef5995b8ea348fdd4e42f1f663170073d9ef85cf3b2a73b7a2fd343cee7a', 'check/snapshots/SnapshotPhase1.v': '6f0fe34b69e5fdcbd2a9982cd3c741200adac83a8ef432b3631f8a7f5d1480a5', 'check/snapshots/SnapshotPhase10.v': '58d60fe8ea2e6b44a828132912bd96c17b5c0f7335621d3ff6b9e47be473aec3', 'check/snapshots/SnapshotPhase11.v': '1dad4ee59c9ce77828c7da5ac1f5ccdd4188c01ffa38d1bf2221a921ac1f0e73', 'check/snapshots/SnapshotPhase12Batch1.v': '5577d1ef78041e6343d92fc932f39642a9814e9d01e4479eb955122c371bd78a', 'check/snapshots/SnapshotPhase12Batch2.v': 'eefd29b50bf3efbfc6e2039cbed7ff02a0ebb95b1fc1da4c8fb7e96c8221500e', 'check/snapshots/SnapshotPhase13.v': 'd53c5cebca8ac54aa2715cca87859cc55213df4f651a156cf096e536d1f72377', 'check/snapshots/SnapshotPhase13Freeze1.v': '30cccb145ca7e9906afc152f20217653e2d6904850566a6bdb0ee8150c8b5f3e', 'check/snapshots/SnapshotPhase13Freeze2.v': 'aaa4d69729494b90cd33092a8d0ca3b686af86a170117e4954eb126da9077161', 'check/snapshots/SnapshotPhase13Freeze3.v': 'be9a7b31f485c3aab0f2a31b443b44f34c25d5debd6d6a0d96f3b6dff25f1110', 'check/snapshots/SnapshotPhase1Theorems.v': 'af59288c93001fdfbd29ed5481fa2c8786e4769501351c76444525d766c55e1a', 'check/snapshots/SnapshotPhase5.v': '57bfc4ef2f1d36b8aefeaca386260183146c906de1835d005af834355e02187f', 'check/snapshots/SnapshotPhase6.v': 'd792342f45f9139d17efa508d47ee8ee25a78c4e3ee569ab2e6694fd21bc4f30', 'check/snapshots/SnapshotPhase7.v': 'd50b6506107ca4a94c7fa74ed8660087ac9c8db34a43d18338ddd2c427a0148b', 'check/snapshots/SnapshotPhase8.v': '271074e46836033353f3dac072360c3bd3a2c5dbe2c4c1cf2c05766f9b25fc94', 'check/snapshots/SnapshotPhase9.v': 'fba0813e1b71db80d055e3d65fc9a44e1b8186422d18b154d688bb746aa41631', 'check/snapshots/SnapshotTupleProd.v': 'f8de7cd1203612ff34c923aee1a7f1f6e7ce7eb7d8282dcfabd0b9c372dfe85d', 'check/Phase14Identities.v': '1a8e7b0a75465464a0d011f7a301c9a75f09a028dd1cd3a6039f7bf11cbabd65', 'check/Phase14Reports.v': '2dd0b0981a64b6e830ac66418985a3ada1dcf15647bae6784f19addc5f43fcbc', 'check/snapshots/SnapshotPhase14.v': '9d9e83728bd78476731826f914e37694d1bb8ef865a6587e34554ff877af6674', 'check/snapshots/SnapshotPhase14Definitions.v': '16af403837b9617f9c8ff0ff1bd5dfd31c5d76f01a724e442563dc2469fc4437', 'check/snapshots/SnapshotPhase14Statements.v': '6886a67779a2917ba1e27f020fc0c5da6b1ad35fd2a07b0bc1a8e9bf403eb768', 'check/ShiftedIdentities.v': '808b204bbdf261283a1aa0dca88ccd6777362d64491812421d3d1f5c3439bc75', 'check/ShiftedReports.v': 'b62f650802fa1210dfd7eba2b3468396099954a8624b426da9eed2e4cc6e5777', 'check/snapshots/SnapshotShifted.v': 'c6f4b9df928b5a3c33f5df49a5f5fdb3fbd82ae74ba5895bfd22dd894116de64', 'check/snapshots/SnapshotShiftedDefinitions.v': '086a8d1f1e7c6bde8a9a5208a7f9aff6f0510525a15aaecbb583b67cbfa66e25'}
# Files fixed byte for byte (SHA-256): the Makefile and the reviewed scripts.
FIXED_FILES = {'Makefile': 'fbac12558c138f16d98528ab94958440f253c00696990dd184006c3beddc6d0a', 'check/snapshots/REFERENCES.json': '376a5716fe96ae386d498db0813d5f2a2d4e398f9ae3e07cf2c083d0d7fb0e4d', 'check/snapshots/SnapshotAcceptedStatements.v': '06d37d6d739528f906f05fcc294cdb0264958a192582df1102f176b5129e29ec', 'check/snapshots/SnapshotAcceptedStatements.txt': '25a5860620224a21d5740ea20dc0a50c02bd13018f36a61cfda9e7b24d6453cd', 'check/snapshots/AcceptedConversions.v': 'c53ea1f50dfbd10e6272ed5e5fcd6d540ff9747dc98a59ac380477b2774faeb2', 'scripts/run_checks.py': '3548d99aea726ecd8ebdde8049785a19ae8c6945be8e8c20e4b8b4787c35970e', 'scripts/rocq_lex.py': '898141e4b081cee47b6fe8c4fc315817a4c2f26ef1529067dc117104edeac5c4', 'scripts/test_rocq_lex.py': '2d3e9b23442958f1368179541d092ed7d17777bb72c9f4d47327e84b22ea7324', 'scripts/snapshot_baselines.py': '604d298f847b7d53305d247c64aa1ac6a7c055b06fd177b13ae0e7f1f2dc9610', 'scripts/run_regressions.py': '76f3efa7018e6f44c7a82d58b52925bfe54e7354b9db7bd4775b6ae19b349d71', 'scripts/test_regression_cleanup.py': '94100576e7dc1846a5efa91be5a6ba4cea4b9451f2289f62dea9b1e3bb7780f7', 'scripts/source_inventory.py': '60f367948e412901bb78810bd590d2179f62cd451536cd1079d88cac219ba573', 'scripts/test_source_inventory.py': '02d8f982a224980ae0ba13c86641c004de399bb2fb3f0bc39dafffa6ef575885', 'scripts/test_command_heads.py': '11fb596ae2f2eab2f30967a58773ee1e93d488706da75df25f598ed255797758', 'scripts/test_check_runner.py': 'a6ebdbb5ff36fde036c2b97d8cd1b4c6f8648eb5fe07c2d109f832e82dcdaba2', 'scripts/test_report_outputs.py': 'a50b255ace43412e06bec87cd3fad22148a32501d319b86356c6016a95d9428a', 'scripts/test_dependency_consistency.py': '85067e57e37161c26d37d9ab113707d65cab54cff7c32cfa99759b85b18674ed', 'scripts/identity_sidecars.py': 'be1b8560b4baf3be9b9d9094f5254a0fe9862523e9fe2e75c1a1a7e908826f09', 'scripts/test_identity_sidecars.py': '3448736a22d5e1367a200bcd46f5ac326ddcc45ae27354dc7d7d74cafe27592b', 'check/identity/kernel_identity.ml': '6435bcb9af29a235937e076b347ec159d30d5b923da5c011798ca4cc7ad722f0', 'check/identity/kernel_universe.ml': 'a0a6e83517d914361cbbea963db4b208a5f217e97005ed8e61a1bc55e40ffb66', 'check/identity/META': '0b344f7c1aba69f30a90ecfd7b601b273a762c0c5cef876a7616ad090ab9fc7a', 'check/identity/README': 'ae517f66c654f056a07883773c4cf0391d1b8cb231a3f8ab9265064dbcff1f0b', 'check/identity/inventory.json': '3a2794ff8891ae777ae8bee009486549345e1c5f8357b8e7d1a40c30ea420fe0', 'check/identity/REFERENCES.json': 'e4879312ba2dccdb86f3f9702adf3f1758776bee081c1b1cb04e2e5b59a26402', 'check/identity/IdentitySnapshotApplicationsDefinitions.v': 'fece3cfb9bd1c1bec2803ab6b597499328b0468db19970bc8a97e7395edc20eb', 'check/identity/IdentitySnapshotMatrixSigmaRing.v': 'dbacd7d5e24cc453c23574df4efbca3c3152884673bb07d95d32a7027f95e715', 'check/identity/IdentitySnapshotPhase1.v': '2153b00d5ff804c403b620c46279421da59b3aae03aa190ce4156e9b8185c3cf', 'check/identity/IdentitySnapshotPhase10.v': 'ccb4afab6a297c74ba711d4c9dbf9ab7734d164cc55de105e281c2f3c2a7c13a', 'check/identity/IdentitySnapshotPhase11.v': 'dd0dcad971e79c8aa2d2517d2d7d59e9e6e66e1696f297b850a2868cb47a08ee', 'check/identity/IdentitySnapshotPhase12Batch1.v': '53c34c77407532011068796f7db4351491ed7311eb3dd0d8934e51d2418d72f7', 'check/identity/IdentitySnapshotPhase12Batch2.v': 'bdd0caa5aaf917490207897ea93d7549c06289665a5496430cdf1b7288a8792d', 'check/identity/IdentitySnapshotPhase13.v': 'f8ca2f616ea1e8b1d2d9a26012651b3ac4847a1a6abaac2328ee0eef454b17b2', 'check/identity/IdentitySnapshotPhase13Freeze1.v': 'aa158786f0bea88e68436ee5b5a4f69409478684db1913032b36e6c47ccade22', 'check/identity/IdentitySnapshotPhase13Freeze2.v': '3b0c5ad0871879cd96347bce9c1ade1408bcbc758302d229072311d1e35e4b36', 'check/identity/IdentitySnapshotPhase13Freeze3.v': 'abcdd5b2d2870ed14c7b4cfc89d673bf8f6a99af12b55bb522227ac937cec070', 'check/identity/IdentitySnapshotPhase1Theorems.v': 'de8ba5ec07f9ea911c19d08ded413376c3e11dfe5a01da51061711ea754f80df', 'check/identity/IdentitySnapshotPhase5.v': '438ebb69ff99cbc743d4b5fb7c4b493f5978365b1fe56549e9c0cc44c9d83f5d', 'check/identity/IdentitySnapshotPhase6.v': '1e65c54f94bb0ad5fab3131212e76df38e72ac885c9f3189d365bf4904b1f68e', 'check/identity/IdentitySnapshotPhase7.v': '0ff636ddc9edc1d52eb9a7586fc3594d696e8cec54baec91f9e82dddfe1614e4', 'check/identity/IdentitySnapshotPhase8.v': '7ed127dbd1493c0e17d7978a3c1336de10b1857ba725a7ae45dcc910303ae27d', 'check/identity/IdentitySnapshotPhase9.v': '54bb7e5e246e2362a10e0258b80a1f501b2cadb2a08b036f4794594c2cd685ae', 'check/identity/IdentitySnapshotTupleProd.v': 'c0f14aa71bee02a8a30f8a30cb31b59e2c74057c0ef710ccf579e82611ae4b16', 'check/snapshots/SnapshotAcceptedStatements14.v': 'f64b4f4c2e9fe75c211a96eefde7564a9b476d0541c3f65a9f45ce216a58f845', 'check/snapshots/SnapshotAcceptedStatements14.txt': '5db70419d3cce9d9867ac128b80823cd5ddbb71126ff12c7a86264c152403e42', 'check/snapshots/AcceptedConversions14.v': 'f7f871935ccedfed4d268620fb21f9585ff9cc850658ef93c4c04d19aba5bd08', 'check/identity/IdentitySnapshotPhase14.v': 'a4175c7a2d200a866505f88d4a92c947f7febe60448161fceacc64ee9e148e07', 'check/identity/IdentitySnapshotPhase14Definitions.v': '33cd4a44a8e5b8523aadc4f7298d86227be08fd46acad6b55098e0cff97ee8b6', 'check/identity/IdentitySnapshotPhase14Statements.v': '3ecc0025c9e0d1ffea6c7019bbf570b4379231fc35ff9fb534735f8c5a691ebe', 'check/identity/IdentitySnapshotShifted.v': 'de2453001115d3b26e17ae816409f3cafa2cadd95fb26c15f97817522089f6cf', 'check/identity/IdentitySnapshotShiftedDefinitions.v': '98c6e35958ad29236fe132b3192c7dc322e02cab9bbd226eb54b3ed5df7fd8c0'}
# The files of scripts/, exactly.
SCRIPTS = ['check_sources.py', 'export_from_ellipsoid_rocq.py', 'stale_citations.py', 'unused.py', 'rocq_lex.py', 'test_rocq_lex.py', 'run_checks.py', 'snapshot_baselines.py', 'run_regressions.py', 'source_inventory.py', 'test_source_inventory.py', 'test_command_heads.py', 'test_check_runner.py', 'test_report_outputs.py', 'test_dependency_consistency.py', 'test_regression_cleanup.py', 'identity_sidecars.py', 'test_identity_sidecars.py']
# Files that make reads before the Makefile (GNUmakefile, makefile) or that the
# generated Makefile.rocq includes (Makefile.rocq.local, Makefile.rocq.local-late)
# if they exist.
ABSENT_FILES = ["GNUmakefile", "makefile", "Makefile.rocq.local", "Makefile.rocq.local-late"]
COQPROJECT_OPTIONS = ['-Q library GaussianAnalysis', '-Q theories EllipsoidFitting', '-Q extension EllipsoidUniversality', '-Q applications GaussianApplications', '-arg -w -arg -notation-overridden', '-arg -w -arg -ambiguous-paths', '-arg -w -arg -notation-incompatible-prefix', '-arg -w -arg -hiding-delimiting-key', '-arg -w -arg +comment-terminator-in-string', '-arg -q']
PAPERS = {"EllipsoidFitting", "EllipsoidUniversality"}
APPLICATIONS = "GaussianApplications"
ASSUMPTION = re.compile(
    r"(?:\A|(?<=\.))\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+)?"
    r"(Admitted\s*\.|Axioms?\b|Parameters?\b|Conjecture\b)")
REQUIRE = re.compile(r"(?:From\s+([\w.]+)\s+)?Require(?:\s+(?:Import|Export))?\s+([^.]+(?:\.[A-Za-z]\w*)*)\s*\.", re.S)
STDLIB_REALS = re.compile(r"^(Reals|Lra|Psatz|Fourier|Ranalysis\w*|R[A-Z]\w*|Rbase|Rfunctions|Rpower|Rtrigo\w*|Rdefinitions|Raxioms|Rbasic_fun|Rsqrt_def|Rlimit|Rseries|Rcomplete|Rderiv|Rprod|Rtopology|SeqProp|SeqSeries|PSeries_reg|Exp_prop|Ratan|Rsigma|Rgeom|Cos_rel|Sqrt_reg|ClassicalDedekindReals|ConstructiveCauchyReals\w*)$")
MATHCOMP_BRIDGE = {"Rstruct", "Rstruct_topology"}


def sha256_hex(data):
    return hashlib.sha256(data).hexdigest()


def present_exact(rel):
    """Whether ROOT/rel exists, matching every path component by its exact
    name. Path.exists() alone is wrong on a case-insensitive file system (it
    finds Makefile when asked for makefile, so ABSENT_FILES would falsely
    fail on macOS); iterdir() returns the names as stored, so this compares
    case-sensitively."""
    base = ROOT
    for part in Path(rel).parts:
        try:
            if part not in {child.name for child in base.iterdir()}:
                return False
        except OSError:
            return False
        base = base / part
    return True


# Rule 30 (a): the text is read as Rocq reads it, by scripts/rocq_lex.py. A
# text that cannot be read (an unterminated comment or string, or a form that
# Rocq reads by the keywords in scope) is a failure, recorded here and
# reported by main().
LEX_FAILURES = []


def read_text(path):
    """The text of a file as Rocq reads it: UTF-8, carriage returns kept."""
    return rocq_lex.read_source(path)


def at_baseline(commit, path):
    """The text of path at commit, decoded as Rocq reads it (the lexer's
    decode_source: UTF-8, carriage returns kept, LexError on invalid UTF-8)."""
    return rocq_lex.decode_source(subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{commit}:{path}"],
        check=True, capture_output=True).stdout)


def views(text, where):
    """(stripped, masked): the text with each comment replaced by one blank
    and strings kept, and the same with the inside of every string replaced
    by x, for finding commands in code only. Both are aligned character by
    character. None if the text cannot be read."""
    try:
        pieces = rocq_lex.segments(text)
    except rocq_lex.LexError as err:
        LEX_FAILURES.append(f"{where}: {err}")
        return None
    stripped, masked = [], []
    for kind, piece in pieces:
        if kind == "blank" and not stripped and piece.startswith("\ufeff"):
            # Rocq treats a BOM as a blank only at the start of a source.
            # Preserve offsets/source bytes, but expose the following head.
            stripped.append(piece)
            masked.append(" " + piece[1:])
        elif kind == "comment":
            stripped.append(" ")
            masked.append(" ")
        elif kind == "string":
            stripped.append(piece)
            masked.append('"' + "x" * (len(piece) - 2) + '"')
        else:
            stripped.append(piece)
            masked.append(piece)
    return "".join(stripped), "".join(masked)


def code(text, where="a source"):
    """The code of a source: each maximal run of blanks and comments one
    blank, strings kept exactly (rocq_lex.code)."""
    try:
        return rocq_lex.code(text)
    except rocq_lex.LexError as err:
        LEX_FAILURES.append(f"{where}: {err}")
        return "\0unreadable\0"


SENTENCE_END = re.compile(r"\.(?=[ \t\n\r]|\Z)")
LEADING = re.compile(r"\A(?:[-+*]+|[{}]|[ \t\n\r])+")
PREFIX_WORD = re.compile(r"[\w']+")
PREFIX_ATTRIBUTE = re.compile(r"#\[[^\]]*\]")
PREFIX_NATURAL = re.compile(r"[0-9]+(?=[ \t\n\r#]|\Z)")
PREFIX_MODIFIERS = frozenset((
    "Local", "Global", "Export", "Polymorphic", "Monomorphic", "Cumulative",
    "NonCumulative", "Private", "Program"))
# The complete vernac_control alternatives of Rocq 9.1.1, g_vernac.mlg.
# None occurs in the accepted sources. Refuse all of them before compilation:
# even Profile can write a file, and Fail/Succeed restore the command's state.
CONTROL_PREFIXES = frozenset((
    "Time", "Timeout", "Instructions", "Profile", "Redirect", "Fail", "Succeed"))


def command_prefix(body, where):
    """Read attributes, modifiers and control prefixes, in any order.

    body comes from views(): comments are blanks, and a string is one pair
    of quotes with only x inside. Keep control names in modifiers so every
    consumer sees the same command head, while forbidden() still rejects
    the controls themselves. Arguments never become command text. Original
    sentence offsets and source slices are not changed by this operation.
    None means a malformed prefix; LEX_FAILURES makes the source check fail.
    """
    lead = LEADING.match(body)
    pos = lead.end() if lead else 0
    attributes, modifiers = [], []

    def bad(reason):
        LEX_FAILURES.append(f"{where}: unreadable command prefix: {reason}")
        return None

    while True:
        while pos < len(body) and body[pos] in rocq_lex.BLANKS:
            pos += 1
        if body.startswith("#[", pos):
            attr = PREFIX_ATTRIBUTE.match(body, pos)
            if attr is None:
                return bad("unterminated attribute")
            attributes.append(attr.group(0))
            pos = attr.end()
            continue
        word = PREFIX_WORD.match(body, pos)
        if word is None:
            break
        name = word.group(0)
        if name not in PREFIX_MODIFIERS and name not in CONTROL_PREFIXES:
            break
        modifiers.append(name)
        pos = word.end()
        while pos < len(body) and body[pos] in rocq_lex.BLANKS:
            pos += 1
        if name == "Timeout":
            natural = PREFIX_NATURAL.match(body, pos)
            if natural is None:
                return bad("Timeout needs a natural number")
            pos = natural.end()
        elif name in ("Redirect", "Profile"):
            # Profile has an optional filename; Redirect has a required one.
            # Quotes inside a source string have already been masked by views.
            if pos < len(body) and body[pos] == '"':
                end = body.find('"', pos + 1)
                if end < 0:
                    return bad(f"{name} has an unterminated filename")
                pos = end + 1
            elif name == "Redirect":
                return bad("Redirect needs a filename")
    command = " ".join(body[pos:].split())
    if not command and (attributes or modifiers):
        return bad("attributes, modifiers or controls without a command")
    return (" ".join(" ".join(attributes).split()),
            " ".join(modifiers), command)


def sentences(text, where):
    """Code sentences as (attributes, modifiers, command, start, end).

    command has a consistently normalized head; modifiers also records every
    control prefix, which forbidden() rejects. Strings are masked. start and
    end still address the original comment-stripped source, used by freezes.
    None if the lexer or the command-prefix reader cannot read the source.
    """
    v = views(text, where)
    if v is None:
        return None
    _, masked = v
    found, start = [], 0
    for m in SENTENCE_END.finditer(masked):
        parsed = command_prefix(masked[start:m.start()], where)
        if parsed is None:
            return None
        found.append((*parsed, start, m.end()))
        start = m.end()
    if masked[start:].strip():
        # Use the same reader even for an incomplete final command. A missing
        # dot must not hide a control/attribute from the source scan.
        parsed = command_prefix(masked[start:], where)
        if parsed is None:
            return None
        found.append((*parsed, start, len(masked)))
    return found


REQUIRE_SENTENCE = re.compile(r"(?:From (\S+) )?Require(?: (?:Import|Export))? (.+)\Z")


def requires(text, where):
    """(root, module) for each module of each Require sentence; a dotted
    module name counts as one name (E24)."""
    for _, _, command, _, _ in sentences(text, where) or []:
        m = REQUIRE_SENTENCE.match(command)
        if m:
            for name in m.group(2).split():
                yield m.group(1) or "", name


def section_code(text, name, where):
    """The Require sentences of a source and the code of its section name,
    from the sentence Section name to the sentence End name, both found in
    the code only."""
    v, found = views(text, where), sentences(text, where)
    if v is None or found is None:
        return None, None
    stripped = v[0]
    # Each Require sentence is compared through code(), as Rocq reads it, not
    # through the blank-collapsed command, which str.split() normalizes (E32).
    reqs = " ".join(code(stripped[start:end], where)
                    for _, _, c, start, end in found if REQUIRE_SENTENCE.match(c))
    opens = [s for s in found if s[2] == f"Section {name}" and not s[0] and not s[1]]
    ends = [s for s in found if s[2] == f"End {name}"]
    if len(opens) != 1 or len(ends) != 1 or ends[0][3] < opens[0][3]:
        return reqs, None
    return reqs, code(stripped[opens[0][3]:ends[0][4]], where)


def tuple_prod_code(text, where):
    return section_code(text, "tuple_prod", where)


# Rule 30 (a): commands refused in theories/, library/, extension/ and
# applications/, outside comments and strings: the four of rule 2, after any
# attributes and modifiers, and the commands that declare an assumption, turn
# off a kernel check, load code or write files. Elpi programs can run shell
# commands while Rocq compiles (the built-ins system and open_out of Elpi),
# from a quotation or from a file that Extra Dependency names (E37): every
# Elpi command and Extra Dependency are refused. The commands of
# Hierarchy-Builder (HB.instance and the others) run its own programs and
# take only Rocq terms, except HB.graph, which writes the file it names, and
# is refused.
FORBIDDEN_COMMANDS = re.compile(
    r"\A(?:Axioms?|Parameters?|Conjectures?|Admitted|Admit Obligations|Declare Instance|"
    r"Declare ML Module|Add (?:Rec )?LoadPath|Add ML Path|Load|"
    r"(?:Recursive |Separate )?Extraction(?: Library)?|Redirect|Cd|Elpi|HB\.graph|"
    r"(?:From \S+ )?Extra Dependency|"
    r"(?:Set|Unset) (?:Guard|Positivity|Universe) Checking)\b")
SECTION_VARIABLES = re.compile(r"\A(?:Variables?|Hypothes[ie]s|Context)\b")


def forbidden(text, where, scope):
    """The failures of rule 2 and of the bans of rule 30 in one source.
    scope: "all" for theories/, "library" for library/, extension/ and
    applications/, which also refuse global or exported settings, exported
    modules and Require Export, and "fixed" for frozen and code-fixed files,
    which also refuse Set Warnings and warning attributes."""
    found = sentences(text, where)
    if found is None:
        return []
    out, stack = [], []
    for attributes, modifiers, command, _, _ in found:
        head = command.split(" ", 1)[0] if command else ""
        controls = CONTROL_PREFIXES.intersection(modifiers.split())
        for control in sorted(controls):
            out.append(f"{where}: control prefix {control} is not allowed")
        refused = FORBIDDEN_COMMANDS.match(command)
        if refused:
            out.append(f"{where}: {refused.group(0)}")
        if "bypass_check" in attributes:
            out.append(f"{where}: the attribute bypass_check")
        if SECTION_VARIABLES.match(command) and not stack:
            out.append(f"{where}: {head} outside a section declares an axiom")
        # A refused control never changes the scanner's persistent scope.
        # In particular, Succeed Section cannot license a later Variable.
        if not controls:
            opened = re.fullmatch(r"Section (\S+)", command)
            ended = re.fullmatch(r"End (\S+)", command)
            if opened:
                stack.append(opened.group(1))
            elif ended and stack:
                if ended.group(1) != stack[-1]:
                    out.append(f"{where}: End does not match the open section {stack[-1]}")
                else:
                    stack.pop()
            # Module declarations are forbidden inside sections by Rocq.
            # Outside sections their aliases/functors do not license Variables.
        if scope in ("library", "fixed"):
            settings = command.startswith(("Set ", "Unset "))
            if settings and (re.search(r"#\[\s*(?:global|export)\b", attributes)
                             or re.search(r"\b(?:Global|Export)\b", modifiers)):
                out.append(f"{where}: a global or exported setting: {command[:60]}")
            if head == "Export" or ("Export" in modifiers.split() and not settings) \
                    or re.match(r"(?:From \S+ )?Require Export\b", command):
                out.append(f"{where}: an exported module: {command[:60]}")
        if scope == "fixed":
            if command.startswith("Set Warnings") or re.search(r"\bwarnings?\s*=", attributes):
                out.append(f"{where}: Set Warnings or a warning attribute")
    return out


def comment_boundaries(text, where):
    """The failures of the boundary rule of frozen and code-fixed files: a
    blank, a line boundary or a parenthesis before every (* and after every
    *). The lexer refuses a (* glued to a token; this checks the end."""
    try:
        pieces = rocq_lex.segments(text)
    except rocq_lex.LexError:
        return []
    out = []
    for k, (kind, piece) in enumerate(pieces):
        if kind == "comment" and k + 1 < len(pieces):
            kind2, piece2 = pieces[k + 1]
            if kind2 not in ("blank", "comment") and not piece2.startswith(("(", ")")):
                out.append(f"{where}: no blank after the end of a comment: {piece2[:30]!r}")
    return out


def axiom_names(text):
    """The names of an expected list (one axiom per line, continuation lines
    indented)."""
    names = set()
    for line in text.splitlines():
        if not line or line[0].isspace() or line.rstrip() == "Axioms:":
            continue
        names.add(line.split(" :", 1)[0].strip())
    return names


PROJECT_ROOTS = ("GaussianAnalysis.", "EllipsoidFitting.", "EllipsoidUniversality.",
                 "GaussianApplications.", "Checks.")


def kernel_failures(text):
    """The failures that the output of rocqchk -silent -o shows: a theory
    other than the default one, a constant or inductive that relies on
    type-in-type, unsafe (co)fixpoints or assumed positivity, or an axiom of
    a project module (rule 2 at the kernel level)."""
    out = []
    for theory in ("* Theory: Set is predicative", "* Theory: Rewrite rules are not allowed"):
        if theory not in text.splitlines():
            out.append(f"rocqchk: the line {theory!r} is missing")
    for header in ("* Constants/Inductives relying on type-in-type:",
                   "* Constants/Inductives relying on unsafe (co)fixpoints:",
                   "* Inductives whose positivity is assumed:"):
        if f"{header} <none>" not in text.splitlines():
            out.append(f"rocqchk: {header} not <none>")
    section, axioms = None, []
    for line in text.splitlines():
        if line.startswith("* "):
            section = line
        elif section == "* Axioms:" and line.startswith("    ") and line.strip():
            axioms.append(line.strip())
    if "* Axioms:" not in text.splitlines():
        out.append("rocqchk: no list of axioms")
    for name in axioms:
        if name.startswith(PROJECT_ROOTS):
            out.append(f"rocqchk: the project axiom {name}")
    return out


UNSAFE = re.compile(r"relies on an unsafe hierarchy|is assumed to be guarded|"
                    r"is assumed to be positive|^Theory:", re.M)


def parse_output(text):
    """The items of a check output, in order: ("marker", name) for the output
    of Locate on a constant: the line "Constant <name>" or, for a long name,
    the line "Constant" and the name on the next line, possibly followed by
    "  (shorter name to refer to it in current context is ...)"; ("report",
    axioms) for a complete axiom report, the line "Closed under the global
    context" or the line "Axioms:" followed by at least one axiom (a line
    "<name> : ..." or "<name> :", with indented continuation lines);
    ("other", line) for any other line, including "Axioms:" with no axiom.
    The runner appends one completion trailer after successful exit; a cut
    or duplicated stream is rejected before parsing, independently of its
    manifest hash. This does not parse the Rocq grammar of printed types."""
    if not text.endswith(OUTPUT_COMPLETE) or text.count(OUTPUT_COMPLETE) != 1:
        return [("other", "missing or duplicated output-completion trailer")]
    text = text[:-len(OUTPUT_COMPLETE)]
    if text and not text.endswith("\n"):
        return [("other", "output ends inside a line before its completion trailer")]
    items, lines, k = [], text.splitlines(), 0
    while k < len(lines):
        line = lines[k]
        if line.startswith("Constant ") and len(line.split()) == 2:
            items.append(("marker", line.split()[1]))
            k += 1
        elif line == "Constant" and k + 1 < len(lines) and re.fullmatch(r"\S+", lines[k + 1]):
            items.append(("marker", lines[k + 1]))
            k += 2
        elif line == "Closed under the global context":
            items.append(("report", frozenset()))
            k += 1
            continue
        elif line == "Axioms:":
            axioms, k = set(), k + 1
            while k < len(lines) and lines[k] and not lines[k][0].isspace():
                m = re.match(r"(\S+) :(?: |$)", lines[k])
                if not m:
                    break
                axioms.add(m.group(1))
                k += 1
                while k < len(lines) and lines[k][:1].isspace():
                    k += 1
            items.append(("report", frozenset(axioms)) if axioms else ("other", "Axioms:"))
            continue
        else:
            items.append(("other", line))
            k += 1
            continue
        if k < len(lines) and re.fullmatch(
                r"  \(shorter name to refer to it in current context is \S+\)", lines[k]):
            k += 1
    return items


OUTPUT_COMPLETE = "=== ROCQ CHECK OUTPUT COMPLETE ===\n"
SOURCE_LOGICAL_ROOTS = (("library", "GaussianAnalysis"), ("theories", "EllipsoidFitting"),
                        ("extension", "EllipsoidUniversality"),
                        ("applications", "GaussianApplications"))


def validated_sources():
    inventory = _load("source_inventory", ROOT / "scripts/source_inventory.py")
    result = inventory.inspect_sources(ROOT, COQPROJECT_OPTIONS)
    if result["failures"]:
        raise ValueError("\n".join(result["failures"]))
    return result["sources"]


def kernel_source_modules(sources):
    roots = dict(SOURCE_LOGICAL_ROOTS)
    return [roots[source.split("/", 1)[0]] + "." +
            source.split("/", 1)[1][:-2].replace("/", ".") for source in sources]


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--reuse", metavar="RUN_ID",
                        help="for the regression tests only: verify the outputs of the "
                             "earlier run RUN_ID instead of starting the runner; the "
                             "Makefile, whose content rule 30 fixes, never passes it")
    parser.add_argument("--before-build", action="store_true",
                        help="check the sources only (every rule that reads no compiled "
                             "file), before anything compiles: make check runs this first")
    args = parser.parse_args()
    failures = []
    missing = []
    # Fail before reading frozen/check inputs if source traversal is unsafe
    # or differs from the exact build inventory (E41).
    try:
        sources = validated_sources()
    except ValueError as error:
        sys.exit(str(error))

    def read(path, binary=False):
        try:
            return (ROOT / path).read_bytes() if binary else read_text(ROOT / path)
        except OSError:
            if path not in missing:
                missing.append(path)
                failures.append(f"{path}: missing")
            return None
        except (UnicodeDecodeError, rocq_lex.LexError) as err:
            # Invalid UTF-8, or a text the lexer refuses: a failure; there is
            # no fallback to another reading.
            failures.append(f"{path}: cannot be read as Rocq reads it: {err}")
            return None

    def baseline(commit, path):
        try:
            return at_baseline(commit, path)
        except subprocess.CalledProcessError:
            failures.append(f"{path}: no such file at {commit[:12]}")
            return None
        except (UnicodeDecodeError, rocq_lex.LexError) as err:
            failures.append(f"{path}: cannot be read at {commit[:12]}: {err}")
            return None

    def fixed_rules(path, text):
        """Non-ASCII code, the comment boundaries and the bans of frozen and
        code-fixed files."""
        if text is None:
            return
        try:
            found = rocq_lex.non_ascii(text)
        except rocq_lex.LexError as err:
            LEX_FAILURES.append(f"{path}: {err}")
            found = []
        if found:
            line, column, char = found[0]
            failures.append(f"{path}: the non-ASCII character U+{ord(char):04X} at "
                            f"line {line}, column {column}, outside comments")
        failures.extend(comment_boundaries(text, path))
        failures.extend(f for f in forbidden(text, path, "fixed")
                        if "Set Warnings" in f or "warning" in f)

    def frozen(paths, commit):
        for path in paths:
            now, then = read(path), baseline(commit, path)
            if now is None or then is None:
                continue
            fixed_rules(path, now)
            if code(now, path) != code(then, f"{path} at {commit[:12]}"):
                failures.append(f"{path}: code differs from {commit[:12]}")

    def exact(paths, commit):
        for path in paths:
            now, then = read(path), baseline(commit, path)
            if now is not None and then is not None and now != then:
                failures.append(f"{path}: differs from {commit[:12]}")

    def exact_bytes(paths, commit):
        """Rule 31: the bytes of each file equal its bytes at commit."""
        for path in paths:
            now = read(path, binary=True)
            then = subprocess.run(["git", "-C", str(ROOT), "show", f"{commit}:{path}"],
                                  capture_output=True)
            if then.returncode != 0:
                failures.append(f"{path}: no such file at {commit[:12]}")
            elif now is not None and now != then.stdout:
                failures.append(f"{path}: differs from {commit[:12]}")

    def listed(dirs, commit):
        """Rule 31: the files that git lists under dirs at commit."""
        paths = []
        for d in dirs:
            found = subprocess.run(["git", "-C", str(ROOT), "ls-tree", "-r", "--name-only",
                                    commit, "--", d], capture_output=True, text=True)
            names = found.stdout.splitlines() if found.returncode == 0 else []
            if not names:
                failures.append(f"{d}: no file at {commit[:12]}")
            paths.extend(names)
        return paths

    def fixed(path, want, what):
        now = read(path)
        if now is None:
            return
        fixed_rules(path, now)
        if code(now, path) != want:
            failures.append(f"{path}: code differs from {what}")

    def pinned_section(path, name, commit):
        now_text, then_text = read(path), baseline(commit, path)
        if now_text is None or then_text is None:
            return
        now = section_code(now_text, name, path)
        if now[1] is None:
            failures.append(f"{path}: no section {name}, or more than one")
            return
        if any(ord(c) > 127 for c in now[1]):
            failures.append(f"{path}: a non-ASCII character in the section {name}")
        if now != section_code(then_text, name, f"{path} at {commit[:12]}"):
            failures.append(f"{path}: the Require commands or the section {name} "
                            f"differ from {commit[:12]}")

    # Rules 1, 7 to 28 and 31: the frozen files, the pinned check files and the
    # pinned sections, compared with their baselines.
    frozen_baseline = read("check/frozen-baseline")
    commit = frozen_baseline.split()[0] if frozen_baseline else "HEAD"
    frozen(FROZEN, commit)
    exact(EXACT, commit)
    frozen(EXTENSION_FROZEN, EXTENSION_BASELINE)
    frozen(PHASE6_FROZEN, PHASE6_BASELINE)
    frozen(LATENT_FROZEN, LATENT_BASELINE)
    frozen(PHASE8_FROZEN, PHASE8_BASELINE)
    frozen(PHASE9_FROZEN, PHASE9_BASELINE)
    frozen(PHASE10_FROZEN, PHASE10_BASELINE)
    frozen(PHASE11_FROZEN, PHASE11_BASELINE)
    frozen(PHASE12_B1_FROZEN, PHASE12_B1_BASELINE)
    frozen(PHASE12_B2_FROZEN, PHASE12_B2_BASELINE)
    exact(CHECKS_EXACT, CHECKS_BASELINE)
    exact(CHECKS_EXACT_P8, CHECKS_P8_BASELINE)
    exact(CHECKS_EXACT_P9, CHECKS_P9_BASELINE)
    exact(CHECKS_EXACT_P10, CHECKS_P10_BASELINE)
    exact(CHECKS_EXACT_P11, CHECKS_P11_BASELINE)
    exact(CHECKS_EXACT_P12, CHECKS_P12_BASELINE)
    exact_bytes([p for p in CHECKS_EXACT_P13 + MACHINERY_P13 if p not in P14_CHANGED],
                CHECKS_P13_BASELINE)
    exact_bytes([p for p in listed(MACHINERY_DIRS_P13, CHECKS_P13_BASELINE)
                 if p not in P14_CHANGED], CHECKS_P13_BASELINE)
    exact_bytes([p for p in CHECKS_EXACT_P14 + MACHINERY_P14 if p not in SHIFTED_CHANGED],
                CHECKS_P14_BASELINE)
    exact_bytes(CHECKS_EXACT_SHIFTED + MACHINERY_SHIFTED, CHECKS_SHIFTED_BASELINE)
    pinned_section(TUPLE_PROD, "tuple_prod", CHECKS_BASELINE)
    frozen(PHASE13_B1_FROZEN, PHASE13_B1_BASELINE)
    frozen(PHASE13_B2_FROZEN, PHASE13_B2_BASELINE)
    frozen(PHASE13_B3_FROZEN, PHASE13_B3_BASELINE)
    frozen(PHASE14_FROZEN, PHASE14_BASELINE)
    frozen(SHIFTED_FROZEN, SHIFTED_BASELINE)
    pinned_section(LAMBDA_MAX, "lambda_max", PHASE12_B1_BASELINE)

    # The code-fixed check files (their stored constants are not recomputed).
    fixed(PHASE13_DEFINITIONS, PHASE13_DEFINITIONS_FREEZES[-1],
          "the last code of PHASE13_DEFINITIONS_FREEZES")
    for k, (prev, nxt) in enumerate(zip(PHASE13_DEFINITIONS_FREEZES,
                                        PHASE13_DEFINITIONS_FREEZES[1:])):
        if not nxt.startswith(prev):
            failures.append(f"PHASE13_DEFINITIONS_FREEZES: freeze {k + 2} does not "
                            f"extend freeze {k + 1}")
    fixed(APPLICATIONS_DEFINITIONS, APPLICATIONS_DEFINITIONS_CHECK,
          "APPLICATIONS_DEFINITIONS_CHECK")
    fixed("check/UniversalityAssumptions.v", UNIVERSALITY_CHECK, "UNIVERSALITY_CHECK")
    fixed(LIBRARY_STATEMENTS, LIBRARY_STATEMENTS_CHECK, "LIBRARY_STATEMENTS_CHECK")
    fixed(PHASE14_DEFINITIONS, PHASE14_DEFINITIONS_CHECK, "PHASE14_DEFINITIONS_CHECK")
    fixed(PHASE14_STATEMENTS, PHASE14_STATEMENTS_CHECK, "PHASE14_STATEMENTS_CHECK")
    fixed(SHIFTED_DEFINITIONS, SHIFTED_DEFINITIONS_CHECK, "SHIFTED_DEFINITIONS_CHECK")
    for name, check, check_code, expected in (
            PHASE6_THEOREMS + PHASE8_THEOREMS + PHASE9_THEOREMS + PHASE10_THEOREMS
            + PHASE11_THEOREMS + PHASE12_THEOREMS + PHASE13_THEOREMS
            + PHASE14_THEOREMS + SHIFTED_THEOREMS):
        fixed(check, check_code, "the expected check")
    for path, digest in NEW_CHECK_CODE.items():
        now = read(path)
        if now is None:
            continue
        fixed_rules(path, now)
        if sha256_hex(code(now, path).encode()) != digest:
            failures.append(f"{path}: code differs from the code fixed by NEW_CHECK_CODE")

    # Rule 37: the two merge guards. The count guard: the theorem check files
    # of CHECK_FILES, those whose output is one marked report labelled by a
    # theorem of THEOREMS, correspond one to one with THEOREMS.
    theorem_checks = [c for c in CHECK_FILES if c.expect[0] == "marked"
                      and len(c.expect[1]) == 1 and c.expect[1][0][2] in THEOREMS]
    labels = [c.expect[1][0][2] for c in theorem_checks]
    for name in THEOREMS:
        if labels.count(name) != 1:
            failures.append(f"CHECK_FILES: {labels.count(name)} theorem check files report "
                            f"the {name}, exactly one required (the count guard)")
    if len(set(THEOREMS)) != len(THEOREMS) or len(theorem_checks) != len(THEOREMS) \
            or len({c.source for c in theorem_checks}) != len(theorem_checks):
        failures.append("CHECK_FILES: the theorem check files are not in one-to-one "
                        "correspondence with THEOREMS (the count guard)")
    # The completeness guard: every .v file under check/, outside
    # check/regression/, is compiled by an entry of CHECK_FILES or is one of
    # HISTORICAL_CHECK_FILES; a key of FIXED_FILES exempts nothing.
    compiled = {c.source for c in CHECK_FILES}
    for path in sorted((ROOT / "check").rglob("*.v")):
        rel = path.relative_to(ROOT).as_posix()
        if rel.startswith("check/regression/"):
            continue
        if rel not in compiled and rel not in HISTORICAL_CHECK_FILES:
            failures.append(f"{rel}: a .v file under check/ that no entry of CHECK_FILES "
                            "compiles (the completeness guard)")

    # Rule 26: the inventory of the accepted general statements.
    seen = set()
    for inv_commit, path, name, prop in INVENTORY:
        if (path, name) in seen:
            failures.append(f"INVENTORY: {path} {name} recorded twice")
        seen.add((path, name))
        if not re.fullmatch(r"[0-9a-f]{40}", inv_commit):
            failures.append(f"INVENTORY: {name}: {inv_commit} is not a full commit")
            continue
        try:
            then = at_baseline(inv_commit, path)
        except subprocess.CalledProcessError:
            failures.append(f"INVENTORY: {name}: no file {path} at {inv_commit[:12]}")
            continue
        defined = [c for _, _, c, _, _ in sentences(then, f"{path} at {inv_commit[:12]}") or []
                   if re.match(rf"Definition {re.escape(name)}\b", c)]
        if not defined:
            failures.append(f"INVENTORY: {name}: not defined in {path} at {inv_commit[:12]}")
        if not prop.strip():
            failures.append(f"INVENTORY: {name}: empty proposition")

    # Rule 29: every inventory entry stated in check/LibraryStatements.v.
    libst_text = read(LIBRARY_STATEMENTS)
    lemmas = {}
    if libst_text is not None:
        # Whole sentences built from the lexer's segments: a sentence Lemma
        # <base>_accepted : <statement> followed by the sentence Proof. Nothing
        # inside a string can stand for one (E31).
        v = views(libst_text, LIBRARY_STATEMENTS)
        found = sentences(libst_text, LIBRARY_STATEMENTS) or []
        for k, (attrs, mods, command, start, end) in enumerate(found):
            m = re.match(r"Lemma (\w+)_accepted :", command)
            if m and v is not None and not attrs and not mods \
                    and k + 1 < len(found) and found[k + 1][2] == "Proof":
                text = code(v[0][start:end], LIBRARY_STATEMENTS).strip()
                head = re.match(r"Lemma \w+_accepted :\s*", text)
                body = text[head.end():] if head else ""
                lemmas[m.group(1)] = (body[:-1] if body.endswith(".") else body).rstrip()
    for _, path, name, prop in INVENTORY:
        base = name[: -len("_statement")] if name.endswith("_statement") else name
        fun = re.match(r"fun\s+(.*?)\s*=>\s*(.*)\Z", prop, re.S)
        want = code(f"forall {fun.group(1)}, {fun.group(2)}" if fun else prop,
                    f"INVENTORY {name}").strip()
        if base not in lemmas:
            failures.append(f"{LIBRARY_STATEMENTS}: no lemma {base}_accepted for "
                            f"the accepted statement {name} of {path}")
        elif lemmas[base] != want:
            failures.append(f"{LIBRARY_STATEMENTS}: {base}_accepted does not state "
                            f"the accepted proposition of {name}")

    # Rule 32: the inventory of the accepted general statements of phase 14.
    seen = set()
    for inv_commit, path, name, prop in INVENTORY_P14:
        if (path, name) in seen:
            failures.append(f"INVENTORY_P14: {path} {name} recorded twice")
        seen.add((path, name))
        if not re.fullmatch(r"[0-9a-f]{40}", inv_commit):
            failures.append(f"INVENTORY_P14: {name}: {inv_commit} is not a full commit")
            continue
        try:
            then = at_baseline(inv_commit, path)
        except subprocess.CalledProcessError:
            failures.append(f"INVENTORY_P14: {name}: no file {path} at {inv_commit[:12]}")
            continue
        defined = [c for _, _, c, _, _ in sentences(then, f"{path} at {inv_commit[:12]}") or []
                   if re.match(rf"Definition {re.escape(name)}\b", c)]
        if not defined:
            failures.append(f"INVENTORY_P14: {name}: not defined in {path} at {inv_commit[:12]}")
        if not prop.strip():
            failures.append(f"INVENTORY_P14: {name}: empty proposition")

    # Rule 33: every entry of INVENTORY_P14 stated in check/Phase14Statements.v.
    p14_text = read(PHASE14_STATEMENTS)
    p14_lemmas = {}
    if p14_text is not None:
        v = views(p14_text, PHASE14_STATEMENTS)
        found = sentences(p14_text, PHASE14_STATEMENTS) or []
        for k, (attrs, mods, command, start, end) in enumerate(found):
            m = re.match(r"Lemma (\w+)_accepted :", command)
            if m and v is not None and not attrs and not mods \
                    and k + 1 < len(found) and found[k + 1][2] == "Proof":
                text = code(v[0][start:end], PHASE14_STATEMENTS).strip()
                head = re.match(r"Lemma \w+_accepted :\s*", text)
                body = text[head.end():] if head else ""
                p14_lemmas[m.group(1)] = (body[:-1] if body.endswith(".") else body).rstrip()
    for _, path, name, prop in INVENTORY_P14:
        base = name[: -len("_statement")] if name.endswith("_statement") else name
        fun = re.match(r"fun\s+(.*?)\s*=>\s*(.*)\Z", prop, re.S)
        want = code(f"forall {fun.group(1)}, {fun.group(2)}" if fun else prop,
                    f"INVENTORY_P14 {name}").strip()
        if base not in p14_lemmas:
            failures.append(f"{PHASE14_STATEMENTS}: no lemma {base}_accepted for "
                            f"the accepted statement {name} of {path}")
        elif p14_lemmas[base] != want:
            failures.append(f"{PHASE14_STATEMENTS}: {base}_accepted does not state "
                            f"the accepted proposition of {name}")

    # Rule 30 (e): the inventory of the identity queries, the drivers, and
    # Declare ML Module in the drivers only.
    snapshot_texts = {}
    for path in sorted((ROOT / "check" / "snapshots").glob("Snapshot*.v")):
        text = read(str(path.relative_to(ROOT)))
        if text is not None:
            snapshot_texts[path.stem] = text
    try:
        derived = identity_sidecars.inventory(snapshot_texts)
    except ValueError as err:
        failures.append(f"check/snapshots/: {err}")
        derived = None
    identity_inventory = None
    inventory_data = read(IDENTITY_INVENTORY, binary=True)
    if inventory_data is not None:
        try:
            identity_inventory = json.loads(inventory_data)
        except ValueError:
            failures.append(f"{IDENTITY_INVENTORY}: not JSON")
    if derived is not None and identity_inventory is not None:
        if identity_inventory != derived:
            failures.append(f"{IDENTITY_INVENTORY}: differs from the queries that the "
                            "snapshot files of check/snapshots/ print")
        if sorted(derived["snapshots"]) != sorted(IDENTITY_REFERENCES):
            failures.append("IDENTITY_REFERENCES: not exactly the snapshots that print "
                            "a declaration")
        queries = [q for e in derived["snapshots"].values() for q in e["queries"]]
        parts = sum(len(q["parts"]) for q in queries)
        if (len(queries), parts) != (IDENTITY_QUERIES, IDENTITY_PARTS):
            failures.append(f"{IDENTITY_INVENTORY}: {len(queries)} queries in {parts} parts, "
                            f"not {IDENTITY_QUERIES} in {IDENTITY_PARTS}")
        for name, entry in derived["snapshots"].items():
            path = f"check/identity/Identity{name}.v"
            text = read(path)
            if text is None:
                continue
            fixed_rules(path, text)
            if text != identity_sidecars.driver_text(name, entry):
                failures.append(f"{path}: differs from the driver generated from "
                                f"{IDENTITY_INVENTORY}")
    drivers = {f"check/identity/Identity{name}.v" for name in IDENTITY_REFERENCES}
    for path in sorted((ROOT / "check").rglob("*.v")):
        rel = str(path.relative_to(ROOT))
        if rel.startswith("check/regression/") or rel in drivers:
            continue
        text = read(rel)
        for _, _, command, _, _ in (sentences(text, rel) or []) if text is not None else []:
            if re.match(r"Declare ML Module\b", command):
                failures.append(f"{rel}: Declare ML Module outside the identity drivers "
                                "of check/identity/")

    # Rule 30 (b): the build configuration, the scripts and the build
    # products.
    for path, digest in FIXED_FILES.items():
        data = read(path, binary=True)
        if data is not None and sha256_hex(data) != digest:
            failures.append(f"{path}: differs from the content fixed by FIXED_FILES")
    for path in ABSENT_FILES:
        if present_exact(path):
            failures.append(f"{path}: must not exist; make, or the Makefile.rocq that "
                            "it generates, would read it")
    present = sorted(str(p.relative_to(ROOT / "scripts"))
                     for p in (ROOT / "scripts").rglob("*") if p.is_file() or p.is_symlink())
    for extra in sorted(set(present) - set(SCRIPTS)):
        failures.append(f"scripts/{extra}: not a file of SCRIPTS; scripts/ holds exactly "
                        "those (a stale scripts/__pycache__ must be deleted)")
    for absent in sorted(set(SCRIPTS) - set(present)):
        failures.append(f"scripts/{absent}: missing")
    project = read("_CoqProject")
    if project is not None:
        options = [line for line in project.splitlines()
                   if line.strip() and not line.endswith(".v")]
        if options != COQPROJECT_OPTIONS:
            failures.append("_CoqProject: its option lines differ from COQPROJECT_OPTIONS")
        for line in project.splitlines():
            if line.endswith(".v") and not re.fullmatch(
                    r"(theories|library|extension|applications)/[A-Za-z0-9_/]+\.v", line):
                failures.append(f"_CoqProject: {line!r} is not a source file of the "
                                "four source directories")
    tracked = subprocess.run(["git", "-C", str(ROOT), "ls-files"], capture_output=True,
                             text=True, check=True).stdout.splitlines()
    for path in tracked:
        if re.search(r"\.(vo|vos|vok|glob|aux|pyc)$|(^|/)Makefile\.rocq(\.conf)?$|"
                     r"(^|/)\.Makefile\.rocq\.d$|^build/|(^|/)__pycache__/", path):
            failures.append(f"{path}: a build product is tracked by git")

    # Rules 2 and 3, with the bans of rule 30 (a).
    for top, scope in (("theories", "all"), ("library", "library"), ("extension", "library"),
                       ("applications", "library")):
        for rel in sources:
            if not rel.startswith(top + "/"):
                continue
            text = read(rel)
            if text is not None:
                failures.extend(forbidden(text, rel, scope))
    library = [ROOT / source for source in sources if source.startswith("library/")]
    applications = [ROOT / source for source in sources if source.startswith("applications/")]
    for path in library + applications:
        rel = str(path.relative_to(ROOT))
        text = read(rel)
        if text is None:
            continue
        for root, name in requires(text, rel):
            full = f"{root}.{name}" if root else name
            parts = full.split(".")
            stdlib = root.startswith(("Stdlib", "Coq")) or not root
            if PAPERS & set(parts):
                failures.append(f"{rel}: requires {full} of a paper")
            elif path in library and APPLICATIONS in parts:
                failures.append(f"{rel}: requires {full} of applications/")
            elif stdlib and (any(STDLIB_REALS.match(p) for p in parts) or "Reals" in parts):
                failures.append(f"{rel}: requires Stdlib's {full}")
            elif set(parts) & MATHCOMP_BRIDGE:
                failures.append(f"{rel}: requires {full}")

    # Rule 30 (b): every rule above reads the sources only. They hold before
    # anything compiles: make check runs this script with --before-build
    # first, and the runner starts only if they hold, since a source that
    # breaks them can run code while Rocq compiles it (E37).
    static = failures + LEX_FAILURES
    for line in static:
        print(line)
    if static:
        sys.exit(1)
    if args.before_build:
        print(f"the sources follow the rules of scripts/check_sources.py "
              f"({len(library)} library modules, {len(applications)} modules of "
              f"applications/); nothing was compiled")
        return
    del LEX_FAILURES[:]

    # Rule 30 (b): the run. The checker creates the run identifier and starts
    # the runner; then only the outputs of this run are read.
    run_id = args.reuse
    if run_id is None:
        run_id = secrets.token_hex(16)
        runner = subprocess.run([sys.executable, "-I", "-B", str(ROOT / "scripts" / "run_checks.py"),
                                 "--run-id", run_id, "--jobs", str(args.jobs)], cwd=ROOT)
        if runner.returncode != 0:
            failures.append(f"scripts/run_checks.py: exited with status {runner.returncode}; "
                            "no output of this run is read")
    outputs, errors = {}, {}
    manifest = None
    if (ROOT / MANIFEST).exists():
        try:
            manifest = json.loads((ROOT / MANIFEST).read_text())
        except ValueError:
            failures.append(f"{MANIFEST}: not a manifest of scripts/run_checks.py")
    elif not failures or args.reuse:
        failures.append(f"{MANIFEST}: missing")
    if manifest is not None:
        if manifest.get("run_id") != run_id:
            failures.append(f"{MANIFEST}: written by another run of scripts/run_checks.py")
        if manifest.get("rocq") != ROCQ_VERSION:
            failures.append(f"{MANIFEST}: compiled with {manifest.get('rocq')!r}, "
                            f"not {ROCQ_VERSION!r}")
        if manifest.get("packages") != PACKAGES:
            failures.append(f"{MANIFEST}: installed packages {manifest.get('packages')}, "
                            f"not {PACKAGES}")
        entries = manifest.get("checks", [])
        want = [(c.source, list(c.flags), f"build/checks/{Path(c.source).stem}.out")
                for c in CHECK_FILES]
        got = [(e.get("source"), e.get("flags"), e.get("output")) for e in entries]
        if got != want:
            failures.append(f"{MANIFEST}: the checks compiled are not those of CHECK_FILES, "
                            "with their flags and outputs, in order")
        listed = {MANIFEST}
        for entry in entries:
            src = entry.get("source")
            src_data = read(src, binary=True)
            if src_data is not None and sha256_hex(src_data) != entry.get("source_sha256"):
                failures.append(f"{src}: changed since scripts/run_checks.py compiled it")
            for key, store in (("output", outputs), ("stderr", errors)):
                path = entry.get(key)
                listed.add(path)
                data = read(path, binary=True)
                if data is None:
                    continue
                if sha256_hex(data) != entry.get(key + "_sha256"):
                    failures.append(f"{path}: not the file that scripts/run_checks.py wrote")
                else:
                    store[src] = data.decode("utf-8", "replace")
        ident = manifest.get("identity", {})
        if ident.get("ocaml") != OCAML_VERSION or ident.get("findlib") != FINDLIB_VERSION:
            failures.append(f"{MANIFEST}: the exporter was built by ocamlopt "
                            f"{ident.get('ocaml')!r} and findlib {ident.get('findlib')!r}, not "
                            f"{OCAML_VERSION} and {FINDLIB_VERSION}")
        if ident.get("recipe_sha256") != identity_sidecars.recipe_sha256():
            failures.append(f"{MANIFEST}: the exporter was not built by the recipe of "
                            "scripts/identity_sidecars.py")
        plugin = ident.get("plugin")
        listed.add(plugin)
        data = read(plugin, binary=True) if plugin else None
        if data is None or sha256_hex(data) != ident.get("plugin_sha256"):
            failures.append(f"{MANIFEST}: the exporter plugin is not the file that "
                            "scripts/run_checks.py built")
        meta_data = read(IDENTITY_META, binary=True)
        try:
            meta = json.loads(meta_data) if meta_data is not None else {}
        except ValueError:
            meta = {}
            failures.append(f"{IDENTITY_META}: not JSON")
        for name in IDENTITY_REFERENCES:
            if meta.get(name, {}).get("exporter", {}).get("plugin_sha256") \
                    != ident.get("plugin_sha256"):
                failures.append(f"{IDENTITY_META}: the reference of {name} was not written by "
                                "the plugin of this run")
        kernel = manifest.get("kernel", {})
        expected_modules = kernel_source_modules(sources)
        expected_modules += [f"Checks.{Path(c.source).stem}" for c in CHECK_FILES]
        if kernel.get("modules") != expected_modules:
            failures.append(f"{MANIFEST}: rocqchk did not check exactly the modules of "
                            "library/, theories/, extension/, applications/ and the check files")
        path = kernel.get("output")
        listed.add(path)
        data = read(path, binary=True) if path else None
        if data is not None and sha256_hex(data) != kernel.get("output_sha256"):
            failures.append(f"{path}: not the file that scripts/run_checks.py wrote")
        elif data is not None:
            failures.extend(kernel_failures(data.decode("utf-8", "replace")))
        for path, digest in manifest.get("other_files", {}).items():
            listed.add(path)
            data = read(path, binary=True)
            if data is not None and sha256_hex(data) != digest:
                failures.append(f"{path}: not the file that scripts/run_checks.py wrote")
        for path in sorted((ROOT / "build" / "checks").rglob("*")):
            rel = str(path.relative_to(ROOT))
            if path.is_file() and rel not in listed:
                failures.append(f"{rel}: a file of build/checks/ that the manifest does "
                                "not list")

    # Rule 30 (c), (d): each output has exactly what its check must print.
    allowed = axiom_names(read("check/assumptions.expected") or "")
    allowed_p13 = axiom_names(read(SEVEN_AXIOMS) or "")
    allowed_universality = axiom_names(read("check/universality_assumptions.expected") or "")
    for name in sorted(allowed_universality - allowed):
        failures.append(f"check/universality_assumptions.expected: {name} "
                        "is not among check/assumptions.expected")
    lists = {}
    for name, expected in EXPECTED_LISTS.items():
        lists[expected] = axiom_names(read(expected) or "")
        for ax in sorted(lists[expected] - allowed):
            failures.append(f"{expected}: {ax} is not among check/assumptions.expected")
    for name, check, check_code, expected in (PHASE13_THEOREMS + PHASE14_THEOREMS
                                              + SHIFTED_THEOREMS):
        for ax in sorted(lists[expected] - allowed_p13):
            failures.append(f"{expected}: {ax} is not among {SEVEN_AXIOMS}")
    lists[SEVEN_AXIOMS] = allowed_p13
    for check in CHECK_FILES:
        if check.source not in outputs:
            if manifest is not None:
                failures.append(f"{check.source}: no output of it in this run")
            continue
        text, kind = outputs[check.source], check.expect[0]
        if UNSAFE.search(text):
            failures.append(f"{check.source}: its output reports an unsafe construction: "
                            f"{UNSAFE.search(text).group(0)!r}")
        if kind == "snapshot":
            ref_path, digest = check.expect[1], check.expect[2]
            ref = read(ref_path, binary=True)
            if errors.get(check.source):
                failures.append(f"{check.source}: Rocq wrote to the standard error: "
                                f"{errors[check.source].splitlines()[0][:100]!r}")
            if "..." in text:
                failures.append(f"{check.source}: the output holds the elision token ...")
            if ref is None:
                continue
            if sha256_hex(ref) != digest:
                failures.append(f"{ref_path}: differs from the reference fixed by "
                                "CHECK_FILES; a reference is never regenerated to make an "
                                "output pass")
            elif text.encode() != ref:
                diff = [f"line {k + 1}: {a[:90]!r} / {b[:90]!r}"
                        for k, (a, b) in enumerate(zip(text.splitlines(),
                                                       ref.decode().splitlines())) if a != b][:3]
                failures.append(f"{check.source}: the snapshot differs from {ref_path}"
                                + (": " + "; ".join(diff) if diff else ": lengths differ"))
            continue
        if kind == "identity":
            ref_path, digest = check.expect[1], check.expect[2]
            ref = read(ref_path, binary=True)
            if errors.get(check.source):
                failures.append(f"{check.source}: Rocq wrote to the standard error: "
                                f"{errors[check.source].splitlines()[0][:100]!r}")
            if ref is None or identity_inventory is None:
                continue
            if sha256_hex(ref) != digest:
                failures.append(f"{ref_path}: differs from the reference fixed by "
                                "IDENTITY_REFERENCES; a reference is never regenerated to "
                                "make an output pass")
                continue
            raw = read(check.output, binary=True)
            if raw is None:
                continue
            try:
                # Strict: an invalid sequence fails, never a replacement.
                text = identity_sidecars.decode_output(raw)
            except ValueError as err:
                failures.append(f"{check.output}: {err}")
                continue
            name = Path(check.source).stem[len("Identity"):]
            queries = identity_inventory.get("snapshots", {}).get(name, {}).get("queries")
            if queries is None:
                failures.append(f"{check.source}: no queries in {IDENTITY_INVENTORY}")
                continue
            try:
                got = identity_sidecars.sidecar_bytes(name, text, queries)
            except ValueError as err:
                failures.append(f"{check.source}: its output is not the framed export of "
                                f"its queries: {err}")
                continue
            if got != ref:
                failures.append(f"{check.source}: the references differ from {ref_path}: "
                                + "; ".join(identity_sidecars.first_differences(ref, got)))
            continue
        items = parse_output(text)
        others = [value for what, value in items if what == "other"]
        if others:
            failures.append(f"{check.source}: unexpected output {others[0][:100]!r}")
            continue
        if kind == "empty":
            if items:
                failures.append(f"{check.source}: must print nothing")
            continue
        if kind == "reports":
            count, allowed_path = check.expect[1], check.expect[2]
            reports = [value for what, value in items if what == "report"]
            if len(items) != count or len(reports) != count:
                failures.append(f"{check.source}: {len(reports)} complete axiom reports and "
                                f"{len(items) - len(reports)} other items, {count} reports "
                                "required")
            for axioms in reports:
                for ax in sorted(axioms - lists[allowed_path]):
                    failures.append(f"{check.source}: {ax} is not among {allowed_path}")
            continue
        pairs = check.expect[1]
        want_items = []
        for marker, allowed_path, label in pairs:
            if marker is not None:
                want_items.append(("marker", marker))
            want_items.append(("report", allowed_path, label))
        if len(items) != len(want_items):
            failures.append(f"{check.source}: {len(items)} markers and reports, "
                            f"{len(want_items)} required")
            continue
        for got_item, want_item in zip(items, want_items):
            if got_item[0] != want_item[0]:
                failures.append(f"{check.source}: a {got_item[0]} where a {want_item[0]} "
                                "is required")
                break
            if want_item[0] == "marker" and got_item[1] != want_item[1]:
                failures.append(f"{check.source}: the report of {got_item[1]} where that of "
                                f"{want_item[1]} is required")
                break
            if want_item[0] == "report":
                for ax in sorted(got_item[1] - lists[want_item[1]]):
                    failures.append(f"{want_item[2]}: {ax} is not among {want_item[1]}")

    # Rule 30 (d): the protection closure. Each project constant that the
    # snapshot of a frozen or accepted statement names (resolved by Locate at
    # its acceptance commit, check/snapshots/REFERENCES.json) is defined in a
    # frozen file, lies in a pinned section, or is named by the snapshot of a
    # characterization lemma.
    refs_text = read(REFERENCES)
    if refs_text is not None:
        refs = json.loads(refs_text)
        characterized = {full for name in CHARACTERIZATION_SNAPSHOTS
                         for full in refs.get(name, {}).get("project_names", {}).values()}
        for name, data in sorted(refs.items()):
            if name in CHARACTERIZATION_SNAPSHOTS:
                continue
            for printed, full in sorted(data.get("project_names", {}).items()):
                if full in SNAPSHOT_SUBJECTS.get(name, ()):
                    continue
                module = ".".join(full.split(".")[:-1])
                if any(module == m or module.startswith(m + ".") for m in FROZEN_MODULES) \
                        or full in PINNED_NAMES or full in characterized:
                    continue
                failures.append(f"{REFERENCES}: the snapshot {name} names {full} ({printed}), "
                                "which is neither defined in a frozen file, nor in a pinned "
                                "section, nor named by a characterization snapshot")
    # Rule 30 (e): the same closure over the kernel names of the references.
    found_names = {}
    for name in IDENTITY_REFERENCES:
        ref_path = f"check/identity/Identity{name}.json"
        data = read(ref_path, binary=True)
        if data is None:
            continue
        try:
            found_names[name] = identity_sidecars.referenced_names(json.loads(data))
        except (ValueError, KeyError, TypeError, IndexError):
            failures.append(f"{ref_path}: not an identity sidecar")
    roots = tuple(r.rstrip(".") for r in PROJECT_ROOTS)
    check_modules = {f"Checks.{Path(c.source).stem}" for c in CHECK_FILES}
    for name, target, full, kind in identity_sidecars.unprotected(
            found_names, CHARACTERIZATION_SNAPSHOTS, SNAPSHOT_SUBJECTS, set(FROZEN_MODULES),
            set(PINNED_NAMES), check_modules, roots):
        failures.append(f"check/identity/Identity{name}.json: {target} references {full} "
                        f"({kind}), which is neither defined in a frozen file, nor pinned, "
                        "nor referenced by a characterization snapshot")

    failures = failures + LEX_FAILURES
    for line in failures:
        print(line)
    if failures:
        sys.exit(1)
    print(f"the frozen files of phases 1 to 14 and of step 18 unchanged since their "
          f"acceptance commits; "
          f"the pinned check files unchanged; the sections tuple_prod and lambda_max "
          f"unchanged; the code-fixed check files at their fixed code; "
          f"{len(INVENTORY)} accepted general statements in the inventory, each stated and "
          f"proved in {LIBRARY_STATEMENTS}, and {len(INVENTORY_P14)} of phase 14 in "
          f"{PHASE14_STATEMENTS}; no forbidden command; "
          f"{len(library)} library modules and {len(applications)} modules of applications/ "
          f"with allowed imports; {len(CHECK_FILES)} check files compiled by "
          f"scripts/run_checks.py in run {run_id}, each output as required "
          f"({len(THEOREMS)} theorem reports, "
          f"{len(THEOREM_IDENTITIES) + len(PHASE14_IDENTITIES) + len(SHIFTED_IDENTITIES)} "
          f"identities, "
          f"{len(MARKED_REPORTS) + len(PHASE14_REPORTS) + len(SHIFTED_REPORTS) + 1} "
          f"identified reports, "
          f"{sum(1 for c in CHECK_FILES if c.expect[0] == 'snapshot')} snapshots equal to "
          f"their references, the references of "
          f"{sum(1 for c in CHECK_FILES if c.expect[0] == 'identity')} identity drivers "
          f"equal to theirs); the build configuration and the scripts as fixed")


if __name__ == "__main__":
    main()
