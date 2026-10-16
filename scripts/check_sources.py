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
   PHASE6_THEOREMS to PHASE13_THEOREMS and of SHIFTED_THEOREMS, 35 in all
   since rule 31), and a missing or extra report makes it fail.
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
30. The shifted-Gaussian proof, the freeze. The code of each file of
   SHIFTED_FROZEN, the seven statement files extension/Shifted<X>Statement.v
   (X = Condition, Gaussian, Quadric, Error, MixtureUnsat, MixtureSat and
   Sign), must equal its code at the commit SHIFTED_BASELINE, at which the
   user accepted them. The project definitions that these statements unfold
   to and that the earlier rules do not protect are protected by
   check/ShiftedDefinitions.v, which states a characterization of each,
   written out down to the definitions of MathComp, MathComp-Analysis and
   Stdlib, to the frozen files, to the section tuple_prod and to the
   definitions that check/ApplicationsDefinitions.v characterizes, and
   proves it by computation: family_sequence_limit, coordinate_support,
   quadric_eval, tuple_map, mixture_weights, mixture, cmixture_weights,
   cmixture, row_symmetric_law, row_shift, row_shift_law,
   sign_shift_weights, sign_shift_law, row_outer, row_of_tuple, point_law,
   sample_row_tuple, sample_flat_row, sample_flat_col, sample_of_row_tuple,
   sample_translate, translation_fitting_error, gaussian_small_shift,
   finite_row_law, countable_row_law, row_sample_map, iid_row_sample_law,
   shifted_iid_sample_law and sign_mixture_sample_law. The constants
   generated for them (canonical instances, mixins, factories and Let
   subproofs) are fixed through the values that these characterizations
   compute. The code of check/ShiftedDefinitions.v is fixed: it must equal
   SHIFTED_DEFINITIONS_CHECK. make check deletes its output,
   build/shifted_definitions.txt, then compiles the file into it; the
   output is required: it must exist and be a complete axiom report whose
   axioms are among those of check/sat_variance_assumptions.expected. The
   Makefile must hold the two commands of SHIFTED_MAKE_LINES, the deletion
   of the output and the compilation, so that an old output cannot stand
   for a new one.
31. The shifted-Gaussian proof, the axiom checks. The seven check files of
   SHIFTED_THEOREMS, check/ShiftedConditionAssumptions.v,
   check/ShiftedGaussianAssumptions.v, check/ShiftedQuadricAssumptions.v,
   check/ShiftedErrorAssumptions.v, check/ShiftedMixtureUnsatAssumptions.v,
   check/ShiftedMixtureSatAssumptions.v and check/ShiftedSignAssumptions.v,
   have the codes of SHIFTED_CHECKS. Each is in the identity form of rule
   29: it requires the frozen statement module and the theorem module of a
   target (S1 to S7) without Import, defines shifted_<x>_identity with the
   frozen statement as its type and the theorem as its body, both by their
   absolute names, and prints the full name of that definition (Locate) and
   its axioms, which must be among those of its expected list,
   check/shifted_<x>_assumptions.expected; the axioms of each of the seven
   lists must be among the seven of check/sat_variance_assumptions.expected
   (no Classical_Prop.classic). The script then takes 35 reports, one per
   theorem of THEOREMS. check/ShiftedIdentities.v has the code
   SHIFTED_IDENTITIES_CHECK: it requires the fourteen modules without
   Import, defines the seven identities in the same form, and bundles them
   in the definition shifted_identities, whose type is the conjunction of
   the seven frozen statements, so that one compiled file checks the seven
   theorems against their frozen statements. make check deletes its output,
   build/shifted_identities.txt, then compiles the file into it; the output
   is required: it must exist and be a complete axiom report whose axioms
   are among those of check/sat_variance_assumptions.expected. The Makefile
   must hold the two commands of SHIFTED_MAKE_LINES_P, the deletion of the
   output and the compilation.

`make check` runs this script after the build. It exits 1 on any failure.
"""

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from export_from_ellipsoid_rocq import strip_comments  # noqa: E402

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
PHASE13_DEFINITIONS = "check/Phase13Definitions.v"
PHASE13_DEFINITIONS_OUTPUT = "build/phase13_definitions.txt"
# The commands of the Makefile that delete and regenerate the output.
PHASE13_MAKE_LINES = [
    "rm -f $(REPORTS) build/applications_definitions.txt "
    "build/phase13_definitions.txt",
    "rocq compile -noglob -w -notation-overridden -w -ambiguous-paths "
    "-w -notation-incompatible-prefix -w -hiding-delimiting-key -Q library "
    "GaussianAnalysis -o build/Phase13Definitions.vo "
    "check/Phase13Definitions.v > build/phase13_definitions.txt",
]
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
LIBRARY_STATEMENTS = "check/LibraryStatements.v"
LIBRARY_STATEMENTS_OUTPUT = "build/library_statements.txt"
LIBRARY_STATEMENTS_CHECK = (
    'Set Warnings "-require-in-module". Module accepted_finite_mean. Fr'
    'om HB Require Import structures. From mathcomp Require Import all_'
    'ssreflect_compat ssralg ssrnum. From mathcomp Require Import arith'
    'metic_tactic ring_tactic. Import Order.TTheory GRing.Theory Num.Th'
    'eory. Local Open Scope ring_scope. Require Import GaussianAnalysis'
    '.probability.finite_mean. Lemma unif_mean_union_accepted : forall '
    '(R : realFieldType) (T I : finType) (P : I -> pred T), @unif_mean '
    'R T (fun x : T => [exists i, P i x]%:R : R) <= \\sum_i @unif_mean R'
    ' T (fun x : T => (P i x)%:R : R). Proof. exact: @unif_mean_union. '
    'Qed. Lemma unif_mean_indicatorN_accepted : forall (R : realFieldTy'
    'pe) (T : finType) (P : pred T), (0 < #|T|)%N -> @unif_mean R T (fu'
    'n x : T => (~~ P x)%:R : R) = 1 - @unif_mean R T (fun x : T => (P '
    'x)%:R : R). Proof. exact: @unif_mean_indicatorN. Qed. Lemma unif_m'
    'ean_markov_accepted : forall (R : realFieldType) (T : finType) (f '
    ': T -> R) (t : R), (forall x : T, 0 <= f x) -> t * @unif_mean R T '
    '(fun x : T => (t <= f x)%R%:R : R) <= @unif_mean R T f. Proof. exa'
    'ct: @unif_mean_markov. Qed. Lemma unif_mean_cutoff_accepted : fora'
    'll (R : realFieldType) (T : finType) (f : T -> R) (M t : R), 0 <= '
    't -> (forall x : T, f x <= M) -> @unif_mean R T f <= t + M * @unif'
    '_mean R T (fun x : T => (t <= f x)%R%:R : R). Proof. exact: @unif_'
    'mean_cutoff. Qed. Lemma unif_chebyshev_accepted : forall (R : real'
    'FieldType) (T : finType) (f : T -> R) (t : R), 0 < t -> @unif_mean'
    ' R T (fun x : T => (t <= `|f x - @unif_mean R T f|)%R%:R : R) <= @'
    'unif_var R T f / t ^+ 2. Proof. exact: @unif_chebyshev. Qed. Lemma'
    ' unif_mean_tuple_prod_ord_accepted : forall (R : realFieldType) (T'
    " : finType) (m : nat) (g : 'I_m -> T -> R), @unif_mean R (tuple_tu"
    'ple_of__canonical__fintype_Finite m T) (fun t : m.-tuple T => \\pro'
    'd_(i < m) g i (@tnth m T t i)) = \\prod_(i < m) @unif_mean R T (g i'
    '). Proof. exact: @unif_mean_tuple_prod_ord. Qed. Lemma unif_mean_t'
    'uple_prod_set_accepted : forall (R : realFieldType) (T : finType) '
    "(m : nat) (J : {set 'I_m}) (g : T -> R), (0 < #|T|)%N -> @unif_mea"
    'n R (tuple_tuple_of__canonical__fintype_Finite m T) (fun t : m.-tu'
    'ple T => \\prod_(i in J) g (@tnth m T t i)) = @unif_mean R T g ^+ #'
    '|J|. Proof. exact: @unif_mean_tuple_prod_set. Qed. End accepted_fi'
    'nite_mean. Module accepted_binomial_mean. From HB Require Import s'
    'tructures. From mathcomp Require Import all_ssreflect_compat ssral'
    'g ssrnum. From mathcomp Require Import boolp classical_sets reals '
    'ereal measure numfun. From mathcomp Require Import lebesgue_integr'
    'al binomial_distribution. From mathcomp Require Import ring_tactic'
    '. From GaussianAnalysis.probability Require Import finite_mean. Im'
    'port Order.TTheory GRing.Theory Num.Theory. Local Open Scope ring_'
    'scope. Require Import GaussianAnalysis.probability.binomial_mean. '
    'Lemma binomial_mean0_accepted : forall (R : numDomainType) (p : R)'
    ' (f : nat -> R), @binomial_mean R 0 p f = f 0%N. Proof. exact: @bi'
    'nomial_mean0. Qed. Lemma binomial_meanS_accepted : forall (R : num'
    'DomainType) (m : nat) (p : R) (f : nat -> R), @binomial_mean R m.+'
    '1 p f = (1 - p) * @binomial_mean R m p f + p * @binomial_mean R m '
    'p (fun j : nat => f j.+1). Proof. exact: @binomial_meanS. Qed. Lem'
    'ma eq_binomial_mean_accepted : forall (R : numDomainType) (m : nat'
    ') (p : R) (f g : nat -> R), (forall j : nat, (j <= m)%N -> f j = g'
    ' j) -> @binomial_mean R m p f = @binomial_mean R m p g. Proof. exa'
    'ct: @eq_binomial_mean. Qed. Lemma binomial_mean_cst_accepted : for'
    'all (R : numDomainType) (m : nat) (p c : R), @binomial_mean R m p '
    '(fun=> c) = c. Proof. exact: @binomial_mean_cst. Qed. Lemma binomi'
    'al_meanD_accepted : forall (R : numDomainType) (m : nat) (p : R) ('
    'f g : nat -> R), @binomial_mean R m p (fun j : nat => f j + g j) ='
    ' @binomial_mean R m p f + @binomial_mean R m p g. Proof. exact: @b'
    'inomial_meanD. Qed. Lemma binomial_meanZ_accepted : forall (R : nu'
    'mDomainType) (m : nat) (p c : R) (f : nat -> R), @binomial_mean R '
    'm p (fun j : nat => c * f j) = c * @binomial_mean R m p f. Proof. '
    'exact: @binomial_meanZ. Qed. Lemma ler_binomial_mean_accepted : fo'
    'rall (R : numDomainType) (m : nat) (p : R) (f g : nat -> R), 0 <= '
    'p <= 1 -> (forall j : nat, (j <= m)%N -> f j <= g j) -> @binomial_'
    'mean R m p f <= @binomial_mean R m p g. Proof. exact: @ler_binomia'
    'l_mean. Qed. Lemma binomial_mean_id_accepted : forall (R : numDoma'
    'inType) (m : nat) (p : R), @binomial_mean R m p [eta @Algebra.natm'
    'ul R 1] = m%:R * p. Proof. exact: @binomial_mean_id. Qed. Lemma bi'
    'nomial_mean_sqr_dev_accepted : forall (R : numDomainType) (m : nat'
    ') (p : R), @binomial_mean R m p (fun j : nat => (j%:R - m%:R * p) '
    '^+ 2) = m%:R * p * (1 - p). Proof. exact: @binomial_mean_sqr_dev. '
    'Qed. Lemma binomial_chebyshev_accepted : forall (R : realFieldType'
    ') (m : nat) (p t : R), 0 <= p <= 1 -> 0 < t -> @binomial_mean R m '
    'p (fun j : nat => (t <= `|j%:R - m%:R * p|)%R%:R) <= m%:R * p * (1'
    ' - p) / t ^+ 2. Proof. exact: @binomial_chebyshev. Qed. Lemma bino'
    'mial_mean_last_accepted : forall (R : numDomainType) (m : nat) (p '
    ': R) (f : nat -> R), 0 <= p <= 1 -> (forall j : nat, (j <= m)%N ->'
    ' 0 <= f j) -> p ^+ m * f m <= @binomial_mean R m p f. Proof. exact'
    ': @binomial_mean_last. Qed. Lemma binomial_mean_trials_accepted : '
    "forall (R : numDomainType) (m m' : nat) (p : R) (f : nat -> R), 0 "
    "<= p <= 1 -> {homo f : i j / (i <= j)%N >-> i <= j} -> (m <= m')%N"
    " -> @binomial_mean R m p f <= @binomial_mean R m' p f. Proof. exac"
    't: @binomial_mean_trials. Qed. Lemma unif_mean_binomial_mean_accep'
    'ted : forall (R : realFieldType) (T : finType) (m : nat) (p : R) ('
    'f : nat -> T -> R), @unif_mean R T (fun x : T => @binomial_mean R '
    'm p (f^~ x)) = @binomial_mean R m p (fun j : nat => @unif_mean R T'
    ' (f j)). Proof. exact: @unif_mean_binomial_mean. Qed. Lemma binomi'
    'al_meanE_accepted : forall (R : realType) (m : nat) (p : R) (f : n'
    'at -> R), @binomial_mean R m p f = \\sum_(j < m.+1) @binomial_pmf R'
    ' m p (nat_of_ord j) * f (nat_of_ord j). Proof. exact: @binomial_me'
    'anE. Qed. Lemma integral_binomial_mean_accepted : forall (R : real'
    'Type) (m : nat) (p : R) (f : nat -> R), 0 <= p <= 1 -> (\\int[@bino'
    'mial_prob R m p]_j (f j)%:E)%E = (@binomial_mean R m p f)%:E. Proo'
    'f. exact: @integral_binomial_mean. Qed. End accepted_binomial_mean'
    '. Module accepted_commuting_operators. From HB Require Import stru'
    'ctures. From mathcomp Require Import all_ssreflect_compat ssralg s'
    'srnum boolp. From GaussianAnalysis.probability Require Import fini'
    'te_mean binomial_mean. Import Order.TTheory GRing.Theory Num.Theor'
    'y. Local Open Scope ring_scope. Require Import GaussianAnalysis.pr'
    'obability.commuting_operators. Lemma homo_iter_accepted : forall ('
    'disp : Order.disp_t) (T : preorderType disp) (A : T -> T) (m : nat'
    '), {homo A : x y / (x <= y)%O} -> {homo @iter T m A : x y / (x <= '
    'y)%O}. Proof. exact: @homo_iter. Qed. Lemma iter_le_subcomm_accept'
    'ed : forall (disp : Order.disp_t) (T : preorderType disp) (A B : T'
    ' -> T) (x : T), {homo A : y z / (y <= z)%O} -> {homo B : y z / (y '
    '<= z)%O} -> (forall y : T, (B (A y) <= A (B y))%O) -> (B x <= A x)'
    '%O -> forall m : nat, (@iter T m B x <= @iter T m A x)%O. Proof. e'
    'xact: @iter_le_subcomm. Qed. Lemma monotone_iter_le_accepted : for'
    'all (R : numDomainType) (X : Type) (A B : (X -> R) -> X -> R) (f :'
    ' X -> R), @monotone_op R X A -> @monotone_op R X B -> (forall (g :'
    ' X -> R) (x : X), B (A g) x <= A (B g) x) -> (forall x : X, B f x '
    '<= A f x) -> forall (m : nat) (x : X), @iter (X -> R) m B f x <= @'
    'iter (X -> R) m A f x. Proof. exact: @monotone_iter_le. Qed. Lemma'
    ' iter_scale_accepted : forall (R : numDomainType) (X : Type) (A : '
    '(X -> R) -> X -> R) (c : R), @linear_op R X A -> forall (m : nat) '
    '(f : X -> R) (x : X), @iter (X -> R) m (fun (g : X -> R) (y : X) ='
    '> c * A g y) f x = c ^+ m * @iter (X -> R) m A f x. Proof. exact: '
    '@iter_scale. Qed. Lemma iter_mix_binomial_accepted : forall (R : n'
    'umDomainType) (X : Type) (A B : (X -> R) -> X -> R) (p : R), @line'
    'ar_op R X A -> @linear_op R X B -> (forall f : X -> R, A (B f) = B'
    ' (A f)) -> forall (m : nat) (f : X -> R) (x : X), @iter (X -> R) m'
    ' (fun (g : X -> R) (y : X) => p * A g y + (1 - p) * B g y) f x = @'
    'binomial_mean R m p (fun j : nat => @iter (X -> R) j A (@iter (X -'
    '> R) (m - j) B f) x). Proof. exact: @iter_mix_binomial. Qed. Lemma'
    ' binomial_mix_le_iter_accepted : forall (R : numDomainType) (X : T'
    'ype) (A B C : (X -> R) -> X -> R) (p : R) (f : X -> R), 0 <= p <= '
    '1 -> @linear_op R X A -> @linear_op R X B -> @linear_op R X C -> @'
    'monotone_op R X A -> @monotone_op R X B -> @monotone_op R X C -> ('
    'forall g : X -> R, A (B g) = B (A g)) -> (forall (g : X -> R) (x :'
    ' X), A (C g) x <= C (A g) x) -> (forall (g : X -> R) (x : X), B (C'
    ' g) x <= C (B g) x) -> (forall x : X, p * A f x + (1 - p) * B f x '
    '<= C f x) -> forall (m : nat) (x : X), @binomial_mean R m p (fun j'
    ' : nat => @iter (X -> R) j A (@iter (X -> R) (m - j) B f) x) <= @i'
    'ter (X -> R) m C f x. Proof. exact: @binomial_mix_le_iter. Qed. Le'
    'mma meet_avg_linear_accepted : forall (R : realFieldType) (T C : f'
    'inType) (E : C -> {set T}), @linear_op R {set T} (@meet_avg R T C '
    'E). Proof. exact: @meet_avg_linear. Qed. Lemma meet_avg_monotone_a'
    'ccepted : forall (R : realFieldType) (T C : finType) (E : C -> {se'
    't T}), @monotone_op R {set T} (@meet_avg R T C E). Proof. exact: @'
    'meet_avg_monotone. Qed. Lemma meet_avg_cst_accepted : forall (R : '
    'realFieldType) (T C : finType) (E : C -> {set T}) (a : R) (S0 : {s'
    'et T}), (0 < #|C|)%N -> @meet_avg R T C E (fun=> a) S0 = a. Proof.'
    ' exact: @meet_avg_cst. Qed. Lemma meet_avgC_accepted : forall (R :'
    ' realFieldType) (T C D : finType) (E : C -> {set T}) (F : D -> {se'
    't T}) (f : {set T} -> R), @meet_avg R T C E (@meet_avg R T D F f) '
    '= @meet_avg R T D F (@meet_avg R T C E f). Proof. exact: @meet_avg'
    'C. Qed. Lemma iter_meet_avg_accepted : forall (R : realFieldType) '
    '(T C : finType) (E : C -> {set T}) (m : nat) (f : {set T} -> R) (S'
    ' : {set T}), @iter ({set T} -> R) m (@meet_avg R T C E) f S = @uni'
    'f_mean R (tuple_tuple_of__canonical__fintype_Finite m C) (fun t : '
    'm.-tuple C => f (S :&: \\bigcap_(c <- t) E c)). Proof. exact: @iter'
    '_meet_avg. Qed. End accepted_commuting_operators. Module accepted_'
    'boolean_fourier. From HB Require Import structures. From mathcomp '
    'Require Import all_ssreflect_compat ssralg ssrnum ssrint zmodp. Fr'
    'om mathcomp Require Import matrix. From GaussianAnalysis.matrix Re'
    'quire Import euclidean. Import Order.TTheory GRing.Theory Num.Theo'
    'ry. Local Open Scope ring_scope. Require Import GaussianAnalysis.f'
    'ourier.boolean_fourier. Lemma bchar_algebra_accepted : forall (t a'
    " : nat) (R : pzRingType), [/\\ forall y : matrix 'F_2 t a, @bchar t"
    " a R 0 y = 1, forall p q y : matrix 'F_2 t a, @bchar t a R (p + q)"
    " y = @bchar t a R p y * @bchar t a R q y, forall p y : matrix 'F_2"
    " t a, @bchar t a R p y = @bchar t a R y p & forall p y : matrix 'F"
    '_2 t a, @bchar t a R p y = 1 \\/ @bchar t a R p y = -1]. Proof. exa'
    'ct: @bchar_algebra. Qed. Lemma bchar_orthogonal_accepted : forall '
    "(t a : nat) (R : pzRingType), forall p q : matrix 'F_2 t a, \\sum_y"
    ' @bchar t a R p y * @bchar t a R q y = (if p == q then #|{: matrix'
    " 'F_2 t a}|%:R else 0). Proof. exact: @bchar_orthogonal. Qed. Lemm"
    'a bchar_delta_accepted : forall (t a : nat) (R : pzRingType), fora'
    "ll (i : 'I_t) (j : 'I_a) (y : matrix 'F_2 t a), @bchar t a R (@del"
    'ta_mx (fintype_ordinal__canonical__GRing_PzSemiRing (Zp_trunc (pdi'
    'v 2))) t a i j) y = (-1) ^+ nat_of_ord (y i j). Proof. exact: @bch'
    'ar_delta. Qed. Lemma blk_dist_metric_accepted : forall t a : nat, '
    "[/\\ forall p q : matrix 'F_2 t a, @blk_dist t a p q = @blk_deg t a"
    " (p + q), forall p q : matrix 'F_2 t a, @blk_dist t a p q = 0%N <-"
    "> p = q, forall p q : matrix 'F_2 t a, @blk_dist t a p q = @blk_di"
    "st t a q p, forall p q s : matrix 'F_2 t a, (@blk_dist t a p s <= "
    "@blk_dist t a p q + @blk_dist t a q s)%N & forall p q s : matrix '"
    'F_2 t a, @blk_dist t a (p + s) (q + s) = @blk_dist t a p q]. Proof'
    '. exact: @blk_dist_metric. Qed. Lemma fcoef_inversion_accepted : f'
    'orall (t a : nat) (R : numFieldType), forall (V : lmodType R) (f :'
    " matrix 'F_2 t a -> V) (y : matrix 'F_2 t a), f y = \\sum_p @bchar "
    't a R p y *: @fcoef t a R V f p. Proof. exact: @fcoef_inversion. Q'
    'ed. Lemma fcoef_expansion_accepted : forall (t a : nat) (R : numFi'
    "eldType), forall (V : lmodType R) (c : matrix 'F_2 t a -> V) (q : "
    "matrix 'F_2 t a), @fcoef t a R V (fun y : matrix 'F_2 t a => \\sum_"
    'p @bchar t a R p y *: c p) q = c q. Proof. exact: @fcoef_expansion'
    '. Qed. Lemma fcoef_plancherel_accepted : forall (t a : nat) (R : n'
    'umFieldType), forall (V W Z : lmodType R) (b : V -> W -> Z), (fora'
    'll w : W, linear (b^~ w)) -> (forall v : V, linear (b v)) -> foral'
    "l (f : matrix 'F_2 t a -> V) (g : matrix 'F_2 t a -> W), #|{: matr"
    "ix 'F_2 t a}|%:R^-1 *: \\sum_y b (f y) (g y) = \\sum_p b (@fcoef t a"
    ' R V f p) (@fcoef t a R W g p). Proof. exact: @fcoef_plancherel. Q'
    'ed. Lemma fcoef_linear_accepted : forall (t a : nat) (R : numField'
    "Type), forall (V : lmodType R) (c : R) (f g : matrix 'F_2 t a -> V"
    ") (p : matrix 'F_2 t a), @fcoef t a R V (fun y : matrix 'F_2 t a ="
    '> c *: f y + g y) p = c *: @fcoef t a R V f p + @fcoef t a R V g p'
    '. Proof. exact: @fcoef_linear. Qed. Lemma fcoef_comp_linear_accept'
    'ed : forall (t a : nat) (R : numFieldType), forall (V W : lmodType'
    " R) (h : V -> W), linear h -> forall (f : matrix 'F_2 t a -> V) (p"
    " : matrix 'F_2 t a), @fcoef t a R W (fun y : matrix 'F_2 t a => h "
    '(f y)) p = h (@fcoef t a R V f p). Proof. exact: @fcoef_comp_linea'
    'r. Qed. Lemma fcoef_mulmx_accepted : forall (t a : nat) (R : numFi'
    "eldType), forall (m n k l : nat) (A : matrix R m n) (f : matrix 'F"
    "_2 t a -> matrix R n k) (B : matrix R k l) (p : matrix 'F_2 t a), "
    '@fcoef t a R (matrix_matrix__canonical__GRing_Lmodule R m l) (fun '
    "y : matrix 'F_2 t a => A *m f y *m B) p = A *m @fcoef t a R (matri"
    'x_matrix__canonical__GRing_Lmodule R n k) f p *m B. Proof. exact: '
    '@fcoef_mulmx. Qed. Lemma fcoef_norm_le_accepted : forall (t a : na'
    "t) (R : numFieldType), forall (f : matrix 'F_2 t a -> R^o) (c : R)"
    " (p : matrix 'F_2 t a), (forall y : matrix 'F_2 t a, `|f y : R| <="
    ' c) -> `|@fcoef t a R (GRing.GRing_regular__canonical__GRing_Lmodu'
    'le R) f p : R| <= c. Proof. exact: @fcoef_norm_le. Qed. Lemma fcoe'
    'f_translate_accepted : forall (t a : nat) (R : numFieldType), fora'
    "ll (V : lmodType R) (f : matrix 'F_2 t a -> V) (p q : matrix 'F_2 "
    "t a), @fcoef t a R V (fun y : matrix 'F_2 t a => @bchar t a R q y "
    '*: f y) (p + q) = @fcoef t a R V f p. Proof. exact: @fcoef_transla'
    'te. Qed. Lemma low_blk_deg_expansion_accepted : forall (t a : nat)'
    ' (R : numFieldType), forall (V : lmodType R) (D : nat) (f : matrix'
    " 'F_2 t a -> V), @low_blk_deg t a R V D f <-> (forall y : matrix '"
    'F_2 t a, f y = \\sum_(p | (@blk_deg t a p <= D)%N) @bchar t a R p y'
    ' *: @fcoef t a R V f p). Proof. exact: @low_blk_deg_expansion. Qed'
    '. Lemma low_blk_deg_translate_accepted : forall (t a : nat) (R : n'
    "umFieldType), forall (V : lmodType R) (D : nat) (f : matrix 'F_2 t"
    " a -> V) (q : matrix 'F_2 t a), (forall p : matrix 'F_2 t a, (D < "
    '@blk_dist t a p q)%N -> @fcoef t a R V f p = 0) -> @low_blk_deg t '
    "a R V D (fun y : matrix 'F_2 t a => @bchar t a R q y *: f y). Proo"
    'f. exact: @low_blk_deg_translate. Qed. Lemma blk_dist_row_accepted'
    " : forall (a : nat) (s z : matrix 'F_2 1 a), @blk_dist 1 a s z = ("
    's != z). Proof. exact: @blk_dist_row. Qed. Lemma bchar_col_mx_acce'
    'pted : forall t1 t2 a : nat, forall (R : pzRingType) (p1 y1 : matr'
    "ix 'F_2 t1 a) (p2 y2 : matrix 'F_2 t2 a), @bchar (t1 + t2) a R (@c"
    "ol_mx 'F_2 t1 t2 a p1 p2) (@col_mx 'F_2 t1 t2 a y1 y2) = @bchar t1"
    ' a R p1 y1 * @bchar t2 a R p2 y2. Proof. exact: @bchar_col_mx. Qed'
    '. Lemma blk_col_mx_accepted : forall t1 t2 a : nat, forall (p1 q1 '
    ": matrix 'F_2 t1 a) (p2 q2 : matrix 'F_2 t2 a), @blk_deg (t1 + t2)"
    " a (@col_mx 'F_2 t1 t2 a p1 p2) = (@blk_deg t1 a p1 + @blk_deg t2 "
    "a p2)%N /\\ @blk_dist (t1 + t2) a (@col_mx 'F_2 t1 t2 a p1 p2) (@co"
    "l_mx 'F_2 t1 t2 a q1 q2) = (@blk_dist t1 a p1 q1 + @blk_dist t2 a "
    'p2 q2)%N. Proof. exact: @blk_col_mx. Qed. Lemma fcoef_col_mx_accep'
    'ted : forall t1 t2 a : nat, forall (R : numFieldType) (V : lmodTyp'
    "e R) (f : matrix 'F_2 (t1 + t2) a -> V) (p1 : matrix 'F_2 t1 a) (p"
    "2 : matrix 'F_2 t2 a), @fcoef (t1 + t2) a R V f (@col_mx 'F_2 t1 t"
    "2 a p1 p2) = @fcoef t1 a R V (fun y1 : matrix 'F_2 t1 a => @fcoef "
    "t2 a R V (fun y2 : matrix 'F_2 t2 a => f (@col_mx 'F_2 t1 t2 a y1 "
    'y2)) p2) p1. Proof. exact: @fcoef_col_mx. Qed. End accepted_boolea'
    'n_fourier. Module accepted_psd_factorization. From HB Require Impo'
    'rt structures. From mathcomp Require Import all_ssreflect_compat f'
    'ingroup perm ssralg ssrnum. From mathcomp Require Import matrix se'
    'squilinear boolp classical_sets reals. From mathcomp Require Impor'
    't topology normedtype derive exp. From mathcomp Require Import ari'
    'thmetic_tactic ring_tactic. From GaussianAnalysis.matrix Require I'
    'mport euclidean real_spectral psd_part. From GaussianAnalysis.matr'
    'ix Require Import psd_splitting. From GaussianAnalysis.convex Requ'
    'ire Import logdet_barrier moreau. Import GRing.Theory Num.Theory O'
    'rder.TTheory. Import numFieldTopology.Exports numFieldNormedType.E'
    'xports. Local Open Scope ring_scope. Local Open Scope classical_se'
    't_scope. Require Import GaussianAnalysis.matrix.psd_factorization.'
    ' Lemma psd_factorization_ge0_accepted : forall (R : realType) (I J'
    ' : finType) (A : I -> J -> R) (r : nat), @psd_factorization R I J '
    'A r -> forall (i : I) (j : J), 0 <= A i j. Proof. exact: @psd_fact'
    'orization_ge0. Qed. Lemma psd_factorization_size_gt0_accepted : fo'
    'rall (R : realType) (I J : finType) (A : I -> J -> R) (r : nat), @'
    'psd_factorization R I J A r -> (exists (i : I) (j : J), A i j != 0'
    ') -> (0 < r)%N. Proof. exact: @psd_factorization_size_gt0. Qed. Le'
    'mma psd_factorization_restrict_accepted : forall (R : realType) (I'
    " J I' J' : finType) (A : I -> J -> R) (r : nat) (f : I' -> I) (g :"
    " J' -> J), @psd_factorization R I J A r -> @psd_factorization R I'"
    " J' (fun (i : I') (j : J') => A (f i) (g j)) r. Proof. exact: @psd"
    '_factorization_restrict. Qed. Lemma psd_factorization_widen_accept'
    'ed : forall (R : realType) (I J : finType) (A : I -> J -> R) (r s '
    ': nat), (r <= s)%N -> @psd_factorization R I J A r -> @psd_factori'
    'zation R I J A s. Proof. exact: @psd_factorization_widen. Qed. Lem'
    'ma psd_factorization_shift_accepted : forall (R : realType) (I J :'
    ' finType) (A : I -> J -> R) (r : nat) (rho : R), 0 <= rho -> @psd_'
    'factorization R I J A r -> @psd_factorization R I J (fun (i : I) ('
    'j : J) => A i j + rho) r.+1. Proof. exact: @psd_factorization_shif'
    't. Qed. Lemma psd_factorization_nonneg_accepted : forall (R : real'
    "Type) (I J : finType) (r : nat) (a : I -> 'I_r -> R) (b : J -> 'I_"
    "r -> R), (forall (i : I) (k : 'I_r), 0 <= a i k) -> (forall (j : J"
    ") (k : 'I_r), 0 <= b j k) -> @psd_factorization R I J (fun (i : I)"
    ' (j : J) => \\sum_(k < r) a i k * b j k) r. Proof. exact: @psd_fact'
    'orization_nonneg. Qed. End accepted_psd_factorization. Module acce'
    'pted_binomial_bounds. From HB Require Import structures. From math'
    'comp Require Import all_ssreflect_compat ssralg ssrnum rat reals. '
    'From mathcomp Require Import sequences exp. From mathcomp Require '
    'Import arithmetic_tactic ring_tactic. Import Order.TTheory GRing.T'
    'heory Num.Theory. Local Open Scope ring_scope. Local Open Scope na'
    't_scope. Require Import GaussianAnalysis.combinatorics.binomial_bo'
    'unds. Lemma central_bin_le_accepted : forall n : nat, (3 * n).+1 *'
    " 'C(2 * n, n) ^ 2 <= 16 ^ n. Proof. exact: @central_bin_le. Qed. L"
    'emma central_bin_ge_accepted : forall n : nat, 0 < n -> 16 ^ n <= '
    "4 * n * 'C(2 * n, n) ^ 2. Proof. exact: @central_bin_ge. Qed. Lemm"
    "a half_bin_ge_accepted : forall h : nat, 4 ^ h <= 2 * h.+1 * 'C(h,"
    ' h./2) ^ 2. Proof. exact: @half_bin_ge. Qed. Lemma leq_bin_half_ac'
    "cepted : forall n k : nat, 'C(n, k) <= 'C(n, n./2). Proof. exact: "
    '@leq_bin_half. Qed. Lemma bin_near_half_accepted : forall h g T : '
    "nat, 6 * T <= h -> h <= 2 * (g + T) -> 2 * g <= h + 2 * T -> 'C(h,"
    " h./2) <= 2 ^ T.+1 * 'C(h, g). Proof. exact: @bin_near_half. Qed. "
    "Lemma bin_sqr_central_accepted : forall u j : nat, j <= u -> 'C(u,"
    " j) ^ 2 * 'C(2 * u, u) = 'C(2 * j, j) * 'C(2 * (u - j), u - j) * '"
    'C(2 * u, 2 * j). Proof. exact: @bin_sqr_central. Qed. Lemma bin_sq'
    "r_ratio_accepted : forall u j : nat, j <= u -> 'C(u, j) ^ 4 * j.+1"
    " * (u - j).+1 <= 4 * u.+1 * 'C(2 * u, 2 * j) ^ 2. Proof. exact: @b"
    'in_sqr_ratio. Qed. Lemma bin_partial_sum_accepted : forall (R : re'
    "alType) (N M : nat), M <= N -> ((\\sum_(j < M.+1) 'C(N, nat_of_ord "
    'j)%:R : R) <= ((@expR R 1 * N%:R / M%:R) ^+ M : R))%R. Proof. exac'
    't: @bin_partial_sum. Qed. End accepted_binomial_bounds. Module acc'
    'epted_psd_duality. From HB Require Import structures. From mathcom'
    'p Require Import all_ssreflect_compat ssralg ssrnum matrix. From m'
    'athcomp Require Import sesquilinear boolp classical_sets reals. Fr'
    'om mathcomp Require Import topology normedtype. From mathcomp Requ'
    'ire Import arithmetic_tactic ring_tactic. From GaussianAnalysis.ma'
    'trix Require Import euclidean real_spectral psd_part. From Gaussia'
    'nAnalysis.matrix Require Import psd_splitting psd_factorization. F'
    'rom GaussianAnalysis.matrix Require Import nuclear condition_cone.'
    ' From GaussianAnalysis.gaussian Require Import measurable_matrix. '
    'From GaussianAnalysis.convex Require Import logdet_barrier moreau.'
    ' Import GRing.Theory Num.Theory Order.TTheory. Import numFieldTopo'
    'logy.Exports numFieldNormedType.Exports. Local Open Scope ring_sco'
    'pe. Local Open Scope classical_set_scope. Require Import GaussianA'
    'nalysis.matrix.psd_duality. Lemma psd_eval_cone_closed_accepted : '
    "forall (R : realType) (n N : nat) (G : 'I_N -> matrix R n n), (for"
    "all j : 'I_N, @psdmx R n (G j)) -> @closed (matrix_matrix__canonic"
    'al__topology_structure_Topological 1 N (numFieldTopology.Real_sort'
    '__canonical__topology_structure_Topological R)) (@psd_eval_cone R '
    'n N G). Proof. exact: @psd_eval_cone_closed. Qed. Lemma psdmx_dual'
    '_accepted : forall (R : realType) (n : nat) (S : matrix R n n), S '
    '\\is symmetricmx -> @psdmx R n S <-> (forall F : matrix R n n, @psd'
    'mx R n F -> 0 <= \\tr (F *m S)). Proof. exact: @psdmx_dual. Qed. Le'
    "mma psd_farkas_accepted : forall (R : realType) (n N : nat) (G : '"
    "I_N -> matrix R n n) (y : matrix R 1 N), (forall j : 'I_N, @psdmx "
    'R n (G j)) -> @psd_eval_cone R n N G y <-> (forall c : matrix R 1 '
    'N, @psdmx R n (\\sum_j c 0 j *: G j) -> 0 <= @mxdot R 1 N c y). Pro'
    'of. exact: @psd_farkas. Qed. Lemma psd_slack_certificate_accepted '
    ': forall (R : realType) (n : nat) (I : finType) (B : I -> matrix R'
    ' n n) (s : I -> R) (i0 : I), (forall i : I, @psdmx R n (B i)) -> s'
    ' i0 = 0 -> (exists2 A : matrix R n n, @psdmx R n A & forall i : I,'
    ' \\tr (A *m B i) = s i) <-> (forall w : I -> R, \\sum_i w i = 1 -> @'
    'psdmx R n (\\sum_i w i *: B i) -> 0 <= \\sum_i w i * s i). Proof. ex'
    'act: @psd_slack_certificate. Qed. Lemma psd_slack_certificate_affi'
    'ne_accepted : forall (R : realType) (n m : nat) (I : finType) (C :'
    " 'I_m -> matrix R n n) (c : 'I_m -> R) (D : matrix R n n) (d : R) "
    '(B : I -> matrix R n n) (i0 : I), (forall i : I, @psdmx R n (B i))'
    " -> (forall (i : I) (l : 'I_m), \\tr (C l *m B i) = c l) -> (forall"
    " X : matrix R n n, @psdmx R n X -> (forall l : 'I_m, \\tr (C l *m X"
    ') = c l) -> 0 <= \\tr (D *m X) + d) -> \\tr (D *m B i0) + d = 0 -> e'
    'xists2 A : matrix R n n, @psdmx R n A & forall i : I, \\tr (A *m B '
    'i) = \\tr (D *m B i) + d. Proof. exact: @psd_slack_certificate_affi'
    'ne. Qed. End accepted_psd_duality. Definition library_statements_a'
    'ccepted := (accepted_finite_mean.unif_mean_union_accepted, accepte'
    'd_finite_mean.unif_mean_indicatorN_accepted, accepted_finite_mean.'
    'unif_mean_markov_accepted, accepted_finite_mean.unif_mean_cutoff_a'
    'ccepted, accepted_finite_mean.unif_chebyshev_accepted, accepted_fi'
    'nite_mean.unif_mean_tuple_prod_ord_accepted, accepted_finite_mean.'
    'unif_mean_tuple_prod_set_accepted, accepted_binomial_mean.binomial'
    '_mean0_accepted, accepted_binomial_mean.binomial_meanS_accepted, a'
    'ccepted_binomial_mean.eq_binomial_mean_accepted, accepted_binomial'
    '_mean.binomial_mean_cst_accepted, accepted_binomial_mean.binomial_'
    'meanD_accepted, accepted_binomial_mean.binomial_meanZ_accepted, ac'
    'cepted_binomial_mean.ler_binomial_mean_accepted, accepted_binomial'
    '_mean.binomial_mean_id_accepted, accepted_binomial_mean.binomial_m'
    'ean_sqr_dev_accepted, accepted_binomial_mean.binomial_chebyshev_ac'
    'cepted, accepted_binomial_mean.binomial_mean_last_accepted, accept'
    'ed_binomial_mean.binomial_mean_trials_accepted, accepted_binomial_'
    'mean.unif_mean_binomial_mean_accepted, accepted_binomial_mean.bino'
    'mial_meanE_accepted, accepted_binomial_mean.integral_binomial_mean'
    '_accepted, accepted_commuting_operators.homo_iter_accepted, accept'
    'ed_commuting_operators.iter_le_subcomm_accepted, accepted_commutin'
    'g_operators.monotone_iter_le_accepted, accepted_commuting_operator'
    's.iter_scale_accepted, accepted_commuting_operators.iter_mix_binom'
    'ial_accepted, accepted_commuting_operators.binomial_mix_le_iter_ac'
    'cepted, accepted_commuting_operators.meet_avg_linear_accepted, acc'
    'epted_commuting_operators.meet_avg_monotone_accepted, accepted_com'
    'muting_operators.meet_avg_cst_accepted, accepted_commuting_operato'
    'rs.meet_avgC_accepted, accepted_commuting_operators.iter_meet_avg_'
    'accepted, accepted_boolean_fourier.bchar_algebra_accepted, accepte'
    'd_boolean_fourier.bchar_orthogonal_accepted, accepted_boolean_four'
    'ier.bchar_delta_accepted, accepted_boolean_fourier.blk_dist_metric'
    '_accepted, accepted_boolean_fourier.fcoef_inversion_accepted, acce'
    'pted_boolean_fourier.fcoef_expansion_accepted, accepted_boolean_fo'
    'urier.fcoef_plancherel_accepted, accepted_boolean_fourier.fcoef_li'
    'near_accepted, accepted_boolean_fourier.fcoef_comp_linear_accepted'
    ', accepted_boolean_fourier.fcoef_mulmx_accepted, accepted_boolean_'
    'fourier.fcoef_norm_le_accepted, accepted_boolean_fourier.fcoef_tra'
    'nslate_accepted, accepted_boolean_fourier.low_blk_deg_expansion_ac'
    'cepted, accepted_boolean_fourier.low_blk_deg_translate_accepted, a'
    'ccepted_boolean_fourier.blk_dist_row_accepted, accepted_boolean_fo'
    'urier.bchar_col_mx_accepted, accepted_boolean_fourier.blk_col_mx_a'
    'ccepted, accepted_boolean_fourier.fcoef_col_mx_accepted, accepted_'
    'psd_factorization.psd_factorization_ge0_accepted, accepted_psd_fac'
    'torization.psd_factorization_size_gt0_accepted, accepted_psd_facto'
    'rization.psd_factorization_restrict_accepted, accepted_psd_factori'
    'zation.psd_factorization_widen_accepted, accepted_psd_factorizatio'
    'n.psd_factorization_shift_accepted, accepted_psd_factorization.psd'
    '_factorization_nonneg_accepted, accepted_binomial_bounds.central_b'
    'in_le_accepted, accepted_binomial_bounds.central_bin_ge_accepted, '
    'accepted_binomial_bounds.half_bin_ge_accepted, accepted_binomial_b'
    'ounds.leq_bin_half_accepted, accepted_binomial_bounds.bin_near_hal'
    'f_accepted, accepted_binomial_bounds.bin_sqr_central_accepted, acc'
    'epted_binomial_bounds.bin_sqr_ratio_accepted, accepted_binomial_bo'
    'unds.bin_partial_sum_accepted, accepted_psd_duality.psd_eval_cone_'
    'closed_accepted, accepted_psd_duality.psdmx_dual_accepted, accepte'
    'd_psd_duality.psd_farkas_accepted, accepted_psd_duality.psd_slack_'
    'certificate_accepted, accepted_psd_duality.psd_slack_certificate_a'
    'ffine_accepted). Print Assumptions library_statements_accepted.')
PHASE13_MAKE_LINES_P = [
    "rm -f $(REPORTS) build/applications_definitions.txt "
    "build/phase13_definitions.txt build/library_statements.txt",
    "rocq compile -noglob -w -notation-overridden -w -ambiguous-paths "
    "-w -notation-incompatible-prefix -w -hiding-delimiting-key -Q library "
    "GaussianAnalysis -o build/LibraryStatements.vo "
    "check/LibraryStatements.v > build/library_statements.txt",
]
# The freeze of the seven statement files of the shifted-Gaussian proof
# (rule 30), accepted by the user at SHIFTED_BASELINE.
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
SHIFTED_DEFINITIONS = "check/ShiftedDefinitions.v"
SHIFTED_DEFINITIONS_OUTPUT = "build/shifted_definitions.txt"
# The commands of the Makefile that delete and regenerate the output.
SHIFTED_MAKE_LINES = [
    "rm -f $(REPORTS) build/applications_definitions.txt "
    "build/phase13_definitions.txt build/library_statements.txt "
    "build/shifted_definitions.txt",
    "rocq compile -noglob -w -notation-overridden -w -ambiguous-paths "
    "-w -notation-incompatible-prefix -w -hiding-delimiting-key -Q library "
    "GaussianAnalysis -Q theories EllipsoidFitting -Q extension "
    "EllipsoidUniversality -o build/ShiftedDefinitions.vo "
    "check/ShiftedDefinitions.v > build/shifted_definitions.txt",
]
# The code of check/ShiftedDefinitions.v, fixed at the freeze.
SHIFTED_DEFINITIONS_CHECK = (
    'From Stdlib Require Import Reals. From mathcomp Require Import all'
    '_ssreflect_compat ssralg ssrnum matrix. From mathcomp Require Impo'
    'rt classical_sets reals Rstruct. From mathcomp Require Import erea'
    'l topology sequences measure lebesgue_measure. From mathcomp Requi'
    're Import probability. Require GaussianAnalysis.gaussian.measurabl'
    'e_matrix. Require GaussianAnalysis.analysis.family_reindexing. Req'
    'uire GaussianAnalysis.matrix.euclidean. Require GaussianAnalysis.m'
    'atrix.coordinate_blocks. Require GaussianAnalysis.matrix.quadric_c'
    'ertificate. Require GaussianAnalysis.probability.lindeberg. Requir'
    'e GaussianAnalysis.probability.tuple_rows. Require GaussianAnalysi'
    's.probability.mixture. Require GaussianAnalysis.probability.counta'
    'ble_mixture. Require GaussianAnalysis.probability.symmetric_shift.'
    ' Require EllipsoidFitting.PaperMainDefinitions. Require EllipsoidF'
    'itting.Gaussian.Law.LibraryBridge. Require EllipsoidUniversality.U'
    'niversalityDefinitions. Require EllipsoidUniversality.MixtureDefin'
    'itions. Require EllipsoidUniversality.CountableMixtureDefinitions.'
    ' Require EllipsoidUniversality.Sat.AprioriSparse. Require Ellipsoi'
    'dUniversality.Shifted.GaussianRows. Require EllipsoidUniversality.'
    'Shifted.Translations. Require EllipsoidUniversality.Shifted.Transl'
    'ationError. Require EllipsoidUniversality.Shifted.GaussianConditio'
    'n. Require EllipsoidUniversality.Shifted.MixtureRows. Require Elli'
    'psoidUniversality.Shifted.SignMixture. Import (canonicals) Gaussia'
    'nAnalysis.gaussian.measurable_matrix. Import (canonicals) Gaussian'
    'Analysis.probability.mixture. Import (canonicals) GaussianAnalysis'
    '.probability.countable_mixture. Local Open Scope ring_scope. Local'
    ' Open Scope classical_set_scope. Local Notation RR := (R : realTyp'
    'e). Lemma family_sequence_limit_characterization (R : realType) (u'
    ' : nat -> R) (a : R) : GaussianAnalysis.analysis.family_reindexing'
    '.family_sequence_limit u a <-> forall eps : R, 0 < eps -> exists D'
    ' : nat, forall d : nat, (D <= d)%N -> `|u d - a| < eps. Proof. by '
    '[]. Qed. Lemma coordinate_support_characterization (R : realType) '
    "(d : nat) (m : 'cV[R]_d) : GaussianAnalysis.matrix.coordinate_bloc"
    "ks.coordinate_support m = [set i : 'I_d | m i 0 != 0]%SET. Proof. "
    'by []. Qed. Lemma quadric_eval_characterization (R : realType) (n '
    ": nat) (Q : 'M[R]_n) (v : 'cV[R]_n) (c : R) (x : 'cV[R]_n) : Gauss"
    'ianAnalysis.matrix.quadric_certificate.quadric_eval Q v c x = Gaus'
    'sianAnalysis.matrix.euclidean.mxdot x (Q *m x) + GaussianAnalysis.'
    'matrix.euclidean.mxdot v x + c. Proof. by []. Qed. Lemma tuple_map'
    "_characterization d d' (T : measurableType d) (T' : measurableType"
    " d') (g : nat -> T -> T') (n : nat) (x : n.-tuple T) : GaussianAna"
    'lysis.probability.tuple_rows.tuple_map g x = [tuple g i (tnth x i)'
    ' | i < n]. Proof. by []. Qed. Lemma mixture_weights_characterizati'
    'on (I : finType) (R : realType) (w : I -> R) : GaussianAnalysis.pr'
    'obability.mixture.mixture_weights w <-> (forall i, 0 <= w i) /\\ \\s'
    'um_i w i = 1. Proof. by []. Qed. Lemma mixture_characterization d '
    '(T : measurableType d) (R : realType) (I : finType) (w : I -> R) ('
    'P : I -> probability T R) (hw : GaussianAnalysis.probability.mixtu'
    're.mixture_weights w) (A : set T) : (GaussianAnalysis.probability.'
    'mixture.mixture P hw : probability T R) A = (\\sum_i (w i)%:E * P i'
    ' A)%E. Proof. by []. Qed. Lemma cmixture_weights_characterization '
    '(R : realType) (p : nat -> R) : GaussianAnalysis.probability.count'
    'able_mixture.cmixture_weights p <-> (forall s, 0 <= p s) /\\ (\\sum_'
    '(s <oo) (p s)%:E = 1)%E. Proof. by []. Qed. Lemma cmixture_charact'
    'erization d (T : measurableType d) (R : realType) (P : nat -> prob'
    'ability T R) (p : nat -> R) (hp : GaussianAnalysis.probability.cou'
    'ntable_mixture.cmixture_weights p) (A : set T) : (GaussianAnalysis'
    '.probability.countable_mixture.cmixture P hp : probability T R) A '
    '= (\\sum_(s <oo) (p s)%:E * P s A)%E. Proof. by []. Qed. Lemma row_'
    'symmetric_law_characterization (R : realType) (d : nat) (P : proba'
    "bility 'rV[R]_d R) : GaussianAnalysis.probability.symmetric_shift."
    "row_symmetric_law P <-> forall A : set 'rV[R]_d, measurable A -> P"
    ' ((fun x => - x) @^-1` A) = P A. Proof. by []. Qed. Lemma row_shif'
    "t_characterization (R : realType) (d : nat) (m x : 'rV[R]_d) : Gau"
    'ssianAnalysis.probability.symmetric_shift.row_shift m x = x + m. P'
    'roof. by []. Qed. Lemma row_shift_law_characterization (R : realTy'
    "pe) (d : nat) (P : probability 'rV[R]_d R) (m : 'rV[R]_d) (A : set"
    " 'rV[R]_d) : (GaussianAnalysis.probability.symmetric_shift.row_shi"
    "ft_law P m : probability 'rV[R]_d R) A = P [set x | A (x + m)]. Pr"
    'oof. by []. Qed. Lemma sign_shift_weights_characterization (R : re'
    'alType) (w : R) (b : bool) : GaussianAnalysis.probability.symmetri'
    'c_shift.sign_shift_weights w b = if b then w else 1 - w. Proof. by'
    ' []. Qed. Lemma sign_shift_law_characterization (R : realType) (d '
    ": nat) (P : probability 'rV[R]_d R) (m : 'rV[R]_d) (w : R) (hw : 0"
    " <= w <= 1) (A : set 'rV[R]_d) : (GaussianAnalysis.probability.sym"
    "metric_shift.sign_shift_law P m hw : probability 'rV[R]_d R) A = ("
    '\\sum_(b : bool) (if b then w else 1 - w)%:E * P [set x | A (x + if'
    ' b then m else - m)%R])%E. Proof. by []. Qed. Lemma row_outer_char'
    "acterization (R : realType) (d : nat) (x : 'rV[R]_d) : GaussianAna"
    'lysis.probability.symmetric_shift.row_outer x = x^T *m x. Proof. b'
    'y []. Qed. Lemma row_of_tuple_characterization (d : nat) (t : d.-t'
    'uple (measurableTypeR R)) : EllipsoidFitting.Gaussian.Law.LibraryB'
    'ridge.row_of_tuple d t = \\row_i (tnth t i : R). Proof. by []. Qed.'
    ' Lemma point_law_characterization (d : nat) (nu : nat -> probabili'
    "ty (measurableTypeR R) R) (A : set 'rV[RR]_d) : EllipsoidUniversal"
    'ity.Sat.AprioriSparse.point_law d nu A = GaussianAnalysis.probabil'
    'ity.lindeberg.tuple_prod nu d [set t | A (\\row_i (tnth t i : R))].'
    ' Proof. by []. Qed. Lemma sample_row_tuple_characterization (n d :'
    ' nat) (x : (n * d).-tuple (measurableTypeR R)) : @EllipsoidUnivers'
    'ality.Shifted.GaussianRows.sample_row_tuple n d x = [tuple (Ellips'
    'oidFitting.PaperMainDefinitions.paper_main_point x i)^T | i < n]. '
    'Proof. by []. Qed. Lemma sample_flat_row_characterization (n d : n'
    "at) (k : 'I_(n * d)) : nat_of_ord (@EllipsoidUniversality.Shifted."
    'GaussianRows.sample_flat_row n d k) = (k %/ d)%N. Proof. by []. Qe'
    "d. Lemma sample_flat_col_characterization (n d : nat) (k : 'I_(n *"
    ' d)) : nat_of_ord (@EllipsoidUniversality.Shifted.GaussianRows.sam'
    'ple_flat_col n d k) = (k %% d)%N. Proof. by []. Qed. Lemma sample_'
    "of_row_tuple_characterization (n d : nat) (x : n.-tuple 'rV[RR]_d)"
    ' : @EllipsoidUniversality.Shifted.GaussianRows.sample_of_row_tuple'
    ' n d x = [tuple tnth x (EllipsoidUniversality.Shifted.GaussianRows'
    '.sample_flat_row k) 0 (EllipsoidUniversality.Shifted.GaussianRows.'
    'sample_flat_col k) | k < n * d]. Proof. by []. Qed. Lemma sample_t'
    "ranslate_characterization (n d : nat) (m : 'cV[RR]_d) (x : (n * d)"
    '.-tuple (measurableTypeR R)) : @EllipsoidUniversality.Shifted.Tran'
    'slations.sample_translate n d m x = @EllipsoidUniversality.Shifted'
    '.GaussianRows.sample_of_row_tuple n d [tuple tnth (EllipsoidUniver'
    'sality.Shifted.GaussianRows.sample_row_tuple x) i + m^T | i < n]. '
    'Proof. by []. Qed. Lemma translation_fitting_error_characterizatio'
    'n (n d : nat) (x : (n * d).-tuple (measurableTypeR R)) : Ellipsoid'
    'Universality.Shifted.TranslationError.translation_fitting_error n '
    'd x = inf [set EllipsoidUniversality.UniversalityDefinitions.unive'
    'rsality_fitting_error n d (EllipsoidUniversality.Shifted.Translati'
    "ons.sample_translate m x) | m in [set: 'cV[RR]_d]]. Proof. by []. "
    'Qed. Lemma gaussian_small_shift_characterization (m : forall d : n'
    "at, 'cV[R]_d) : EllipsoidUniversality.Shifted.GaussianCondition.ga"
    'ussian_small_shift m <-> forall e : R, 0 < e -> exists D : nat, fo'
    'rall d : nat, (D <= d)%N -> GaussianAnalysis.matrix.euclidean.frob'
    'enius (m d) <= e * Num.sqrt d%:R. Proof. by []. Qed. Lemma finite_'
    'row_law_characterization (K : R) (N : nat -> nat) (w : nat -> nat '
    '-> R) (mu : nat -> nat -> nat -> probability (measurableTypeR R) R'
    ') (hfam : EllipsoidUniversality.MixtureDefinitions.mixture_family '
    "K N w mu) (d : nat) (A : set 'rV[RR]_d) : EllipsoidUniversality.Sh"
    'ifted.MixtureRows.finite_row_law hfam d A = (\\sum_(s < N d) (w d s'
    ')%:E * EllipsoidUniversality.Sat.AprioriSparse.point_law d (mu d s'
    ') A)%E. Proof. by []. Qed. Lemma countable_row_law_characterizatio'
    'n (K : R) (w : nat -> nat -> R) (mu : nat -> nat -> nat -> probabi'
    'lity (measurableTypeR R) R) (hfam : EllipsoidUniversality.Countabl'
    'eMixtureDefinitions.countable_mixture_family K w mu) (d : nat) (A '
    ": set 'rV[RR]_d) : EllipsoidUniversality.Shifted.MixtureRows.count"
    'able_row_law hfam d A = (\\sum_(s <oo) (w d s)%:E * EllipsoidUniver'
    'sality.Sat.AprioriSparse.point_law d (mu d s) A)%E. Proof. by []. '
    'Qed. Lemma row_sample_map_characterization (n d : nat) (x : n.-tup'
    "le 'rV[RR]_d) : EllipsoidUniversality.Shifted.SignMixture.row_samp"
    'le_map n d x = @EllipsoidUniversality.Shifted.GaussianRows.sample_'
    'of_row_tuple n d x. Proof. by []. Qed. Lemma iid_row_sample_law_ch'
    "aracterization (d : nat) (P : probability 'rV[RR]_d RR) (n : nat) "
    '(A : set ((n * d).-tuple (measurableTypeR R))) : EllipsoidUniversa'
    'lity.Shifted.SignMixture.iid_row_sample_law P n A = GaussianAnalys'
    'is.probability.lindeberg.tuple_prod (fun _ => P) n (@EllipsoidUniv'
    'ersality.Shifted.GaussianRows.sample_of_row_tuple n d @^-1` A). Pr'
    'oof. by []. Qed. Lemma shifted_iid_sample_law_characterization (d '
    ": nat) (P : probability 'rV[RR]_d RR) (m : 'cV[R]_d) (n : nat) (A "
    ': set ((n * d).-tuple (measurableTypeR R))) : EllipsoidUniversalit'
    'y.Shifted.SignMixture.shifted_iid_sample_law P m n A = GaussianAna'
    'lysis.probability.lindeberg.tuple_prod (fun _ => GaussianAnalysis.'
    'probability.symmetric_shift.row_shift_law P m^T) n (@EllipsoidUniv'
    'ersality.Shifted.GaussianRows.sample_of_row_tuple n d @^-1` A). Pr'
    'oof. by []. Qed. Lemma sign_mixture_sample_law_characterization (d'
    " : nat) (P : probability 'rV[RR]_d RR) (m : 'cV[R]_d) (w : R) (hw "
    ': 0 <= w <= 1) (n : nat) (A : set ((n * d).-tuple (measurableTypeR'
    ' R))) : EllipsoidUniversality.Shifted.SignMixture.sign_mixture_sam'
    'ple_law P m hw n A = GaussianAnalysis.probability.lindeberg.tuple_'
    'prod (fun _ => GaussianAnalysis.probability.symmetric_shift.sign_s'
    'hift_law P m^T hw) n (@EllipsoidUniversality.Shifted.GaussianRows.'
    'sample_of_row_tuple n d @^-1` A). Proof. by []. Qed. Definition sh'
    'ifted_characterizations := (@family_sequence_limit_characterizatio'
    'n, @coordinate_support_characterization, @quadric_eval_characteriz'
    'ation, @tuple_map_characterization, @mixture_weights_characterizat'
    'ion, @mixture_characterization, @cmixture_weights_characterization'
    ', @cmixture_characterization, @row_symmetric_law_characterization,'
    ' @row_shift_characterization, @row_shift_law_characterization, @si'
    'gn_shift_weights_characterization, @sign_shift_law_characterizatio'
    'n, @row_outer_characterization, @row_of_tuple_characterization, @p'
    'oint_law_characterization, @sample_row_tuple_characterization, @sa'
    'mple_flat_row_characterization, @sample_flat_col_characterization,'
    ' @sample_of_row_tuple_characterization, @sample_translate_characte'
    'rization, @translation_fitting_error_characterization, @gaussian_s'
    'mall_shift_characterization, @finite_row_law_characterization, @co'
    'untable_row_law_characterization, @row_sample_map_characterization'
    ', @iid_row_sample_law_characterization, @shifted_iid_sample_law_ch'
    'aracterization, @sign_mixture_sample_law_characterization). Print '
    'Assumptions shifted_characterizations.')
# The axiom checks of the seven theorems of the shifted-Gaussian proof
# (rule 31), in the identity form of rule 29: the code of each check file.
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
# The joint check of the seven theorems against their frozen statements
# (rule 31), its output, and the commands of the Makefile that delete and
# regenerate the output.
SHIFTED_IDENTITIES = "check/ShiftedIdentities.v"
SHIFTED_IDENTITIES_OUTPUT = "build/shifted_identities.txt"
SHIFTED_MAKE_LINES_P = [
    "rm -f $(REPORTS) build/applications_definitions.txt "
    "build/phase13_definitions.txt build/library_statements.txt "
    "build/shifted_definitions.txt build/shifted_identities.txt",
    "rocq compile -noglob -Q library GaussianAnalysis -Q theories "
    "EllipsoidFitting -Q extension EllipsoidUniversality -o "
    "build/ShiftedIdentities.vo check/ShiftedIdentities.v > "
    "build/shifted_identities.txt",
]
# The code of check/ShiftedIdentities.v, fixed with the axiom checks.
SHIFTED_IDENTITIES_CHECK = (
    'Require EllipsoidUniversality.ShiftedConditionStatement. Require E'
    'llipsoidUniversality.Shifted.ConditionTheorem. Require EllipsoidUn'
    'iversality.ShiftedGaussianStatement. Require EllipsoidUniversality'
    '.Shifted.GaussianTheorem. Require EllipsoidUniversality.ShiftedQua'
    'dricStatement. Require EllipsoidUniversality.Shifted.QuadricTheore'
    'm. Require EllipsoidUniversality.ShiftedErrorStatement. Require El'
    'lipsoidUniversality.Shifted.ErrorTheorem. Require EllipsoidUnivers'
    'ality.ShiftedMixtureUnsatStatement. Require EllipsoidUniversality.'
    'Shifted.MixtureUnsatTheorem. Require EllipsoidUniversality.Shifted'
    'MixtureSatStatement. Require EllipsoidUniversality.Shifted.Mixture'
    'SatTheorem. Require EllipsoidUniversality.ShiftedSignStatement. Re'
    'quire EllipsoidUniversality.Shifted.SignTheorem. Definition shifte'
    'd_condition_identity : EllipsoidUniversality.ShiftedConditionState'
    'ment.shifted_condition_statement := EllipsoidUniversality.Shifted.'
    'ConditionTheorem.shifted_condition_theorem. Definition shifted_gau'
    'ssian_identity : EllipsoidUniversality.ShiftedGaussianStatement.sh'
    'ifted_gaussian_statement := EllipsoidUniversality.Shifted.Gaussian'
    'Theorem.shifted_gaussian_theorem. Definition shifted_quadric_ident'
    'ity : EllipsoidUniversality.ShiftedQuadricStatement.shifted_quadri'
    'c_statement := EllipsoidUniversality.Shifted.QuadricTheorem.shifte'
    'd_quadric_theorem. Definition shifted_error_identity : EllipsoidUn'
    'iversality.ShiftedErrorStatement.shifted_error_statement := Ellips'
    'oidUniversality.Shifted.ErrorTheorem.shifted_error_theorem. Defini'
    'tion shifted_mixture_unsat_identity : EllipsoidUniversality.Shifte'
    'dMixtureUnsatStatement.shifted_mixture_unsat_statement := Ellipsoi'
    'dUniversality.Shifted.MixtureUnsatTheorem.shifted_mixture_unsat_th'
    'eorem. Definition shifted_mixture_sat_identity : EllipsoidUniversa'
    'lity.ShiftedMixtureSatStatement.shifted_mixture_sat_statement := E'
    'llipsoidUniversality.Shifted.MixtureSatTheorem.shifted_mixture_sat'
    '_theorem. Definition shifted_sign_identity : EllipsoidUniversality'
    '.ShiftedSignStatement.shifted_sign_statement := EllipsoidUniversal'
    'ity.Shifted.SignTheorem.shifted_sign_theorem. Definition shifted_i'
    'dentities : EllipsoidUniversality.ShiftedConditionStatement.shifte'
    'd_condition_statement /\\ EllipsoidUniversality.ShiftedGaussianStat'
    'ement.shifted_gaussian_statement /\\ EllipsoidUniversality.ShiftedQ'
    'uadricStatement.shifted_quadric_statement /\\ EllipsoidUniversality'
    '.ShiftedErrorStatement.shifted_error_statement /\\ EllipsoidUnivers'
    'ality.ShiftedMixtureUnsatStatement.shifted_mixture_unsat_statement'
    ' /\\ EllipsoidUniversality.ShiftedMixtureSatStatement.shifted_mixtu'
    're_sat_statement /\\ EllipsoidUniversality.ShiftedSignStatement.shi'
    'fted_sign_statement := conj shifted_condition_identity (conj shift'
    'ed_gaussian_identity (conj shifted_quadric_identity (conj shifted_'
    'error_identity (conj shifted_mixture_unsat_identity (conj shifted_'
    'mixture_sat_identity shifted_sign_identity))))). Locate shifted_id'
    'entities. Print Assumptions shifted_identities.')
# Every theorem whose axiom report the script takes, in the order of its
# arguments, and the path of its report: the arguments must be exactly the
# paths of REPORTS.
THEOREMS = (["main theorem", "universality theorem"]
            + [name for name, _, _, _ in PHASE6_THEOREMS + PHASE8_THEOREMS
               + PHASE9_THEOREMS + PHASE10_THEOREMS + PHASE11_THEOREMS
               + PHASE12_THEOREMS + PHASE13_THEOREMS + SHIFTED_THEOREMS])
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
    "build/shifted_condition_assumptions.txt",
    "build/shifted_gaussian_assumptions.txt",
    "build/shifted_quadric_assumptions.txt",
    "build/shifted_error_assumptions.txt",
    "build/shifted_mixture_unsat_assumptions.txt",
    "build/shifted_mixture_sat_assumptions.txt",
    "build/shifted_sign_assumptions.txt",
]
assert len(REPORTS) == len(THEOREMS)
PAPERS = {"EllipsoidFitting", "EllipsoidUniversality"}
APPLICATIONS = "GaussianApplications"
ASSUMPTION = re.compile(
    r"(?:\A|(?<=\.))\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+)?"
    r"(Admitted\s*\.|Axioms?\b|Parameters?\b|Conjecture\b)")
REQUIRE = re.compile(r"(?:From\s+([\w.]+)\s+)?Require(?:\s+(?:Import|Export))?\s+([^.]+(?:\.[A-Za-z]\w*)*)\s*\.", re.S)
STDLIB_REALS = re.compile(r"^(Reals|Lra|Psatz|Fourier|Ranalysis\w*|R[A-Z]\w*|Rbase|Rfunctions|Rpower|Rtrigo\w*|Rdefinitions|Raxioms|Rbasic_fun|Rsqrt_def|Rlimit|Rseries|Rcomplete|Rderiv|Rprod|Rtopology|SeqProp|SeqSeries|PSeries_reg|Exp_prop|Ratan|Rsigma|Rgeom|Cos_rel|Sqrt_reg|ClassicalDedekindReals|ConstructiveCauchyReals\w*)$")
MATHCOMP_BRIDGE = {"Rstruct", "Rstruct_topology"}


def code(text):
    return " ".join(strip_comments(text).split())


def at_baseline(commit, path):
    return subprocess.run(["git", "-C", str(ROOT), "show", f"{commit}:{path}"],
                          check=True, capture_output=True, text=True).stdout


def library_imports(text):
    """Pairs (root, module) of the Require commands of a source."""
    for match in REQUIRE.finditer(strip_comments(text)):
        root = match.group(1) or ""
        for name in match.group(2).split():
            yield root, name


def section_code(text, name):
    """The Require commands of a source and the code of its section name,
    comments removed and whitespace collapsed."""
    stripped = strip_comments(text)
    requires = " ".join(m.group(0) for m in REQUIRE.finditer(stripped))
    section = re.search(rf"Section {name}\..*?End {name}\.", stripped, re.S)
    return " ".join(requires.split()), " ".join(section.group(0).split()) if section else None


def tuple_prod_code(text):
    """The Require commands of TUPLE_PROD and the code of its section
    tuple_prod, comments removed and whitespace collapsed."""
    return section_code(text, "tuple_prod")


def read_report(path):
    """The text of an axiom report, or the empty string if it is missing."""
    try:
        return Path(path).read_text()
    except OSError:
        return ""


def report_complete(text):
    """An axiom report is complete when it has the line "Closed under the
    global context", or the line "Axioms:" followed by at least one
    axiom. A report with the line "Axioms:" and no axiom is incomplete."""
    lines = text.splitlines()
    if any(line.startswith("Closed under the global context") for line in lines):
        return True
    if any(line.rstrip() == "Axioms:" for line in lines):
        return any(not name.startswith("unexpected section ")
                   for name in axiom_names(text))
    return False


def axiom_names(text):
    names, header, marker = set(), None, False
    for line in text.splitlines():
        if marker:
            marker = False
            continue
        if not line or line[0].isspace():
            continue
        # The output of Locate, which the check files of phase 13 print
        # before their report: "Constant <name>", or "Constant" and the name
        # on the next line.
        if line == "Constant":
            marker = True
            continue
        if line.startswith("Constant ") and len(line.split()) == 2:
            continue
        if line.rstrip().endswith(":") and " " not in line.rstrip()[:-1]:
            header = line.rstrip()
            if header != "Axioms:":
                names.add("unexpected section " + header)
            continue
        if line.startswith("Closed under the global context"):
            continue
        names.add(line.split(" :", 1)[0].strip())
    return names


def main():
    commit = (ROOT / "check" / "frozen-baseline").read_text().split()[0]
    failures = []
    for path in FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(commit, path)):
            failures.append(f"{path}: code differs from {commit[:12]}")
    for path in EXACT:
        if (ROOT / path).read_text() != at_baseline(commit, path):
            failures.append(f"{path}: differs from {commit[:12]}")
    for path in EXTENSION_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(EXTENSION_BASELINE, path)):
            failures.append(f"{path}: code differs from {EXTENSION_BASELINE[:12]}")
    for path in PHASE6_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE6_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE6_BASELINE[:12]}")
    for path in LATENT_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(LATENT_BASELINE, path)):
            failures.append(f"{path}: code differs from {LATENT_BASELINE[:12]}")
    for path in PHASE8_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE8_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE8_BASELINE[:12]}")
    for path in PHASE9_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE9_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE9_BASELINE[:12]}")
    for path in PHASE10_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE10_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE10_BASELINE[:12]}")
    for path in PHASE11_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE11_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE11_BASELINE[:12]}")
    for path in PHASE12_B1_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE12_B1_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE12_B1_BASELINE[:12]}")
    for path in PHASE12_B2_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE12_B2_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE12_B2_BASELINE[:12]}")
    for path in CHECKS_EXACT:
        if (ROOT / path).read_text() != at_baseline(CHECKS_BASELINE, path):
            failures.append(f"{path}: differs from {CHECKS_BASELINE[:12]}")
    for path in CHECKS_EXACT_P8:
        if (ROOT / path).read_text() != at_baseline(CHECKS_P8_BASELINE, path):
            failures.append(f"{path}: differs from {CHECKS_P8_BASELINE[:12]}")
    for path in CHECKS_EXACT_P9:
        if (ROOT / path).read_text() != at_baseline(CHECKS_P9_BASELINE, path):
            failures.append(f"{path}: differs from {CHECKS_P9_BASELINE[:12]}")
    for path in CHECKS_EXACT_P10:
        if (ROOT / path).read_text() != at_baseline(CHECKS_P10_BASELINE, path):
            failures.append(f"{path}: differs from {CHECKS_P10_BASELINE[:12]}")
    for path in CHECKS_EXACT_P11:
        if (ROOT / path).read_text() != at_baseline(CHECKS_P11_BASELINE, path):
            failures.append(f"{path}: differs from {CHECKS_P11_BASELINE[:12]}")
    for path in CHECKS_EXACT_P12:
        if (ROOT / path).read_text() != at_baseline(CHECKS_P12_BASELINE, path):
            failures.append(f"{path}: differs from {CHECKS_P12_BASELINE[:12]}")
    now = tuple_prod_code((ROOT / TUPLE_PROD).read_text())
    if now[1] is None:
        failures.append(f"{TUPLE_PROD}: no section tuple_prod")
    elif now != tuple_prod_code(at_baseline(CHECKS_BASELINE, TUPLE_PROD)):
        failures.append(f"{TUPLE_PROD}: the Require commands or the section "
                        f"tuple_prod differ from {CHECKS_BASELINE[:12]}")
    for path in PHASE13_B1_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE13_B1_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE13_B1_BASELINE[:12]}")
    for path in PHASE13_B2_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE13_B2_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE13_B2_BASELINE[:12]}")
    for path in PHASE13_B3_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(PHASE13_B3_BASELINE, path)):
            failures.append(f"{path}: code differs from {PHASE13_B3_BASELINE[:12]}")
    if code((ROOT / PHASE13_DEFINITIONS).read_text()) != PHASE13_DEFINITIONS_FREEZES[-1]:
        failures.append(f"{PHASE13_DEFINITIONS}: code differs from the last code "
                        "of PHASE13_DEFINITIONS_FREEZES")
    for k, (prev, nxt) in enumerate(zip(PHASE13_DEFINITIONS_FREEZES,
                                        PHASE13_DEFINITIONS_FREEZES[1:])):
        if not nxt.startswith(prev):
            failures.append(f"PHASE13_DEFINITIONS_FREEZES: freeze {k + 2} does not "
                            f"extend freeze {k + 1}")
    makefile = (ROOT / "Makefile").read_text()
    allowed_p13 = axiom_names(
        (ROOT / "check" / "sat_variance_assumptions.expected").read_text())
    for line in PHASE13_MAKE_LINES:
        if line not in makefile:
            failures.append(f"Makefile: the command {line!r} is missing")
    output = ROOT / PHASE13_DEFINITIONS_OUTPUT
    if not output.exists():
        failures.append(f"{PHASE13_DEFINITIONS_OUTPUT}: no such output; make check "
                        f"compiles {PHASE13_DEFINITIONS} into it")
    elif not report_complete(output.read_text()):
        failures.append(f"{PHASE13_DEFINITIONS_OUTPUT}: incomplete, neither the line "
                        "Axioms: with at least one axiom nor the line Closed under "
                        "the global context")
    else:
        for ax in sorted(axiom_names(output.read_text()) - allowed_p13):
            failures.append(f"{PHASE13_DEFINITIONS_OUTPUT}: {ax} is not among "
                            "check/sat_variance_assumptions.expected")
    seen = set()
    for inv_commit, path, name, prop in INVENTORY:
        if (path, name) in seen:
            failures.append(f"INVENTORY: {path} {name} recorded twice")
        seen.add((path, name))
        if not re.fullmatch(r"[0-9a-f]{40}", inv_commit):
            failures.append(f"INVENTORY: {name}: {inv_commit} is not a full commit")
            continue
        try:
            then = strip_comments(at_baseline(inv_commit, path))
        except subprocess.CalledProcessError:
            failures.append(f"INVENTORY: {name}: no file {path} at {inv_commit[:12]}")
            continue
        if not re.search(rf"\bDefinition\s+{re.escape(name)}\b", then):
            failures.append(f"INVENTORY: {name}: not defined in {path} at {inv_commit[:12]}")
        if not prop.strip():
            failures.append(f"INVENTORY: {name}: empty proposition")
    libst_text = (ROOT / LIBRARY_STATEMENTS).read_text()
    if code(libst_text) != LIBRARY_STATEMENTS_CHECK:
        failures.append(f"{LIBRARY_STATEMENTS}: code differs from LIBRARY_STATEMENTS_CHECK")
    lemmas = {}
    for m in re.finditer(r"Lemma\s+(\w+)_accepted\s*:\s*(.*?)\.\s*Proof\.",
                         " ".join(strip_comments(libst_text).split()), re.S):
        lemmas[m.group(1)] = m.group(2).strip()
    for _, path, name, prop in INVENTORY:
        base = name[: -len("_statement")] if name.endswith("_statement") else name
        fun = re.match(r"fun\s+(.*?)\s*=>\s*(.*)\Z", prop, re.S)
        want = " ".join((f"forall {fun.group(1)}, {fun.group(2)}" if fun else prop).split())
        if base not in lemmas:
            failures.append(f"{LIBRARY_STATEMENTS}: no lemma {base}_accepted for "
                            f"the accepted statement {name} of {path}")
        elif lemmas[base] != want:
            failures.append(f"{LIBRARY_STATEMENTS}: {base}_accepted does not state "
                            f"the accepted proposition of {name}")
    for line in PHASE13_MAKE_LINES_P:
        if line not in makefile:
            failures.append(f"Makefile: the command {line!r} is missing")
    output = ROOT / LIBRARY_STATEMENTS_OUTPUT
    if not output.exists():
        failures.append(f"{LIBRARY_STATEMENTS_OUTPUT}: no such output; make check "
                        f"compiles {LIBRARY_STATEMENTS} into it")
    elif not report_complete(output.read_text()):
        failures.append(f"{LIBRARY_STATEMENTS_OUTPUT}: incomplete axiom report")
    else:
        for ax in sorted(axiom_names(output.read_text()) - allowed_p13):
            failures.append(f"{LIBRARY_STATEMENTS_OUTPUT}: {ax} is not among "
                            "check/sat_variance_assumptions.expected")
    for path in SHIFTED_FROZEN:
        if code((ROOT / path).read_text()) != code(at_baseline(SHIFTED_BASELINE, path)):
            failures.append(f"{path}: code differs from {SHIFTED_BASELINE[:12]}")
    if code((ROOT / SHIFTED_DEFINITIONS).read_text()) != SHIFTED_DEFINITIONS_CHECK:
        failures.append(f"{SHIFTED_DEFINITIONS}: code differs from "
                        "SHIFTED_DEFINITIONS_CHECK")
    for line in SHIFTED_MAKE_LINES:
        if line not in makefile:
            failures.append(f"Makefile: the command {line!r} is missing")
    output = ROOT / SHIFTED_DEFINITIONS_OUTPUT
    if not output.exists():
        failures.append(f"{SHIFTED_DEFINITIONS_OUTPUT}: no such output; make check "
                        f"compiles {SHIFTED_DEFINITIONS} into it")
    elif not report_complete(output.read_text()):
        failures.append(f"{SHIFTED_DEFINITIONS_OUTPUT}: incomplete, neither the line "
                        "Axioms: with at least one axiom nor the line Closed under "
                        "the global context")
    else:
        for ax in sorted(axiom_names(output.read_text()) - allowed_p13):
            failures.append(f"{SHIFTED_DEFINITIONS_OUTPUT}: {ax} is not among "
                            "check/sat_variance_assumptions.expected")
    if code((ROOT / SHIFTED_IDENTITIES).read_text()) != SHIFTED_IDENTITIES_CHECK:
        failures.append(f"{SHIFTED_IDENTITIES}: code differs from "
                        "SHIFTED_IDENTITIES_CHECK")
    for line in SHIFTED_MAKE_LINES_P:
        if line not in makefile:
            failures.append(f"Makefile: the command {line!r} is missing")
    output = ROOT / SHIFTED_IDENTITIES_OUTPUT
    if not output.exists():
        failures.append(f"{SHIFTED_IDENTITIES_OUTPUT}: no such output; make check "
                        f"compiles {SHIFTED_IDENTITIES} into it")
    elif not report_complete(output.read_text()):
        failures.append(f"{SHIFTED_IDENTITIES_OUTPUT}: incomplete, neither the line "
                        "Axioms: with at least one axiom nor the line Closed under "
                        "the global context")
    else:
        for ax in sorted(axiom_names(output.read_text()) - allowed_p13):
            failures.append(f"{SHIFTED_IDENTITIES_OUTPUT}: {ax} is not among "
                            "check/sat_variance_assumptions.expected")
    now = section_code((ROOT / LAMBDA_MAX).read_text(), "lambda_max")
    if now[1] is None:
        failures.append(f"{LAMBDA_MAX}: no section lambda_max")
    elif now != section_code(at_baseline(PHASE12_B1_BASELINE, LAMBDA_MAX), "lambda_max"):
        failures.append(f"{LAMBDA_MAX}: the Require commands or the section "
                        f"lambda_max differ from {PHASE12_B1_BASELINE[:12]}")
    if code((ROOT / APPLICATIONS_DEFINITIONS).read_text()) != APPLICATIONS_DEFINITIONS_CHECK:
        failures.append(f"{APPLICATIONS_DEFINITIONS}: code differs from "
                        "APPLICATIONS_DEFINITIONS_CHECK")
    reports = sys.argv[1:]
    if len(reports) != len(THEOREMS):
        missing = THEOREMS[len(reports):]
        failures.append(
            f"{len(reports)} axiom reports given, {len(THEOREMS)} required, "
            "one per theorem"
            + (": no report for the " + ", the ".join(missing) if missing else ""))
    for k, (arg, path) in enumerate(zip(reports, REPORTS)):
        if arg != path:
            failures.append(f"argument {k + 1}: {arg} given where the report of "
                            f"the {THEOREMS[k]}, {path}, is required")
    for arg in sorted({a for a in reports if reports.count(a) > 1}):
        failures.append(f"{arg}: given {reports.count(arg)} times")
    for arg in reports:
        if not Path(arg).exists():
            failures.append(f"{arg}: no such axiom report")
            continue
        if not report_complete(Path(arg).read_text()):
            failures.append(f"{arg}: the axiom report has neither the line "
                            "Axioms: with at least one axiom nor the line "
                            "Closed under the global context")
    sources = [path for top in ("theories", "library", "extension", "applications")
               for path in sorted((ROOT / top).rglob("*.v"))]
    for path in sources:
        for match in ASSUMPTION.finditer(strip_comments(path.read_text())):
            failures.append(f"{path.relative_to(ROOT)}: {match.group(1).strip()}")
    library = sorted((ROOT / "library").rglob("*.v"))
    applications = sorted((ROOT / "applications").rglob("*.v"))
    for path in library + applications:
        for root, name in library_imports(path.read_text()):
            full = f"{root}.{name}" if root else name
            last = full.split(".")[-1]
            stdlib = root.startswith(("Stdlib", "Coq")) or not root
            if PAPERS & set(full.split(".")):
                failures.append(f"{path.relative_to(ROOT)}: requires {full} of a paper")
            elif path in library and APPLICATIONS in full.split("."):
                failures.append(f"{path.relative_to(ROOT)}: requires {full} of applications/")
            elif stdlib and (STDLIB_REALS.match(last) or "Reals" in full.split(".")):
                failures.append(f"{path.relative_to(ROOT)}: requires Stdlib's {full}")
            elif last in MATHCOMP_BRIDGE:
                failures.append(f"{path.relative_to(ROOT)}: requires {full}")
    if code((ROOT / "check" / "UniversalityAssumptions.v").read_text()) != UNIVERSALITY_CHECK:
        failures.append("check/UniversalityAssumptions.v: code differs from UNIVERSALITY_CHECK")
    allowed = axiom_names((ROOT / "check" / "assumptions.expected").read_text())
    allowed_universality = axiom_names(
        (ROOT / "check" / "universality_assumptions.expected").read_text())
    for name in sorted(allowed_universality - allowed):
        failures.append(f"check/universality_assumptions.expected: {name} "
                        "is not among check/assumptions.expected")
    if len(sys.argv) > 1:
        printed = axiom_names(read_report(sys.argv[1]))
        for name in sorted(printed - allowed):
            failures.append(f"main theorem: {name} is not among check/assumptions.expected")
        if not failures and printed != allowed:
            print("main theorem: fewer axioms than check/assumptions.expected:",
                  ", ".join(sorted(printed)) or "none")
    if len(sys.argv) > 2:
        printed = axiom_names(read_report(sys.argv[2]))
        for name in sorted(printed - allowed_universality):
            failures.append(f"universality theorem: {name} is not among "
                            "check/universality_assumptions.expected")
        if not failures and printed != allowed_universality:
            print("universality theorem: fewer axioms than "
                  "check/universality_assumptions.expected:",
                  ", ".join(sorted(printed)) or "none")
    for k, (name, check, check_code, expected) in enumerate(
            PHASE6_THEOREMS + PHASE8_THEOREMS + PHASE9_THEOREMS
            + PHASE10_THEOREMS + PHASE11_THEOREMS + PHASE12_THEOREMS
            + PHASE13_THEOREMS + SHIFTED_THEOREMS):
        if code((ROOT / check).read_text()) != check_code:
            failures.append(f"{check}: code differs from the expected check")
        allowed_k = axiom_names((ROOT / expected).read_text())
        for ax in sorted(allowed_k - allowed):
            failures.append(f"{expected}: {ax} is not among check/assumptions.expected")
        if (name, check, check_code, expected) in PHASE13_THEOREMS + SHIFTED_THEOREMS:
            for ax in sorted(allowed_k - allowed_p13):
                failures.append(f"{expected}: {ax} is not among "
                                "check/sat_variance_assumptions.expected")
        if len(sys.argv) > 3 + k:
            printed = axiom_names(read_report(sys.argv[3 + k]))
            for ax in sorted(printed - allowed_k):
                failures.append(f"{name}: {ax} is not among {expected}")
            if not failures and printed != allowed_k:
                print(f"{name}: fewer axioms than {expected}:",
                      ", ".join(sorted(printed)) or "none")
    for line in failures:
        print(line)
    if failures:
        sys.exit(1)
    print(f"{len(FROZEN)} frozen files unchanged since {commit[:12]}; "
          f"{len(EXTENSION_FROZEN)} frozen files of extension/ unchanged since "
          f"{EXTENSION_BASELINE[:12]}; "
          f"{len(PHASE6_FROZEN)} frozen files of phase 6 unchanged since "
          f"{PHASE6_BASELINE[:12]}; "
          f"{len(CHECKS_EXACT)} check files and tuple_prod unchanged since "
          f"{CHECKS_BASELINE[:12]}; "
          f"{len(CHECKS_EXACT_P8)} check files of phases 7 and 8 unchanged since "
          f"{CHECKS_P8_BASELINE[:12]}; "
          f"{len(CHECKS_EXACT_P9)} check files of phase 9 unchanged since "
          f"{CHECKS_P9_BASELINE[:12]}; "
          f"{len(CHECKS_EXACT_P10)} check files of phase 10 unchanged since "
          f"{CHECKS_P10_BASELINE[:12]}; "
          f"{len(CHECKS_EXACT_P11)} check files of phase 11 unchanged since "
          f"{CHECKS_P11_BASELINE[:12]}; "
          f"{len(CHECKS_EXACT_P12)} check files of phase 12 unchanged since "
          f"{CHECKS_P12_BASELINE[:12]}; "
          f"{len(LATENT_FROZEN)} frozen files of phase 7 unchanged since "
          f"{LATENT_BASELINE[:12]}; "
          f"{len(PHASE8_FROZEN)} frozen files of phase 8 unchanged since "
          f"{PHASE8_BASELINE[:12]}; "
          f"{len(PHASE9_FROZEN)} frozen files of phase 9 unchanged since "
          f"{PHASE9_BASELINE[:12]}; "
          f"{len(PHASE10_FROZEN)} frozen files of phase 10 unchanged since "
          f"{PHASE10_BASELINE[:12]}; "
          f"{len(PHASE11_FROZEN)} frozen files of phase 11 unchanged since "
          f"{PHASE11_BASELINE[:12]}; "
          f"{len(PHASE12_B1_FROZEN)} frozen files of phase 12 and the section "
          f"lambda_max unchanged since {PHASE12_B1_BASELINE[:12]}; "
          f"{len(PHASE12_B2_FROZEN)} frozen files of phase 12 unchanged since "
          f"{PHASE12_B2_BASELINE[:12]}; "
          f"{len(PHASE13_B1_FROZEN)} frozen files of batch 1 of phase 13 unchanged since "
          f"{PHASE13_B1_BASELINE[:12]}; "
          f"{len(PHASE13_B2_FROZEN)} frozen files of batch 2 of phase 13 unchanged since "
          f"{PHASE13_B2_BASELINE[:12]}; "
          f"{len(PHASE13_B3_FROZEN)} frozen files of batch 3 of phase 13 unchanged since "
          f"{PHASE13_B3_BASELINE[:12]}; "
          f"{len(SHIFTED_FROZEN)} frozen shifted statement files unchanged since "
          f"{SHIFTED_BASELINE[:12]}; "
          f"the characterizations of {APPLICATIONS_DEFINITIONS} unchanged; "
          f"the characterizations of {PHASE13_DEFINITIONS} at freeze "
          f"{len(PHASE13_DEFINITIONS_FREEZES)}, compiled; "
          f"the characterizations of {SHIFTED_DEFINITIONS} unchanged, compiled; "
          f"the joint identities of the {len(SHIFTED_THEOREMS)} shifted theorems "
          f"in {SHIFTED_IDENTITIES} unchanged, compiled; "
          f"{len(INVENTORY)} accepted general statements in the inventory, each "
          f"stated and proved in {LIBRARY_STATEMENTS}; "
          f"no Admitted, Axiom, Parameter or Conjecture; "
          f"{len(library)} library modules independent of the papers, of applications/ "
          f"and of Stdlib's reals; "
          f"{len(applications)} modules of applications/ independent of the papers "
          f"and of Stdlib's reals; "
          f"{len(reports)} axiom reports, one per theorem"
          + ("; axioms of the main theorem allowed" if len(sys.argv) > 1 else "")
          + ("; axioms of the universality theorem allowed" if len(sys.argv) > 2 else "")
          + ("; axioms of the mixture theorem allowed" if len(sys.argv) > 3 else "")
          + ("; axioms of the paired theorem allowed" if len(sys.argv) > 4 else "")
          + ("; axioms of the latent-sign theorem allowed" if len(sys.argv) > 5 else "")
          + ("; axioms of the countable-mixture theorem allowed" if len(sys.argv) > 6 else "")
          + ("; axioms of the condition-number theorem allowed" if len(sys.argv) > 7 else "")
          + ("; axioms of the latent-sign scope theorem allowed" if len(sys.argv) > 8 else "")
          + ("; axioms of the robustness theorem allowed" if len(sys.argv) > 9 else "")
          + ("; axioms of the tensorization theorem allowed" if len(sys.argv) > 10 else "")
          + ("; axioms of the continuous-latent theorem allowed" if len(sys.argv) > 11 else "")
          + ("; axioms of the condition-endpoints theorem allowed" if len(sys.argv) > 12 else "")
          + ("; axioms of the robust condition-number theorem allowed" if len(sys.argv) > 13 else "")
          + ("; axioms of the tensorization upper bound allowed" if len(sys.argv) > 14 else "")
          + ("; axioms of the condition-number curve at kappa allowed" if len(sys.argv) > 15 else "")
          + ("; axioms of the condition-number theorem at kappa allowed" if len(sys.argv) > 16 else "")
          + ("; axioms of the robust condition-number theorem at kappa allowed" if len(sys.argv) > 17 else ""))


if __name__ == "__main__":
    main()
