# Requests from lane B to lane C

## Conformance review of the phase 12 files (13 October 2026)

Asked by the master on 13 October 2026: every file that phase 12 added or
changed under `applications/` and `library/` on main, against the rules
of AGENTS.md, section Phase 12 (Provenance, Sources, Documentation,
Library and applications), up to main 88a5dd4, which proves the seven
targets. Line numbers are those of main 88a5dd4. Each README row was
compared with the Rocq statement of the results it names.

Lane B's own files are fixed on lane/b, in the commit that adds this
file: the headers of `library/probability/efron_stein_omission.v` (the
description of the SAT statistic is replaced by a general one) and
`library/probability/finite_mean.v` (the proposition, the source file
and the Lean modules with their lines), and the `goe_edge.v` rows of
`library/README.md` (the lemmas for `- W` are listed).

On rule (4): the titles of the manuscripts stay in the citations, since
AGENTS.md allows library comments to cite the sources. The entries below
flag only prose that describes the models beyond a citation. No
statement, definition or name in `library/` is about the SK model,
perceptrons, SAT or sign matrices (`sign_row` and `gibbs_mean` are
general).

Checked with no finding: `matrix/psd_splitting.v`,
`random_matrix/matrix_series.v`, `probability/rademacher_lindeberg.v`
(header), `random_matrix/goe_edge.v`; `MatrixSeriesStatement.v`,
`TensorPackingStatement.v`, `GoeEdgeStatement.v`,
`PsdSplittingStatement.v`, `SKGapDefinitions.v`, `SKGapStatement.v`,
`PerceptronSignDefinitions.v`, `PerceptronSignStatement.v`,
`SatVarianceDefinitions.v`, `SatVarianceStatement.v`,
`Perceptron/Pressure.v`, and the rows of these files. The theorem
wrappers `MatrixSeriesTheorem.v`, `TensorPackingTheorem.v`,
`PsdSplittingTheorem.v` and `PerceptronSignTheorem.v` call the library or
proof file, not themselves, a Rocq formalization of the credited
argument. I read that as meeting rule (1) for a wrapper, so I propose no
change. `RandomSAT/Model.v` of main is replaced by lane B's file in
598614d.

### `library/matrix/spectral_gap.v` (lane C), lines 20-25

Rules (1) and (4). The header does not call the file a Rocq formalization
of the credited argument and does not say whether it follows a Lean
module. It also describes the model beyond the citation ("the spectral gap
of the heat-bath dynamics of the Sherrington-Kirkpatrick model in
applications/SKGap/"). The two bounds are two steps of the proof of the
proposition (entropy.tex, lines 358-413): "the maximum absolute row-sum
bound for symmetric matrices", and the passage from
`|Af|^2 >= kappa <f, Af>` to the gap. Proposed paragraph:

> This file is a Rocq formalization, in general form, of two steps of the
> credited argument of the proposition 'Gap and covariance under scaled
> interactions and fields' of 'Cutoff throughout the high-temperature
> Sherrington-Kirkpatrick phase' (family 227 of the OpenAI math
> collection, revision 1581d4cbd, appendices/entropy.tex): the row-sum
> bound for the operator norm of a symmetric matrix, and the gap read
> from the inequality |A f|^2 >= kappa <f, A f>. Target T4 of phase 12
> (AGENTS.md, section Phase 12) uses both. The file follows no Lean
> module.

If it does follow a Lean module, replace the last sentence by `Lean:`
lines.

### `library/matrix/lambda_max.v` (lane C), lines 16-22 and 31-33

Rule (1): the header cites the title, the family and the revision, but
not the section or lemma where lambda_max occurs, and it does not call
the file a Rocq formalization of the credited argument. lambda_max(W)
occurs in the proof of the proposition 'Good disorder'
(appendices/entropy.tex, lines 136-143). The Lean modules write it as
the supremum of a Gaussian process over the unit ball (`diagonalProcess`,
`Matrices/UnitBall.lean`, line 78, in `goe_expected_top`) and have no
separate definition of the largest eigenvalue. Proposed paragraph:

> The definition is alone in the section lambda_max, which is frozen with
> the statement of target T3 of phase 12 (AGENTS.md, section Phase 12;
> the sharp upper edge of the GOE): the source checker of scripts/
> compares its code and the Require commands of this file with the
> acceptance commit fc76edf. The lemmas below it may grow. The file is a
> Rocq formalization of the largest eigenvalue lambda_max(W) of the
> credited argument of the proof of the proposition 'Good disorder' of
> 'Cutoff throughout the high-temperature Sherrington-Kirkpatrick phase'
> (family 227 of the OpenAI math collection, revision 1581d4cbd,
> appendices/entropy.tex). It follows no Lean module.

Rule (3), lines 31-33: `eigenvalue_le_lambda_max` needs neither `n > 0`
nor a symmetric `A`. Proposed:

> - lambda_max_eigenvector, eigenvalue_le_lambda_max: for n > 0 and A
>   symmetric, lambda_max A is an eigenvalue of A; for every A, every
>   eigenvalue of A with a unit eigenvector is at most lambda_max A.

### `applications/SKGap/Ising.v` (lane C), lines 12-18

Rule (1): the header cites no Lean module and does not say that it
follows none. Its pair law (`ising_weight_block`, the weights
K (1 + a x)(1 + b y)(1 + t x y)) is the pair law of the Lean module
`Calculus/TwoSpin.lean`: `pairBaseMass` (line 243) is
(1 + a x)(1 + b y)/4 and `pairDensity` (line 342) is
(1 + u x y)/(1 + u a b). Its conditional variance v_i is
`conditionalVariance` of `Calculus/PlusSpin.lean` (line 232). If the file
follows these modules, add after line 18:

> The Lean counterparts, in lean/OAI/Probability/SKRatio of the
> collection:
> Lean: pairBaseMass (Calculus/TwoSpin.lean, line 243)
> Lean: pairDensity (Calculus/TwoSpin.lean, line 342)
> Lean: conditionalVariance (Calculus/PlusSpin.lean, line 232)

Otherwise add: "The file follows no Lean module."

### `library/probability/log_partition.v` (lane A), lines 10 and 25

Rule (3): the four results of its README row, `gibbs_mean_le`,
`is_derive_gibbs_mean`, `is_derive_log_partition` and
`log_partition_derive3`, assume a nonempty `X` (`0 < #|X|`; checked on
their discharged statements), and the header does not say so. Line 10:
"For a finite type X" becomes "For a nonempty finite type X". Rule (4),
optional, line 25: "The manuscript bounds the third derivative of the
normalized pressure by bounded Gibbs moments" becomes "The manuscript
bounds this third derivative by bounded Gibbs moments".

### `library/README.md` (rows of lanes A and C), lines 111, 142, 212 and 214

Rule (3), the rows and the proved statements:

- Line 111 (`matrix/lambda_max.v`, lane C): as in the header,
  "For `n > 0` and `A` symmetric, `lambda_max A` is an eigenvalue of `A`
  with a unit eigenvector, and every eigenvalue of `A` with a unit
  eigenvector is at most `lambda_max A`." becomes "For `n > 0` and `A`
  symmetric, `lambda_max A` is an eigenvalue of `A` with a unit
  eigenvector. For every square `A`, every eigenvalue of `A` with a unit
  eigenvector is at most `lambda_max A`."
- Line 142 (`matrix/tensor_packing.v`, lane A): `almost_orthogonal_sum_le`
  and `almost_orthogonal_card_le` assume `0 <= eta`. "Almost orthogonal
  families: if `<v_a, v_a> <= 1`" becomes "Almost orthogonal families:
  if `eta >= 0`, `<v_a, v_a> <= 1`".
- Line 212 (`probability/log_partition.v`, lane A): "For a finite type
  `X`" becomes "For a nonempty finite type `X`".
- Line 214 (`probability/rademacher_lindeberg.v`, lane A), optional:
  `derive_le_cmp` assumes `a <= b` and `g`, `k` differentiable on all of
  `R`. "The mean value inequality `\|g b - g a\| <= k b - k a` when
  `\|g'\| <= k'` on `[a, b]`" becomes "The mean value inequality
  `\|g b - g a\| <= k b - k a` for `a <= b` and `g`, `k` differentiable
  everywhere with `\|g'\| <= k'` on `[a, b]`".

### `library/random_matrix/goe_entries.v` (lane A, T4b), lines 49-51

Rule (4): the header describes the model beyond the citation ("the row
sums of the disorder; the proposition itself is in
applications/SKGap/Disorder.v"). Proposed, from line 49:

> revision 1581d4cbd, file appendices/entropy.tex), for the diagonal
> entries, the off-diagonal entries and the row sums of the GOE matrix;
> the proposition itself belongs to target T4. It follows the TeX, not a
> Lean module of the collection.

Rule (3), optional, in `library/README.md`: the row of line 377 says
that the three union events are measurable; its results could also list
`measurable_goe_diag_max`, `measurable_goe_offdiag_max` and
`measurable_goe_row_max`. The row of line 376 could say "A Rocq
formalization of the credited argument" instead of "A formalization of an
argument", as the header does.

`applications/SKGap/Disorder.v` (T4b): no finding. Its header meets
rules (1) and (2) (delta fixed instead of n^(-1/4), and the cubic row
sums left out), and its row matches `sk_good_disorder`,
`sk_good_disorder_measurable` and `sk_good_disorder_prob`.

### T4a: `applications/README.md`, line 85, and `library/README.md`, line 215

The T4a files reached main at 88a5dd4. The headers of
`applications/SKGap/TwoSpin.v`, `Poincare.v`, `Spectral.v`,
`applications/SKGapTheorem.v` and `library/probability/finite_gap.v` meet
rules (1), (2) and (4): each cites the lemma or proposition, the title,
the family, the revision and the source file, calls the file a Rocq
formalization of the credited argument, and names the Lean module it
follows or says that it follows none; the differences with the TeX and
the Lean module (the polynomial certificate, the constants t_0 and C_0,
the explicit tolerance for every n) are stated. The rows of `Spectral.v`,
`TwoSpin.v`, `SKGapTheorem.v` and `finite_gap.v` match the proved
statements. Two points:

- `applications/README.md`, line 85 (`SKGap/Poincare.v`, lane C), rule
  (3): `ising_cov_from_gap` assumes `0 < k`. "From `k Var_nu <= E` for all
  `f`: `opnorm Cov_nu(x) <= 1 / k`." becomes "For `k > 0`, from
  `k Var_nu(f) <= E(f)` for all `f`: `opnorm Cov_nu(x) <= 1 / k`."
- `library/README.md`, line 215 (`probability/finite_gap.v`, lane A),
  optional: "A formalization of an argument of family 227" could be "A
  Rocq formalization of the credited argument of family 227", as the
  header says.

The review is complete: every file that phase 12 added or changed under
`applications/` and `library/` up to main 88a5dd4 has been checked.
