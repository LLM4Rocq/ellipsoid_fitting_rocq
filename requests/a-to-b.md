# Requests of lane A to lane B

## Cross-lane review of the new library files of phase 13 (15 October 2026)

Asked by the master on 15 October 2026, under the rule of AGENTS.md,
section Phase 13, "Library and applications" (before the release, a
lane other than its author reviews each new library file for models):
`library/probability/binomial_mean.v`, `commuting_operators.v` and the
phase 13 additions to `finite_mean.v`, at lane/b aa94052. The three files
are unchanged at lane/b da44b33. Line numbers are those of aa94052. The
six checks are those of the master's request:

1. no model;
2. statements in the weakest structure that suffices;
3. no duplicate of a MathComp, MathComp-Analysis or library lemma;
4. the provenance header;
5. README rows with the actual hypotheses;
6. an example independent of any application at the end.

How (3) was checked: the declarations of the MathComp 2.6 and
MathComp-Analysis 1.16 sources of the pinned image were searched
(`binomial.v`, `binomial_distribution.v`, `ssralg.v`, `ssrnat.v`,
`boolp.v`, `functions.v`), and `library/` and `applications/` with
`git grep`. For (4), all 26 `Lean:` lines of the three headers were
compared with the Lean sources of the collection; each names the
declaration at the cited line.

`library/combinatorics/binomial_bounds.v` (item X), whose statements
landed on lane/b in f496d29 during this review, is reviewed in the last
section, at f496d29.

### `library/probability/finite_mean.v`, the additions of phase 13

Checks 1 to 6: no finding.

- (1), (2) The bounds are general, over a `realFieldType`, as the plan
  asks.
- (3) MathComp-Analysis has Markov's and Chebyshev's inequalities only
  for measures. The T7 lemma `unif_mean_tuple_prod` (line 236) is the
  constant case of `unif_mean_tuple_prod_ord`, so it is a special case
  and not a duplicate.
- (4) The header cites the lemma 'Bounds on the centers'
  (anchors.tex), the proposition 'Polynomial concentration', the
  revision and five `Lean:` lines.
- (5) Row 175 states every hypothesis.
- (6) `unif_mean_fair_bits` is independent of any application.

### `library/probability/binomial_mean.v`

Checks 1, 2, 4 and 6: no finding.

- (1), (2) The statements are over a `numDomainType`; Chebyshev's
  inequality and the exchange with `unif_mean` are over a
  `realFieldType`, and the bridge is over a `realType`. This is what the
  plan asks. The comments name clauses and the satisfiability threshold
  only in the provenance paragraph (lines 41-62).
- (4) The header cites the title, family 235, the revision, the lemmas
  'Auxiliary product inequality' and 'Proper-clause transfer'
  (convergence.tex) and eleven `Lean:` lines. It states the departures:
  fixed numbers of clauses and binomial mixtures instead of Poisson
  counts, and the closed form as the definition instead of Lean's
  recursion.
- (6) `binomial_prob_mean_var` is independent of any application. The
  header is right that MathComp-Analysis 1.16 does not state the mean or
  the variance of `binomial_prob`: `binomial_distribution.v` has
  `binomial_pmf`, `integral_binomial` for nonnegative functions and
  `integral_binomial_prob`, nothing more.

**Check 3, `applications/RandomSAT/Forcing.v` (T7) on main, lines 72-160.**
The library file duplicates nothing in MathComp, MathComp-Analysis or
`library/`. But `Forcing.v` keeps its own `binom_mean`, defined by the
recursion on the first trial, with twelve lemmas that the library now
has: `eq_binom_mean`, `binom_mean_cst`, `binom_meanD`, `binom_meanZ`,
`binom_meanN`, `binom_meanB`, `ler_binom_mean`, `binom_mean_id`,
`binom_mean_trials_le`, `binom_mean_trials`, `binom_mean_sum` and
`unif_mean_binom_mean`. So T9 uses `binomial_mean` and T7 uses
`binom_mean`. I propose, once packet S is accepted, to prove
`binom_mean p m f = binomial_mean m p f` by induction on `m` with
`binomial_meanS`, and to replace these lemmas of `Forcing.v` by those of
`binomial_mean.v`. No frozen file uses `binom_mean`: it occurs only in
`Forcing.v`.

**Check 5, row 176 of `library/README.md`.** The row gives Chebyshev's
inequality without its hypotheses: `binomial_chebyshev` (lines 320-323)
assumes `0 <= p <= 1` and `0 < t`. I propose "Chebyshev's inequality
`P(|J - m p| >= t) <= m p (1 - p) / t^2` for `p` in `[0, 1]` and
`t > 0`".

**Use (information, no change asked).** Five lemmas are used neither by
T9 at lane/b da44b33 nor in `library/`, except by the example:
`binomial_chebyshev`, `binomial_mean_trials` (with
`binomial_mean_trialsS`), `unif_mean_binomial_mean`, `binomial_meanE`
and `integral_binomial_mean`. Section 3 of the plan lists them
(Chebyshev, monotonicity in the number of trials, the bridge to
`binomial_pmf`) for T9 or phase 14. Under the rule "Generalize only
where it pays", they stay only if phase 14 uses them.

### `library/probability/commuting_operators.v`

Checks 1, 2, 4 and 6: no finding.

- (1), (2) The statements are general: a `porderType` for the comparison
  of iterates, a `numDomainType` for operators, a `realFieldType` for
  `meet_avg`. The comments name constraints and solutions only in the
  provenance paragraph (lines 45-67).
- (4) The header cites the title, family 235, the revision, the same
  two lemmas of convergence.tex and seven `Lean:` lines. It states the
  departures: fixed counts instead of marked Poisson families, and the
  comparison for sub-commuting monotone maps at one point instead of
  Lean's exactly commuting operators.
- (6) `lazy_walk_binomial` is independent of any application.
- `homo_iter` is not in MathComp: `ssrnat.v` has only `iter_in`, for
  membership.

**Check 3, lines 89-95 and 237-261.** `linear_op` restates, pointwise,
MathComp's `linear` (ssralg) for maps of the module of functions
`X -> R`, which MathComp provides in `classical/functions.v` (section
`fct_lmod`). Likewise, `linear_op0` and `linear_op_sum` restate `linear0`
and `linear_sum`. `monotone_op` is `{homo A : f g / (f <= g)%O}` for the
pointwise order of `boolp.v`, which `monotone_iter_le` already reaches
through `lefP`. A `Prop` on plain functions is a reasonable choice for
hypotheses, so no change is required. I propose a sentence in the header
that says why MathComp's linear maps are not used, for example:
"linear_op is the pointwise form of MathComp's linearity (linear) for
the module of functions X -> R of classical/functions.v; it lets the
hypotheses be stated on plain functions."

**Check 5, row 178 of `library/README.md`.** `iter_scale` assumes
`linear_op A` (lines 270-273), and the row leaves this out ("the iterate
of `c A` is `c^m` times that of `A`"). I propose "for a linear `A`, the
iterate of `c A` is `c^m` times that of `A`".

**Use (information, no change asked).** `meet_avg_cst` is used neither
by T9 at lane/b da44b33 nor in `library/`.

### `library/combinatorics/binomial_bounds.v` (statements, lane/b f496d29)

Line numbers are those of f496d29. Nothing is proved yet, so checks 5
and 6 wait for the proofs: the file has no README row and no example
yet.

Checks 1 and 2: no finding.

- (1) No statement mentions a model.
- (2) The coefficient bounds are in `nat`, as the plan asks. Only
  `bin_partial_sum_statement` is over a `realType`; it needs `expR`, as
  `bin_le_expR` of `matrix/nets.v` does.

All eight statements hold numerically. This was checked with exact
integers, and in floating point for the partial sums: the central
bounds for n < 1500, `half_bin_ge` for h < 1500, `leq_bin_half` for
n < 300, `bin_near_half` for h < 400 with every allowed T and g,
`bin_sqr_central` and `bin_sqr_ratio` for j <= u < 300, and
`bin_partial_sum` for M <= N < 200. This guards against a false
statement before the user's review; it is not a proof.

**Check 3, lines 90-93.** `bin_partial_sum_statement` restates a library
result. `small_sets_le` (`random_matrix/restricted_isometry.v`, line 594
on main, lane C) bounds the number of subsets of size at most `s` of
`'I_N` by `(expR 1 * N / s) ^+ s` for `0 < s <= N`. `card_small_sets`
(line 574) shows that this number is `\sum_(j < s.+1) 'C(N, j)`, and the
proof of `small_sets_le` proves the sum form first. Only the case
`M = 0` is new. Proving the statement from those two lemmas would make
`combinatorics/` depend on `random_matrix/`, which imports measure
theory. So I propose to prove the sum form here and, optionally, to ask
lane C through the master to derive `small_sets_le` from it, so that the
proof exists once. The other seven
statements are not in MathComp (`binomial.v` has no central,
unimodality or near-center bound) and not in `library/`. `bin_le_expR`
is the bound on one coefficient, as the header says.

**Check 4, lines 20-22.** The header cites
"reviews/phase13-psd-audit.md, Part 2", a file outside the repository
(`/srv/ellipsoid-fitting/reviews/`). A reader of the repository cannot
follow the reference, and no other library file cites a document outside
the repository. I propose: "The manuscript uses the estimates without
proof and leaves their constants unspecified; the statements below fix
constants that suffice for its two uses." The other references hold:
local-averaging.tex, lines 155-176, has local:central-ratio, the identity
and local:binomial-ratio, and parity.tex, lines 60-67, has the partial
sum.

**Check 1, comments, lines 45-47 (optional).** "In the expander lemma,
with N = 100 a, it gives (20 e)^(5 a) at M = 5 a and (100 e a / w)^w at
M = w, the two crude chains of the audit" describes the parameters of
the application and the audit, beyond a citation. I propose: "The
manuscript uses it at M = N / 20 (parity.tex, lines 60-67)."
