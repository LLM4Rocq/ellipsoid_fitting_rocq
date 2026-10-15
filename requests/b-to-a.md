# Requests of lane B to lane A

## Cross-lane review of the new library files of lane A (15 October 2026)

Asked by the master on 15 October 2026, under the rule of AGENTS.md,
section Phase 13, "Library and applications" (before the release, a
lane other than its author reviews each new library file for models):
`library/fourier/boolean_fourier.v`, `library/fourier/product_smoothing.v`
and `library/matrix/psd_duality.v`, with their rows 125-126 and 384-395
of `library/README.md`, at lane/a 78a5188. Line numbers are those of
78a5188. The six checks are those of the review of lane A
(requests/a-to-b.md on lane/a):

1. no model, except in the provenance paragraphs;
2. statements in the weakest structure that suffices;
3. no duplicate of a MathComp, MathComp-Analysis or library lemma;
4. the provenance header;
5. README rows with the actual hypotheses;
6. an example independent of any application at the end of each module.

How (3) was checked: the sources of MathComp 2.6 and MathComp-Analysis
1.16 of the pinned image were searched, and `library/` and
`applications/` at 78a5188 with `git grep`. The replacements proposed
for `bdot` and `linearD_prop` were compiled against the files (`bdot p y =
mxdot p y` holds by `[]`). For (4), every cited range of the TeX was
read, the six `Lean:` lines of `psd_duality.v` were compared with the
Lean sources of the collection (each names the declaration at the cited
line), and the claims "it follows no Lean module" were checked against
`lean/OAI/Combinatorics/MatchingPSD`: it has no Fourier analysis on
`F_2` and no product smoothing (its `MatchingSmoothing` files smooth
functions of matchings, for the other sections of the manuscript).

Nothing in this file asks to change a statement: the user has not
answered the review of the statements yet.

### `library/fourier/boolean_fourier.v`

Checks 1, 2, 5 and 6: no finding.

- (1) The model appears only in the provenance paragraph (lines 96-112:
  the title, the parity functional and matching.tex).
- (2) The characters are over a `pzRingType`, the coefficients over a
  `numFieldType`, `sum_col_mx` over an `nmodType`. Only `fcoef_norm_le`
  uses the norm; the rest of the coefficient theory would hold over a
  field in which 2 is invertible, but `numFieldType` is the natural
  class here, and no use needs more.
- (5) Rows 384-389 state the hypotheses: the bilinearity of `b` in
  Plancherel's identity, `|f y| <= c` for `fcoef_norm_le`, the support
  condition of `low_blk_deg_translate`.
- (6) The file ends with `bchar_one_bit` and `fcoef_bchar` (lines
  744-755), independent of any application.

**Check 3, lines 138 and 352-376: `bdot` is `mxdot` at `'F_2`.**
`bdot p y = \sum_i \sum_j p i j * y i j` (line 138) is, word for word,
`mxdot` of `matrix/euclidean.v` (line 32), which is defined over any
`comNzRingType`; `'F_2` is one, and `bdot p y = mxdot p y` holds by `[]`.
So `bdotC`, `bdotDl`, `bdotDr`, `bdot0l` and `bdot_delta` (lines 352-376)
are `mxdotC`, `mxdotDl`, `mxdotDr`, `mxdot0l` and `mxdot_delta`
(euclidean.v, lines 34, 37, 44, 71 and 135) at `'F_2`; only
`bdot_col_mx` (line 632) is new. I propose, without changing any
statement or definition text: add `bdotE : bdot p y = mxdot p y` (by
`[]`) and prove the five lemmas from it in one line each (for example
`by rewrite !bdotE mxdotC`), or replace their uses by the `mxdot`
lemmas. Defining `bdot` as `mxdot` would change a definition that the
batch 2 statements unfold to, so that part is the user's decision.

**Check 3, lines 320-345 (information).** MathComp states the
consequences of the predicate `linear` for plain maps:
`GRing.semilinear_linear` gives additivity and scalability (so
`linearD_prop` is `(GRing.semilinear_linear hl).2`, checked), and
`scalable_linear` is already used for `linearZ_prop`. `linear0_prop`
and `linear_sum_prop` are `linear0` and `linear_sum` after packing `h`
with `GRing.isLinear.Build`. As in the review of lane A of my
`linear_op`, keeping lemmas on plain maps is a reasonable choice; the
header (lines 67-69) could say why the structure `{linear U -> W}` is not
used.

**Check 3, line 309 (information).** `signF2D` is the `'F_2` form of
MathComp's `signr_addb`, `(-1) ^+ (b1 (+) b2) = (-1) ^+ b1 * (-1) ^+ b2`
for booleans. No change asked.

**Check 4, lines 12 and 111 (wording).** "a module V over a number
field R": a number field is a finite extension of the rationals. I
propose "over a numFieldType R" (or "a numeric field"). The other
references hold: fourier-smoothing.tex lines 12-40 (the characters and
the block degree) and 42-98 (the theorem), parity.tex lines 107-117 and
271-283, matching.tex lines 148-193, and the absence of Boolean
characters in the Lean development.

### `library/fourier/product_smoothing.v`

Checks 1 and 4: no finding.

- (1) The model appears only in the provenance paragraph (lines 89-114);
  "the application draws subsets of two sizes" (line 98) explains a
  departure without naming the model.
- (4) Title, family 126, the theorem 'Fourier smoothing of matrix
  squares' (fourier-smoothing.tex, lines 42-98), the revision, and the
  departures, including lambda > 0 for lambda > 1 and the shared
  witnesses of the user's amendment 4. The claim that the Lean
  development has neither Boolean characters nor product smoothing
  holds (see above).

**Check 6, lines 177-183 and 1193.** The only example,
`prob_vec_uniform`, sits after the definitions (lines 177-183); the
file ends with `product_smoothing_coef` (lines 1175-1193). I propose to
move the example to the end, or to add one there. One that shows the
hypotheses at work: constant channels, `pi i m z = mu i`, satisfy
`smoothing_hyps mu nu pi 0` for any probability vectors `mu i` and
`nu i`, since the marginal identity is `\sum_m nu i m mu i x = mu i x`
and the variance term vanishes.

**Check 5, row 393.** The row gives no hypotheses for
`smoothing_step_one` and `smoothing_param`. `smoothing_step_one` assumes
the section hypotheses of lines 604-611: `mu`, `nu` and every channel
are probability vectors, the marginal identity, the variance
contraction, `lambda > 0` and `2^a lambda^2 2^(2^a - 1) theta <= 1`;
`smoothing_param` (lines 923-928) assumes `rho >= 0`,
`smoothing_hyps`, `F` positive semidefinite, `lambda > 0` and the same
condition. I propose "under the hypotheses of T11 for one coordinate"
for the first and "under the hypotheses of T11, with nonnegative
weights rho" for the second.

**Check 5, row 394.** "for `C = \sum_i w_i h_i h_i^T` with `w >= 0`":
`mxtrace_gram_mul`, `frobenius_gram` and `mxtrace_gram` (lines 239-266)
hold for any weights; only `mxtrace_gram_le` and `psdmx_gram` assume
`w >= 0`. I propose to attach "with `w >= 0`" to those two.

**Check 3, lines 429-439.** `sum_prod_prob` follows in one line from
`big_tuple_distr` of `probability/mixture.v` (line 335),
`\sum_(s : n.-tuple I) \prod_k F k (tnth s k) = \prod_k \sum_i F k i`,
since each probability vector sums to one. I propose to derive it from
that lemma.

**Check 3 (information, no change asked).**

- `mxtrace_gram` and `psdmx_gram` (lines 261 and 359) are the weighted
  forms of `gram_trace`, `gram_sym` and `gram_form_ge0` of
  `matrix/tensor_packing.v` (lines 573-584, lane A, phase 12), which
  could be derived from them.
- `sum_wsqr_le` (line 192) overlaps `sum_cauchy_schwarz` of
  `matrix/euclidean.v` (line 182), with `a_i = sqrt w_i` and
  `b_i = sqrt w_i z_i`; the direct proof avoids square roots, which is a
  reason to keep it.
- `mxtrace_le_frobenius` (line 269) also follows from `mxdot_le_nuclear`
  and `nuclear_le_frobenius` of `matrix/nuclear.v` (lines 97 and 157),
  since `\tr A = mxdot A 1%:M`; the direct proof is as short.
- `sum_tuple_cons` (line 404) is a reindexing by `bij_tuple_cons` of
  `probability/finite_mean.v` (line 209).

**Check 2 (optional).** The sections `matrix_tools`, `prob_tools` and
`channel_tools` (lines 188, 402 and 476) fix a `realType`, but
`sum_wsqr_le`, `exists_weight_le` and `contraction_ge0` hold over a
`realDomainType`, `sum_prod_prob` and `prod_prob_ge0` over a
`numDomainType` like `prob_vec`, and `prod_tuple_cons` over any
`comPzSemiRingType`; the other lemmas use `frobenius` or `Num.sqrt`.
These are tools of the proof, so this matters little.

### `library/matrix/psd_duality.v`

Checks 1 to 6: no finding.

- (1) The first paragraph (lines 15-20) speaks of exact semidefinite
  lifts and slack matrices, general notions; the model appears only in
  the provenance paragraph (lines 48-61).
- (2) Everything is over a `realType`, which `psdmx`, the topology and
  Moreau's decomposition need.
- (3) `psdmx_factor`, `psdmx_outer` and the self-duality are not in
  the library: no lemma gives a positive semidefinite matrix as `H^T H`
  or `x x^T` as positive semidefinite. `psdmx_frobenius_le_trace` also
  follows from `frobenius_le_nuclear` and `nuclear_spectral` of
  `matrix/nuclear.v`, but its direct proof is two lines.
- (4) The title, family 126, the corollary 'Unshifted rank and exact
  lifts' (introduction.tex, lines 94-113, the cone-factorization step),
  the revision, the departures, and the six `Lean:` lines, which name
  `evaluation` and `evaluationCone` (PSDEvaluation.lean, lines 10 and
  19), `evaluationCone_isClosed` (OrthogonalCone.lean, line 39),
  `psd_of_trace_nonneg` and `exists_psd_evaluation` (PSDDuality.lean,
  lines 33 and 44) and `affine_slack_certificate` (AffineCertificate.lean,
  line 12). The departure about the slack certificate matches the Lean
  statement (an affine subspace and an affine map).
- (5) Rows 125-126 state every hypothesis. After the acceptance, the
  "Result" column of row 125, which lists the `_statement` names, should
  list the lemmas.
- (6) The file ends with `psd_eval_cone_trace`, independent of any
  application.
