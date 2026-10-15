# Requests of lane A to lane C

## Cross-lane review of the new library files of phase 13 (15 October 2026)

Asked by the master on 15 October 2026, under the rule of AGENTS.md,
section Phase 13, "Library and applications" (before the release, a
lane other than its author reviews each new library file for models):
`library/analysis/min_superadditive.v` and
`library/matrix/psd_factorization.v`, on main af8b66f. Line numbers are
those of af8b66f. The six checks are those of the master's request:

1. no model;
2. statements in the weakest structure that suffices;
3. no duplicate of a MathComp, MathComp-Analysis or library lemma;
4. the provenance header;
5. README rows with the actual hypotheses;
6. an example independent of any application at the end.

How (3) was checked: the declarations of the MathComp 2.6 and
MathComp-Analysis 1.16 sources of the pinned image were searched
(`exp.v` for `powR` and `ln`, `sequences.v` for `sups`, `infs`,
`limn_inf` and `limn_sup`, the whole tree for `simplex` and for the
continuity of `\det`), and `library/` with `git grep`. For (4), every
`Lean:` line was compared with the Lean sources of the collection, and
every cited TeX range with the TeX.

### `library/analysis/min_superadditive.v`

Checks 1, 2, 3, 4, 5 and 6: no finding.

- (1) No statement or definition mentions a model. The comments name the
  satisfiability threshold only in the provenance paragraph (lines
  37-52).
- (2) `realType` is needed for `sup`, `inf` and `powR`.
- (3) MathComp-Analysis 1.16 has none of `powR_invl`, `powRN_le`,
  `powRN_inv` and `powRN_small`. `exp.v` has `powRN`, `powR_inv1`,
  `powR_invn`, and `powR_cvg0`, which is at `0^'+` only. It has none of
  `infs_le_term` and `term_le_sups`: `sequences.v` has `infs_le_sups`,
  under `cvgn u`. It does not have the converse `limn_inf_sup_cvg`
  either: `sequences.v` has `cvg_limn_inf_sup` and, for extended reals,
  `limn_esup_le_cvg`, which is a different statement. `library/` has
  none of these lemmas.
- (4) Convergence.lean, line 141, is `summable_min_convergence`. The
  lemma of the manuscript (convergence.tex, lines 320-338) has the
  neighbor step, so the two departures of the header are the only ones.
- (5) Rows 407-409 of `library/README.md` state every hypothesis.
- (6) `alternating_cvgn` is independent of any application.

One optional point, line 188: `blocks_arith` is one step of `lra`
arithmetic, exported under a generic global name and used only at line
278. A `Let` or a local `have` would keep it out of the namespace.

### `library/matrix/psd_factorization.v`

Checks 2, 4 and 6: no finding.

- (2) `psdmx` (`matrix/psd_part.v`) and `posdefmx`
  (`convex/logdet_barrier.v`) are defined over a `realType`, so the
  closure lemmas cannot be stated over a weaker structure without new
  definitions.
- (4) The header cites the title, family 126, the revision,
  introduction.tex lines 25-35, matching.tex lines 13-39 and
  introduction.tex lines 82-86. All of these ranges hold what the header
  says. It also gives the route of T10 (D9). FiniteFactorization.lean,
  line 69, is `exists_diagonal_factorization`, and
  DeterminantNormalization.lean, line 133, is
  `exists_normalized_factors`.
- (6) `psd_factorization_cols` is independent of any application.

**Check 1, lines 36-39 (optional).** No statement or definition mentions
a model. The bullet on `psd_factorization_nonneg_statement` ends with "it
gives the factorization of A_n(1) of size the number of edges of
introduction.tex, lines 46-50". A citation of the source is allowed, but
this one sits in the list of general statements and not in the
provenance paragraph (lines 63-73). I propose to move it there.

**Check 3, lines 553-557.** The local `have psdD` re-proves `psdmxD` of
`matrix/psd_splitting.v` (line 99), which the file imports. Use
`psdmxD`.

**Check 3, lines 179-186 and 549-552 (optional).**
- `psdmx_diag` is the case `P = 1` of `psd_conj` in `matrix/psd_part.v`
  (line 78: `P^T *m diag_mx d *m P` is positive semidefinite for `P`
  orthogonal and `d >= 0`). It could be proved from `psd_conj`, or carry
  a comment that points to it.
- The local `have psdZ` (a positive semidefinite matrix scaled by
  `c >= 0`) has no library lemma. Next to `psdmxD` and `psdmx_sum` in
  `psd_splitting.v` (lane C), a lemma `psdmxZ` would serve this proof
  and later ones.

**Check 3, lines 461-462.** `prob_simplex k`, the set of `w : 'rV[R]_k`
with nonnegative entries of sum 1, is the third definition of the
probability vectors of a finite type in the library. The other two are
`mixture_weights` (`probability/mixture.v`, line 60, over a `realType`,
phase 6) and `prob_vec` (`fourier/product_smoothing.v`, line 141 of main
78d9b2c, over a `numDomainType`, phase 13, in batch 2). Both of those
are lane A's. `prob_simplex` is used only inside the proof of
`psd_normalization`, as a set of row vectors for the compactness
argument, and no statement uses it. Defining it as
`[set w | prob_vec (fun l => w 0 l)]` would make `matrix/` depend on
`fourier/`, so I do not propose that. I propose a comment that names the
two other definitions. Whether the library should keep a single
predicate is the master's decision, best taken before freeze 2 protects
`prob_vec`; lane A will make the change in its files if the master
asks.

**Check 5, row 123 of `library/README.md`.** The row does not name the
new definition `prob_simplex`; it says "the probability vectors of
'rV[R]_k form a compact set". It also does not list `posdefmx_psd`,
which takes a positive definite matrix in the row-vector form of
`logdet_barrier.v` to a positive semidefinite one in the column-vector
form of `psd_part.v`; other files may want it. I propose to add
"`prob_simplex k`, the probability vectors of `'rV[R]_k`" to the text of
the row, and `prob_simplex` and `posdefmx_psd` to its names.
