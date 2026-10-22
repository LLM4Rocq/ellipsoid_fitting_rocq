# Requests of lane B to lane A

## Review of the new library files of lane A for models (22 October 2026)

Under AGENTS.md, section Phase 14, "Library and applications": before the
release, a lane other than its author reviews each new library file for
models (plan, section 18, point 16). The files are
`library/matrix/multiplicity.v` and `library/combinatorics/harmonic.v`,
with their rows 127-132 and 434 of `library/README.md`, at main 4d020691.
Line numbers are those of 4d020691. The checks are those of the
cross-lane review of phase 13:

1. no model, except in the provenance paragraphs;
2. statements in the weakest structure that suffices;
3. no duplicate of a MathComp, MathComp-Analysis or library lemma;
4. the provenance header;
5. README rows with the actual hypotheses;
6. an example independent of any application at the end of each module.

How it was checked:
- (1) both files were read in full; and `grep -i` found none of cell,
  frame, incidence, odd cut, parity, matching, lift, channel and charge
  outside the provenance paragraphs.
- (3) the sources of MathComp 2.6 and MathComp-Analysis 1.16 of the
  pinned image and `library/` were searched.
- (4) every cited range of the TeX was read, and the four `Lean:` lines of
  `multiplicity.v` were compared with the Lean sources of the collection.

Nothing here asks to change a statement: batch 1 is under the user's
review.

### `library/matrix/multiplicity.v`

No finding.

- (1) The model appears only in the provenance paragraph (lines 62-76),
  which names the lemma on local averaging of the manuscript. `ksubset`,
  `ksubset_mx` and `kact` are the action of the permutations of `'I_k` on
  the `w`-subsets, a general object (the Johnson scheme); the statements
  speak of permutation matrices and orthogonal projections only.
- (2) The matrix results are over a `realType`, which `sym_eigenproj`
  needs for the spectral theorem of `real_spectral.v`. `perm_map_uniq`
  and `tperm_disjC` are over a `finType`, as `{perm T}` requires.
- (3) No duplicate:
  - `sym_eigenproj` projects onto the eigenspace of one eigenvalue c.
    `spectral_nonneg_proj` of `psd_splitting.v` projects onto the
    nonnegative part of the spectrum, which is a different object.
  - `mxtrace_orthoproj_ge0` would also follow from `mxtrace_psd_ge0` of
    `psd_splitting.v` with the identity, but no lemma states it.
  - MathComp has `tpermC` (a transposition is symmetric in its two
    points) but no commutation of disjoint transpositions, and no
    statement of `perm_map_uniq`; `tuple_permP` is about tuples
    indexed by `'I_n`.
- (4) The cited ranges of `local-averaging.tex` are right: lines 191-246
  are the step "From trace to contraction", lines 197-223 the claim on
  invariant subspaces, and lines 225-234 the bound (k/2) mu^2 <=
  tr(K^2) - 1. The four `Lean:` lines name the declaration at the cited
  line:
  - `simultaneous_sign_eigenvector` and `independent_eigenprofiles` of
    `Involutions.lean`, at lines 70 and 109;
  - `eigenspace_dim_mul_sq_le_trace_square` and
    `quadratic_form_le_of_multiplicity` of `SpectralMultiplicity.lean`,
    at lines 24 and 55.

  The departures are stated: traces of projections instead of
  dimensions, the route of the audit, and k >= 5 being enough for the
  proof.
- (5) The rows match the statements:
  - rows 127-130: the hypotheses of `trace_multiplicity`, `sym_eigenproj`,
    `orthoproj_family_trace` and `sign_refine`, the two curried
    hypotheses on Q included;
  - row 131: `perm_map_uniq` and `tperm_disjC`;
  - row 132: `kact_exchange` with k >= 3, x in A and y not in A, and
    `kact_cycle_const`.
- (6) `ksubset_multiplicity_six` (lines 1029-1038) is about the 3-subsets
  of `'I_6`, with no application.

### `library/combinatorics/harmonic.v`

No finding.

- (1) The manuscript appears only in the provenance paragraph (lines
  20-27).
- (2) A `realType` is what `ln` of MathComp-Analysis needs.
- (3) MathComp-Analysis has the terms of the harmonic series (`harmonic`
  of `sequences.v`) and its divergence, but no bound on its partial sums;
  the header says so.
- (4) Lines 177-185 of `local-averaging.tex` are the sum of 1/j for j
  from 1 to g* + 1 and its bound O(log(h + 2)), used without proof.
- (5) Row 434 matches `harmonic_ln`: n > 0, any `realType`.
- (6) `harmonic_ln_four` is a numerical instance, with no application.
