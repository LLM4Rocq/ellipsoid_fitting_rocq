# GaussianApplications

Rocq formalizations of theorems of manuscripts of the OpenAI math
collection (`openai/math` at revision 1581d4cbd, under the Apache License
2.0) whose proofs reuse the library `GaussianAnalysis` of `library/`. The
logical root is `GaussianApplications`; phase 12 of `AGENTS.md` adds the
directory.

Each file is a Rocq formalization of a credited argument. Its header cites
the manuscript (its title and its family number in the collection), the
section or lemma it follows, the revision 1581d4cbd, and any Lean module of
the collection whose argument it follows. Nothing is copied from the Lean
code. The TeX of the collection is the mathematical source; where a frozen
statement, the TeX and a Lean statement differ, the header says so.

## Rules

- **Reals.** Every file is written over an arbitrary `R : realType`, as in
  `library/`. It requires only `library/` and MathComp: no module of
  Stdlib's real analysis (`Reals`, `Lra`, `Psatz` and the others), neither
  `Rstruct` nor `Rstruct_topology`, and nothing of `EllipsoidFitting`
  (`theories/`) or `EllipsoidUniversality` (`extension/`).
  `scripts/check_sources.py` rejects such a `Require`.
- **Direction.** Dependencies go from `applications/` to `library/` only:
  `scripts/check_sources.py` also rejects a module of `library/` that
  requires a module of `GaussianApplications`. General mathematics goes to
  `library/`, stated without the models of the manuscripts (the SK model,
  perceptrons, SAT, sign matrices); this directory holds the developments
  specific to a model.
- **Statements and theorems.** The statement files at the top of the
  directory (`XStatement.v`, with their definitions in `XDefinitions.v`
  where needed) fix what the user reviewed. Once the user accepts them they
  are frozen: `scripts/check_sources.py` compares their code with the
  acceptance commit, and only the master of the phase edits their comments.
  The theorem files (`XTheorem.v`) prove them; the proofs live in folders
  named after the targets.
- **Lean references.** `scripts/stale_citations.py` checks that every name
  cited in a comment exists, and the names of the Lean modules do not
  exist here. On a comment line, the text after the marker `Lean:` is not
  checked. Write each Lean reference on its own line, after its own
  marker, for example `Lean: goe_norm_tail (Matrices/GoeMatrixQuadCoeff.lean)`.
- **Axioms.** No `Admitted`, `Axiom`, `Parameter` or `Conjecture`.
  MathComp's classical axioms may be used.
- **Documentation.** Every file has a documentation header in MathComp's
  format, as in `library/`, and its rows in the table of main results
  below; its library files have their rows in `library/README.md`.

## Targets of phase 12

The plan is `/srv/ellipsoid-fitting/notes/phase12-plan.md` (section 3);
the sources are in `/srv/ellipsoid-fitting/papers/openai-math-1581d4c/`.

| Target | Manuscript (family) | Statement files | Library files | Proof folder |
|---|---|---|---|---|
| T1. Gaussian matrix series | Pointwise convergence of fourfold ergodic averages for mixing transformations (154), Lemma 4.2 | `MatrixSeriesStatement.v` | `random_matrix/matrix_series.v` | |
| T2. Tensor packing in finite dimensions | the same (154), Theorem 4.1 | `TensorPackingStatement.v` | `matrix/tensor_packing.v` | |
| T3. Sharp upper edge of the GOE | Cutoff throughout the high-temperature Sherrington-Kirkpatrick phase (227), appendix "Uniform spectral and entropy estimates" | `GoeEdgeStatement.v` | `matrix/lambda_max.v`, `random_matrix/goe_edge.v` | |
| T4. Spectral gap of the SK heat-bath dynamics for beta < 1/2 | the same (227) | `SKGapDefinitions.v`, `SKGapStatement.v` | | `SKGap/` |
| T5. Orthogonal splitting of positive semidefinite matrices | Exponential PSD rank of positively shifted matching matrices (126), lemma "Orthogonal splitting" | `PsdSplittingStatement.v` | `matrix/psd_splitting.v` | |
| T6. Sign/Gaussian comparison for the Ising perceptron pressure | The free energy of the Ising random perceptron (222), Theorem ext:sign | `PerceptronSignDefinitions.v`, `PerceptronSignStatement.v` | | `Perceptron/` |
| T7. Capped variance for random k-SAT | A limiting satisfiability threshold for every fixed clause size (235), Proposition "Polynomial concentration" | `SatVarianceDefinitions.v`, `SatVarianceStatement.v` | `probability/efron_stein_omission.v` | `RandomSAT/` |

The files of a target are added when its work starts; the statement files
are reviewed in two batches (T1, T3 and T5, then T2, T4, T6 and T7).

## Main results

The main results of each file, with an informal statement and its actual
hypotheses. The lanes add their rows.

| File | Result | Informal statement |
|---|---|---|
| `GoeEdgeTheorem.v` | `goe_edge_theorem` | Proves `goe_edge_statement` (T3): for every `R : realType`, `d >= 1`, `a` of law `gauss (d * d)` and `W = goe_mx a`, the map `a \|-> lambda_max W` is measurable and integrable, `E lambda_max W <= 2`, `P(lambda_max W >= 2 + t)` and `P(lambda_max (- W) >= 2 + t)` are at most `exp (- d t^2 / 4)`, and `P(opnorm W >= 2 + t) <= 2 exp (- d t^2 / 4)`, for every `t >= 0`. From `library/random_matrix/goe_edge.v`. |
