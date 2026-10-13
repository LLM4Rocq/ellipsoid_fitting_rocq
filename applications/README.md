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

The files of a target are added when its work starts. The statement files
were reviewed in two batches and are frozen: T1, T3 and T5 with
`library/matrix/lambda_max.v`, accepted at `fc76edf`, then T2, T4, T6 and
T7, accepted at `0d5afba`.

## Main results

The main results of each file, with an informal statement and its actual
hypotheses. The lanes add their rows.

| File | Result | Informal statement |
|---|---|---|
| `MatrixSeriesTheorem.v` | `matrix_series_theorem` | Proves `matrix_series_statement` (T1). (a) For symmetric `H_1, ..., H_r` in `'M[R]_n`, `S = \sum_j H_j H_j` and `g` of law `gauss r`, `E tr (\sum_j g_j H_j)^(2q) <= (2q - 1)!! opnorm S^(q-1) tr S` for every `q >= 1` (`gauss_mx_series_moment`). (b) For `B_1, ..., B_r` in `'M[R]_(m, p)` and every `q >= 1`, `E opnorm (\sum_j g_j B_j) <= ((2q - 1)!! sigma^(2(q-1)) tau)^(1/(2q))`, with `sigma^2 = max (opnorm (\sum_j B_j B_j^T), opnorm (\sum_j B_j^T B_j))` and `tau = 2 tr (\sum_j B_j B_j^T)` (`gauss_mx_series_opnorm`). (c) With `C = 5`: if `sigma^2 <= sqrt d` and `tau <= 2 d` for a real `d >= 1`, then `E opnorm (\sum_j g_j B_j) <= 5 sqrt (sqrt d) sqrt (ln (2 + d))` (`gauss_mx_series_opnorm_log`). The expectations are integrals in the extended reals. Axioms: three of `boolp`. |
| `TensorPackingTheorem.v` | `tensor_packing_theorem` | Proves `tensor_packing_statement` (T2) with `C = 30000`: for every `R : realType`, rows `x_1, ..., x_m` and `y_1, ..., y_m` in the unit balls of `'rV[R]_n1` and `'rV[R]_n2`, relations `Gx` and `Gy` on `'I_m` with at most `L` successors at every vertex that contain every pair `a != b` with `\|<x_a, x_b>\| > eta` (respectively `\|<y_a, y_b>\| > eta`), Frobenius-orthonormal `A_1, ..., A_r` in `'M[R]_(n1, n2)` with `r <= d`, `0 < eps <= 1`, `d >= 1` and `0 <= eta <= eps^2 / 10^4`, the number of indices `a` with `sum_k (x_a A_k y_a^T)^2 >= eps^2` is at most `30000 (1 + L) / eps^2 exp (30000 eps^(-2) sqrt d ln (2 + d))`, from `tensor_packing` of `library/matrix/tensor_packing.v`. Axioms: three of `boolp`. |
| `GoeEdgeTheorem.v` | `goe_edge_theorem` | Proves `goe_edge_statement` (T3): for every `R : realType`, `d >= 1`, `a` of law `gauss (d * d)` and `W = goe_mx a`, the map `a \|-> lambda_max W` is measurable and integrable, `E lambda_max W <= 2`, `P(lambda_max W >= 2 + t)` and `P(lambda_max (- W) >= 2 + t)` are at most `exp (- d t^2 / 4)`, and `P(opnorm W >= 2 + t) <= 2 exp (- d t^2 / 4)`, for every `t >= 0`. From `library/random_matrix/goe_edge.v`. |
| `PsdSplittingTheorem.v` | `psd_splitting_theorem` | Proves `psd_splitting_statement` (T5): for every `R : realType`, `L >= 1` and positive semidefinite `A_1, ..., A_L` of `'M[R]_n`, there are orthogonal projections `P_1, ..., P_L`, possibly zero, with `P_s P_t = 0` for `s != t` and `sum_s P_s = 1`, and `sum_z sum_(s != z) \|P_s A_z P_s\|_F^2 <= 2^(L-1) sum_z sum_(z' != z) tr (A_z A_z')`, from `psd_splitting` of `library/matrix/psd_splitting.v`. |
| `Perceptron/Pressure.v` | `perceptron_pressure_le`, `measurable_perceptron_pressure`, `perceptron_pressure_derive3`, `sign_pressureE`, `perceptron_sign_compare` | For `N >= 1` and `f` with three derivatives such that `\|f\| <= B0`, `\|f'\| <= B1`, `\|f''\| <= B2` and `\|f'''\| <= B3`: the pressure `p_N(G, f)` is at most `M B0` in absolute value and measurable in the entries of `G`; along each entry of `G` it has three derivatives, the third at most `(B3 + 6 B1 B2 + 6 B1^3) / (N^2 sqrt N)` in absolute value (from `log_partition_derive3`); and `g \|-> p_N(vec_mx g, f)` is integrable against `gauss (M * N)` with `\|E_sign p_N - E_Gauss p_N\| <= (B3 + 6 B1 B2 + 6 B1^3) / 2 M N^(-3/2)` (from `rademacher_gauss_lindeberg` over the `M N` entries). |
| `PerceptronSignTheorem.v` | `perceptron_sign_theorem` | Proves `perceptron_sign_statement` (T6) with `C = 1 + (\|B3\| + 6 \|B1\| \|B2\| + 6 \|B1\|^3) / 2`, from `perceptron_sign_compare` of `Perceptron/Pressure.v`. The continuity of `f'''` required by `bounded_C3` is not used. Axioms: three of `boolp`. |
| `SKGap/Ising.v` | `ising_dproj_eq`, `ising_energy`, `ising_dproj_adj`, `ising_dirichlet_eq0`, `ising_weight_block`, `sk_tanh_sub_le` | For the Ising law `nu` of a matrix `A` and a field `theta` on `{-1, 1}^n` (the definitions of T4), the conditional expectation `E_i` given the spins outside `i` and `D_i = I - E_i` satisfy `D_i f = (x_i - m_i) d_i f`, `nu[(D_i f)^2] = nu[v_i (d_i f)^2]` and `nu[g D_i f] = nu[D_i g D_i f]`; the Dirichlet form vanishes only on the constants; `ising_gen f = sum_i D_i f`. For `A` symmetric with zero diagonal and `i != j`, the weights of the four configurations of the spins `i` and `j`, the other spins fixed, are `K (1 + a x)(1 + b y)(1 + t x y)` with `K > 0`, `\|a\|, \|b\| < 1` and `t = tanh A_ij`. `\|tanh u\| <= \|u\|` and `\|tanh u - u\| <= \|u\|^3`. |
| `SKGap/Disorder.v` | `sk_good_disorder`, `sk_good_disorder_measurable`, `sk_good_disorder_prob` | The good-disorder event of T4 (item T4b), for `beta >= 0` and a fixed `delta > 0`: `sk_good_disorder n beta delta` is the set of the `a` of `'rV[R]_(n * n)` whose coupling `J = sk_coupling beta a` satisfies `opnorm J <= 2 beta + delta`, `sum_j J_ij^2 <= beta^2 + delta` for every `i` and `\|J_ij\| <= delta` for every `i` and `j`. It is measurable, and for every `eps > 0` there is `N` such that its probability under `gauss (n * n)` is at least `1 - eps` for every `n >= N`. The proposition 'Good disorder' of the manuscript, with `delta` fixed instead of `n^(-1/4)`, from `goe_opnorm_edge_tail` and the tails of `random_matrix/goe_entries.v`. `R` is implicit; the other arguments are explicit. |
