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
  perceptrons, SAT and its clauses, sign matrices, matching matrices and
  their cells, odd cuts, the parity system); this directory holds the
  developments specific to a model.
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
| T4. Spectral gap of the SK heat-bath dynamics for beta < 1/2 | the same (227) | `SKGapDefinitions.v`, `SKGapStatement.v` | `matrix/spectral_gap.v`, `probability/finite_gap.v`, `random_matrix/goe_entries.v` | `SKGap/` |
| T5. Orthogonal splitting of positive semidefinite matrices | Exponential PSD rank of positively shifted matching matrices (126), lemma "Orthogonal splitting" | `PsdSplittingStatement.v` | `matrix/psd_splitting.v` | |
| T6. Sign/Gaussian comparison for the Ising perceptron pressure | The free energy of the Ising random perceptron (222), Theorem ext:sign | `PerceptronSignDefinitions.v`, `PerceptronSignStatement.v` | `probability/rademacher_lindeberg.v`, `probability/log_partition.v` | `Perceptron/` |
| T7. Capped variance for random k-SAT | A limiting satisfiability threshold for every fixed clause size (235), Proposition "Polynomial concentration" | `SatVarianceDefinitions.v`, `SatVarianceStatement.v` | `probability/finite_mean.v`; `probability/efron_stein_omission.v`, the general form of the manuscript's lemma 'Deletion variance bound', is not used by the proof | `RandomSAT/` |

The files of a target are added when its work starts. The statement files
were reviewed in two batches and are frozen: T1, T3 and T5 with
`library/matrix/lambda_max.v`, accepted at `fc76edf`, then T2, T4, T6 and
T7, accepted at `0d5afba`.

## Targets of phase 13

The plan is `/srv/ellipsoid-fitting/notes/phase13-plan.md` (sections 2
and 3); the sources are in `/srv/ellipsoid-fitting/papers/openai-math-1581d4c/`.

| Target | Manuscript (family) | Statement files | Library files | Proof folder |
|---|---|---|---|---|
| T9. The satisfiability threshold of random k-SAT, for every k >= 3 | A Limiting Satisfiability Threshold for Every Fixed Clause Size (235), Theorem thm:main | `SatThresholdDefinitions.v`, `SatThresholdStatement.v` | `probability/commuting_operators.v`, `probability/binomial_mean.v`, `probability/finite_mean.v`, `analysis/min_superadditive.v` | `RandomSAT/` |
| T10. Exact normalization of PSD factors | Exponential PSD rank of positively shifted matching matrices (126), lemma "Normalization of PSD factors" | `PsdNormalizationStatement.v` | `matrix/psd_factorization.v` | |
| T11. Product smoothing of matrix squares | the same (126), theorem "Fourier smoothing of matrix squares" | `ProductSmoothingStatement.v` | `fourier/boolean_fourier.v`, `fourier/product_smoothing.v`, `matrix/psd_splitting.v` | |
| T12. Convergence from approximate minimum inequalities | A Limiting Satisfiability Threshold for Every Fixed Clause Size (235), lemma "Balanced comparisons" | `MinSuperadditiveStatement.v` | `analysis/min_superadditive.v` | |

The files of a target are added when its work starts. The statement files
are reviewed in batches: T9 and T12 with the general statements of the SAT
side (batch 1), then T10 and T11 with those of the PSD side (batch 2). The
general statements of the library files are reviewed with their batch as
compiled `Prop` definitions; they are accepted, not frozen. The main
statement of the PSD rank theorem of family 126 (`PsdRankDefinitions.v`,
`PsdRankStatement.v`) is written and reviewed in phase 13 (batch 3) and
proved in phase 14; its folder `PsdRank/` holds sanity lemmas for its
definitions (`Model.v`) and the skeleton of the final step of its proof
(`Main.v`).

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
| `SKGap/Spectral.v` | `ising_gap_from_square`, `ising_gen_form`, `ising_gen_sym`, `ising_gen_ker` | The spectral step of T4 (item T4a). For any matrix `A`, field `theta` and real `k`: if `k E(g) <= nu[(L g)^2]` for every `g`, where `nu` is the Ising law, `E = ising_dirichlet A theta` and `L = ising_gen A theta = sum_i D_i`, then `k Var_nu(f) <= E(f)` for every `f`. In `L^2(nu)`, `L` is linear and self-adjoint, `<f, L f>_nu = E(f)`, and the kernel of `L` is the constants, so `wpoincare_from_square` of `probability/finite_gap.v` applies. `R`, `n`, `A`, `theta` and `k` are implicit. |
| `SKGap/TwoSpin.v` | `pair_two_spin`, `ising_two_spin` | The uniform two-spin inequality. For the pair law proportional to `(1 + a x)(1 + b y)(1 + t x y)` with `\|a\|, \|b\| <= 1` and `\|t\| <= 1/1000`: the mixed energy plus the correction term `(t + 2 t^2 m_i m_j) v_i v_j d_i f d_j f` is at least `- 70000 \|t\|^3` times the sum of the two energies (`pair_two_spin`; the remainder in `t` by a real polynomial certificate, `ts_coef_bound`). For the Ising law of a symmetric `A` with zero diagonal and `i != j` with `\|tanh A_ij\| <= 1/1000`: `nu[D_i f D_j f] >= - nu[(t + 2 t^2 m_i m_j) v_i v_j d_i f d_j f] - 70000 \|t\|^3 (nu[v_i (d_i f)^2] + nu[v_j (d_j f)^2])` with `t = tanh A_ij` (`ising_two_spin`). |
| `SKGap/Poincare.v` | `ising_gen_sq_ge`, `ising_cov_from_gap`, `sk_gap_deterministic` | For `A` symmetric with zero diagonal, `\|tanh A_ij\| <= 1/1000`, `opnorm (tanh A_ij) <= M`, `2 opnorm (tanh^2 A_ij) <= M` and `sum_j \|tanh A_ij\|^3 <= rho` for every row: `nu[(sum_i D_i f)^2] >= (1 - M - 140000 rho) E(f)`. For `k > 0`, from `k Var_nu(f) <= E(f)` for all `f`: `opnorm Cov_nu(x) <= 1 / k`. The deterministic gap: for `0 <= beta < 1/2`, `0 < delta <= sk_gap_tol beta = min (1/2000) ((1 - 2 beta)/400000)`, `J` symmetric with zero diagonal, `opnorm J <= 2 beta + delta`, `sum_j J_ij^2 <= beta^2 + delta` and `\|J_ij\| <= delta`, and `0 <= s <= 1`: `kappa Var_nu(f) <= E(f)` for every `f` and `opnorm Cov_nu(x) <= 1 / kappa`, `kappa = (1 - 2 beta)/2`, for the Ising law of `s J` and any field. |
| `RandomSAT/Model.v` | `sat_prefix_lenE`, `card_clause`, `unif_mean_clause_split` | For a tuple `t` of `M` clauses, the largest satisfiable prefix length `sat_prefix_len t`, the cap `M` included, is the lifetime `life [set: _] t`: the number of nonempty solution sets among those of the nonempty prefixes of `t`. `#\|clause n k\| = 'C(n, k) 2^k`. For `k <= n`, the uniform mean over `clause n.+1 k.+1` is the mixture, with weights `1 - k.+1/n.+1` and `k.+1/n.+1`, of the clauses without the first variable (a uniform clause of size `k.+1` on the other `n` variables) and of the clauses with it (a uniform sign and a uniform clause of size `k` on the others). |
| `RandomSAT/Pivotal.v` | `life_var_le_occ` | For `k <= n`, a set `S` of assignments on `n` variables and `m <= M`, the variance of the lifetime `life S t` of `m` independent uniform clauses `t` of size `k` is at most `2 m` times the sum over `j < m` of the mean of `min(M q_j, 1)`, where `q_j` is the probability that one more clause empties the solution set of the first `j` clauses. |
| `RandomSAT/Replacement.v` | `killE_forced`, `kill_replacement` | For a nonempty set `S` of assignments on `n` variables with `b` forced variables (on which all its elements agree), the probability that a uniform clause of size `k` empties `S` is `'C(b, k) / ('C(n, k) 2^k)`. For `1 <= r < v`, `a > 0` with `1 / (v + 1) <= a^-r` and an integer `g >= 2 (r + 1) a`, a block of `g` independent uniform clauses of size `r + 1` empties a set `S` of assignments on `v` variables with probability at least `kill r S - a^-r`, for every `S`. |
| `RandomSAT/Forcing.v` | `integrated_head_forcing`, `forced_frac_head` | For `1 <= k < n`, `a > 0` with `1 / (n + 1) <= a^-k`, an integer `g >= 2 (k + 1) a` and `p = (k + 1) / (n + 1)`, the probabilities `h_j` that the first variable is forced by `j` independent uniform clauses of size `k + 1` on `n + 1` variables satisfy `sum_(j <= M) h_j <= g M p + (M + 1) M p a^-k` for every `M`. The mean fraction of forced variables after `j` clauses is `h_j`. |
| `RandomSAT/Variance.v` | `sat_capped_varE`, `trunc_le_forced`, `sat_variance_bound_explicit`, `sat_variance_bound` | `sat_capped_var R n k` is the variance of the lifetime of the set of all assignments over `sat_cap k n` clauses. For `0 < k <= n`, `c >= 0` and `M <= c^k`, `min(M q, 1) <= c b / n`, where `q` is the probability that a uniform clause of size `k` empties a set of assignments with `b` forced variables. `sat_variance_bound_explicit`: for `K >= 3` and `N >= K + 1`, `sat_capped_var R N K <= 8 4^(K+1) K (3 K + 2^(K+2)) N^(1 + 2/K)`; `sat_variance_bound` is its existential form, the form of the statement. |
| `SatVarianceTheorem.v` | `sat_variance_theorem` | Proves `sat_variance_statement` (T7), with the constant `C = 8 4^(k+1) k (3 k + 2^(k+2))` of `sat_variance_bound_explicit`: for every `R : realType`, `k >= 3` and `n >= k + 1`, the variance `sat_capped_var R n k` of the largest satisfiable prefix length, capped at `2^(k+1) n`, of `2^(k+1) n` independent uniform proper signed `k`-clauses on `n` variables is at most `C n^(1 + 2/k)` (`powR`). From `sat_variance_bound` of `RandomSAT/Variance.v`. Axioms: three of `boolp`. |
| `SKGapTheorem.v` | `sk_gap_theorem` | Proves `sk_gap_statement` (T4) with the events `E_n = sk_good_disorder n beta (sk_gap_tol beta)` of `SKGap/Disorder.v`: measurable, of probability tending to one under `gauss (n * n)`, and on them, for every `n`, `s` in `[0, 1]` and field `theta`, `(1 - 2 beta)/2 Var_nu(f) <= E(f)` for every `f` and `opnorm Cov_nu(x) <= 2 / (1 - 2 beta)`. Axioms: three of `boolp`. |
| `MinSuperadditiveTheorem.v` | `min_superadditive_theorem` | Proves `min_superadditive_statement` (T12): for every `R : realType`, `u : nat -> R`, `A >= 0`, `beta > 0` and `N`, if `u (r + s) >= min (u r, u s) - A min (r, s)^(-beta)` for all comparable `r, s >= N` (`r <= 3 s`, `s <= 3 r`) and `u (s + 1) >= u s - A s^(-beta)` for all `s >= N`, then `u n >= u s - A (1 + E) s^(-beta)` for `s >= max (N, 2)` and `n >= s^2`, with `E = 3^beta / ((3/2)^beta - 1)`; and if `\|u n\| <= M` for all `n`, then `u` converges and its limit satisfies the same bound. From `min_superadditive_tail`, `min_superadditive_cvgn` and `min_superadditive_lim_ge` of `library/analysis/min_superadditive.v`. Axioms: three of `boolp`. |
| `PsdNormalizationTheorem.v` | `psd_normalization_theorem` | Proves `psd_normalization_statement` (T10): for every `R : realType`, finite types `I`, `J` with `J` nonempty, positive semidefinite `F i`, `G j` in `'M[R]_r` and `m` with `\tr (F i *m G j) <= m` for all `i`, `j`, there are positive semidefinite `F' i`, `G' j` of the same size with the same pairings, `\tr (F' i) <= m` and `\tr (G' j) <= r`. From `psd_normalization` of `library/matrix/psd_factorization.v`. The size is kept by a compression to the range of the column factors, where the manuscript restricts to their span. Axioms: three of `boolp`. |
| `PsdRank/Model.v` | `crossing_odd`, `shifted_matching_mx_ge`, `card_kn_edges`, `shifted_matching_one_factorization`, `psd_rank_statementE` | Sanity lemmas for the definitions of the PSD main statement (`PsdRankDefinitions.v`), not frozen. For every `n`, every odd set `U` and every perfect matching `M` of `K_n`, `\|M cap delta(U)\|` is odd (`\|U\| = sum_(e in M) \|e cap U\|`), so every entry of `A_n(rho)` is at least `rho`. `K_n` has `'C(n, 2)` edges, and `A_n(1)` has a PSD factorization of size `'C(n, 2)`, by the diagonal matrices indexed by the edges with entries `1_(e in delta(U))` for a row and `1_(e in M)` for a column: the exclusion of `rho = 1` in `psd_rank_statement` is necessary. `psd_rank_statementE`: `psd_rank_statement` is equivalent to its form with the factors written out. |
