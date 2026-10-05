# GaussianAnalysis

A Rocq library on Gaussian measures, Gaussian comparison and concentration
inequalities, and the linear algebra and probability tools they need. It is
written over an arbitrary `R : realType`, in the style of MathComp-Analysis,
so that parts of it can later be proposed to MathComp-Analysis. It does not
depend on the ellipsoid fitting paper. The proof of the paper in
`theories/` is being changed to use it, at Stdlib's `R`.

The library is being written. No human has reviewed its statements yet.

## Conventions

- **Reals.** Every result is stated for an arbitrary `R : realType`, or a
  weaker structure such as `realFieldType` when that is enough. No file
  requires Stdlib's `Reals`, `Lra`, `Psatz` or MathComp's `Rstruct`:
  `make check` rejects them in `library/`.
- **Vocabulary.** MathComp's: row and column vectors `'rV[R]_n` and
  `'cV[R]_n`, matrices `'M[R]_(m, n)`, `` `|x| ``, `Num.sqrt`, `expR`, `ln`,
  `n%:R`, `\sum`, and the measures, integrals and probability of
  MathComp-Analysis (`measure`, `lebesgue_integral`, `probability`,
  `normal_distribution`). No lists of coordinates.
- **Tactics.** `From mathcomp Require Import arithmetic_tactic` provides
  `lra`, `nra` and `psatz` on any real field; `ring_tactic` and
  `field_tactic` provide `ring` and `field`.
- **Names and style.** MathComp's naming conventions for lemmas, ssreflect
  proof style, lowercase file names, and a documentation header at the top
  of each file in MathComp's format: each definition and notation with a
  one-line reading.
- **Axioms.** No `Admitted`, `Axiom` or `Parameter`. MathComp's classical
  axioms (`boolp`) may be used.

## Layout

| Directory | Lane | Topic |
|---|---|---|
| `gaussian/` | A | the standard Gaussian measure on `'rV[R]_n`, marginals and Fubini, moments, Gaussian integration by parts (Stein's identity) in one and several dimensions, Gaussian interpolation between two covariances |
| `comparison/` | B | linear images and rotation invariance, tails, moment generating functions and chi-square laws, concentration of Lipschitz functions, Slepian, Sudakov-Fernique and Gordon comparison inequalities, escape through a mesh, norms of Gaussian matrices |
| `matrix/` | C | the spectral theorem for real symmetric matrices, operator and Frobenius norms, nets on spheres |
| `probability/` | C | Paley-Zygmund and other moment inequalities, the Lindeberg replacement method |

## Main results

Each lane lists here the main results of its files, with an informal
statement and the paper modules that use them. This table is what the user
will review.

| File | Result | Informal statement | Used in `theories/` by |
|---|---|---|---|
| `matrix/euclidean.v` | `mxdot_cauchy_schwarz`, `frobeniusD`, `frobenius_mulmx` | The Frobenius inner product of real matrices satisfies Cauchy-Schwarz; the Frobenius norm satisfies the triangle inequality and is submultiplicative. On row and column vectors they are the Euclidean inner product and norm. |  |
| `matrix/euclidean.v` | `mxdot_orthogonalmxl`, `frobenius_orthogonalmxr` | Multiplying by an orthogonal matrix, on either side, preserves the Frobenius inner product and norm. |  |
| `matrix/real_spectral.v` | `symmetric_spectral` | Spectral theorem: every real symmetric matrix is `P^T diag(d) P` with `P` orthogonal, over any `realType`. Proved by maximizing the quadratic form on the unit sphere and splitting off a dimension with a Householder reflection. |  |
| `matrix/real_spectral.v` | `rayleigh_max`, `symmetric_eigenvector` | The quadratic form attains its maximum on the unit sphere; for a symmetric matrix a maximizer is an eigenvector. |  |
| `matrix/real_spectral.v` | `spectral_trace`, `spectral_mxdot`, `spectral_form`, `spectral_form_le`, `spectral_psd`, `spectral_form_abs` | If `A = P^T diag(d) P` with `P` orthogonal: the trace is the sum of the `d_i`, the squared Frobenius norm is the sum of the `d_i^2`, `x^T A x = sum_i d_i (P x)_i^2`, and `x^T A x <= b x^T x` for all `x` if and only if every `d_i <= b` (likewise for lower bounds, positive semidefiniteness and absolute values). |  |
| `matrix/opnorm.v` | `opnorm_leP`, `opnorm_bilinearP`, `opnorm_trmx` | The operator norm `sup_{\|x\| <= 1} \|A x\|` is the least `b` with `\|A x\| <= b \|x\|`, and the least `b` with `\|y^T A x\| <= b \|y\| \|x\|`; it is invariant under transposition and orthogonal multiplication, and bounded by the Frobenius norm. |  |
| `matrix/opnorm.v` | `opnorm_symP`, `opnorm_spectral` | For a symmetric matrix, `opnorm A <= b` if and only if `\|x^T A x\| <= b x^T x` for all `x`, and the operator norm is the largest absolute value of an eigenvalue. |  |
| `matrix/nets.v` | `opnorm_net`, `opnorm_net_bilinear`, `opnorm_net_sym` | If `N` is an `eps`-net of the unit ball, then `opnorm A <= max_{y in N} \|A y\| / (1 - eps)`, `opnorm A <= max_{u, v in N} \|u^T A v\| / (1 - 2 eps)`, and for symmetric `A`, `opnorm A <= max_{v in N} \|v^T A v\| / (1 - 2 eps)`. |  |
| `probability/moments.v` | `paley_zygmund` | Paley-Zygmund: if `X` is square integrable and `0 <= theta < E X`, then `P(theta <= X) >= (E X - theta)^2 / E X^2`. No sign condition on `X`. |  |
| `matrix/real_spectral.v` | `spectral_exp`, `mxtrace_ABAB_le` | If `A = P^T diag(d) P` with `P` orthogonal, then `A^k = P^T diag(d^k) P`. For symmetric `A`, `B`: `tr(ABAB) <= tr(A^2 B^2)`. |  |
| `matrix/opnorm.v` | `opnorm_exp_le_trace_even`, `opnorm_le_trace_exp` | For a symmetric matrix and an even exponent `p > 0`, `opnorm A ^ p <= tr(A^p)`; so `tr(A^p) <= t^p` with `t >= 0` gives `opnorm A <= t`. |  |
| `probability/lindeberg.v` | `tuple_prod`, `Rintegral_tuple_prodS` | `tuple_prod mu n` is the law of `n` independent random elements with laws `mu 0, ..., mu (n-1)`, on `n.-tuple T`; integrals against it are iterated integrals (Fubini). |  |
| `probability/lindeberg.v` | `lindeberg_replacement` | Lindeberg's replacement principle: for `F` bounded and measurable on `n.-tuple T`, if replacing the law `mu i` of coordinate `i` by `nu i` changes the expectation of `F` by at most `B i`, uniformly in the other coordinates, then replacing all of them changes it by at most `B 0 + ... + B (n-1)`. |  |
