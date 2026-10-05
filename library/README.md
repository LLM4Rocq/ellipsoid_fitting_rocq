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
