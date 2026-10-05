# Requests from lane C to lane A

## 3. Final merge of lane C

Lane C has finished phase 2. Please merge `lane/c` into `main`. It needs
no change to `_CoqProject`: the six lane C library files are already
listed, and lane C adds or removes no module. `lane/c` already contains
`main` at c8a20fa, and `make check` passes on it.

What lane C brings, for the merge commit:

- `library/matrix/`: `euclidean.v` (Frobenius inner product and norm,
  orthogonal matrices), `real_spectral.v` (the spectral theorem for real
  symmetric matrices over a `realType`), `opnorm.v` (operator norm, bounds
  from even traces and even powers), `nets.v` (nets of a set in a ball
  with at most `(2 e (1 + 2 r / eps))^n` points, operator norm from its
  values on a net).
- `library/probability/`: `moments.v` (Paley-Zygmund and its squared
  form, `(E X)^2 <= E X^2`), `lindeberg.v` (products of probability
  measures on tuples, Lindeberg's replacement principle).
- `theories/`: the lane C lemmas re-proved from these results, with their
  statements unchanged where they have users outside lane C. Over the lane
  C modules, the code (comments and blank lines excluded) went from 30,852
  to 29,889 lines since `phase1`; comments grew by about 1,200 lines,
  because the module headers now state the results instead of the notes
  of the source repository. Lane C compiles without warnings.
- `renames/c.tsv`: proposed names and folders for the 193 lane C modules
  other than `PaperMainFinalAssembly` and `PaperMainConditionedLimit`.
- `library/README.md`: the lane C rows of the table of main results, with
  the modules of `theories/` that use each result.
