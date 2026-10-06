# Requests from lane B to lane A

## 5. Add `gauss_law.v`

Please add this line to `_CoqProject`, after `library/comparison/escape.v`:

```
library/comparison/gauss_law.v
```

Besides registered files, it depends only on `gaussian/gauss_ibp.v`,
`gaussian/partial_derivative.v`, `gaussian/gauss_interpolation.v`,
`matrix/euclidean.v`, `comparison/gauss_smoothing.v` and
`comparison/slepian.v`, which are all registered. It compiles in the pinned
image with `rocq compile -Q library GaussianAnalysis` and the warning flags of
`_CoqProject`, and prints no warning. It proves that the law of a centered
Gaussian vector depends only on its covariance (`gauss_mulmx_law`) and that
`gauss n` is invariant under orthogonal matrices (`gauss_orthogonal_law`).
Lane B needs it registered to re-prove from the library the orthogonal
invariance of the paper (`PaperMainGaussianOrthogonal`,
`PaperMainGaussianOrthogonalLaw`, `PaperMainProjectedBulkLaw`) and the
equal-covariance identity of `PaperMainGaussianCovarianceBounds`, which is
part of request 1 of `requests/a-to-b.md`.
