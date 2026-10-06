# Requests from lane B to lane A

## 7. One lemma from `finite_sum` to `\sum`

Five modules prove the same lemma, under five names:
`finite_sum f (List.seq 0 n) = \sum_(i < n) f i`
(`paper_main_finite_sum_public` in `PaperMainMatrixDuality`,
`paper_main_gaussian_finite_sum_seq` in
`PaperMainGaussianLipschitzConcentration`, `paper_main_data_finite_sum` in
`PaperMainGaussianDataRadius`, `paper_main_gordon_finite_sum_seq` in
`PaperMainGordonProcesses`, `paper_main_gordon_escape_finite_sum_seq` in
`PaperMainGordonEscapeExpectation`; `paper_main_covariance_finite_sum` in
`PaperMainGaussianCovarianceBounds` is a sixth). Could lane A state it
once, in `GaussianLawBridge` or `RealsBridge`, so that the lanes can use it
and phase 3 can delete the copies?

## 8. Final merge of lane B

The work of lane B for phase 2 is done and pushed: please merge `lane/b`
(23ad3d9 and this entry) into `main`.

- `library/comparison/` covers every topic of its row of the layout table;
  its main results are in lane B's rows of `library/README.md`, with the
  modules of `theories/` that use them.
- The paper's lane B modules now take from the library Gordon's comparison
  and escape through a mesh, Gaussian concentration and the Poincare
  inequality, the law of linear images and orthogonal invariance, the sign
  symmetry, and the tails of linear forms and of weighted squares, with
  unchanged statements.
- Request 1 of `requests/a-to-b.md`: lane B no longer uses lane A's
  `GaussianCovarianceComparison`. The `PaperMainProjection*` modules still
  use `GaussianCovarianceDerivative`, `GaussianCovarianceEndpoints`,
  `GaussianCovariancePath` and `GaussianCovarianceChainRule`: they
  interpolate between quadratic Gaussian features and their Gaussian
  replacement, a comparison the library does not cover. Request 2 is
  answered by `renames/b.tsv`, which lists the 186 modules of lane B.
- The comments of lane B are cleaned and lane B has no warnings.
- Request 7 is a suggestion; lane B needs nothing else from lane A.
