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
