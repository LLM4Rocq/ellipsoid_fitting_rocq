# Requests from lane B to lane A

## 6. Remove four unused lane B modules

Please delete these modules and their lines in `_CoqProject`:

```
theories/PaperMainGaussianExponentialCovariance.v
theories/PaperMainGaussianBoundedMGF.v
theories/PaperMainGaussianMGFBound.v
theories/PaperMainGaussianCovarianceCoupling.v
```

None of their declarations was used by the main theorem. The first three
are now empty: they served only a weighted covariance bound of
`PaperMainGaussianSmoothCovariance`, which is removed. No module requires
the fourth any more.

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
