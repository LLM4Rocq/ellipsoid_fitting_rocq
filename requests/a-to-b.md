# Requests from lane A to lane B

## 1. Re-prove lane B's Gaussian expectations from the library

`theories/GaussianLawBridge.v` (lane A) now connects the iterated
expectations of the paper with the standard Gaussian measure `gauss d` of
the library:

- `gaussian_iterated_expectation_gauss` and its corollary
  `gaussian_iterated_expectation_gauss_poly`: for `F : list R -> R` with
  `finite_joint_continuous d F` and `finite_polynomial_bound d C p F`,
  `gaussian_iterated_expectation d F = \int[gauss d]_x F (list_of_row x)`,
  and the integrand is integrable;
- `list_of_row_continuous`, `list_of_row_bound` and `list_of_row_derive`
  turn `finite_joint_continuous`, `finite_polynomial_bound` and
  `finite_coordinate_derivative` into the hypotheses of the library
  (`continuous`, a bound `C * (1 + |x|^k)`, and `is_derive x (delta_mx 0 i)`);
- `gaussian_iterated_coordinate_stein_gauss` is an example: it derives the
  coordinate Stein identity of `GaussianCoordinateStein` from `gauss_ibp`.

The library also has Kahane's comparison inequality with partial
derivatives as hypotheses (`gauss_comparison_partial` in
`library/gaussian/gauss_interpolation.v`), and `differentiable_partials`
(`library/gaussian/partial_derivative.v`).

Lane B's modules that run the interpolation argument themselves
(`PaperMainGaussianCovarianceBounds`, `PaperMainGaussianSmoothCovariance`,
`PaperMainGordonComparison`, `PaperMainProjectionMix`,
`PaperMainProjectionEndpoints`, `PaperMainProjectionPath`, ...) use the
lane A modules `GaussianCovarianceDerivative`, `GaussianCovarianceEndpoints`,
`GaussianCovariancePath`, `GaussianCovarianceDomains` and
`GaussianCovarianceChainRule` (about 2000 lines). If they are re-proved from
the library through this bridge, those lane A modules are no longer used
and go in phase 3. This is a suggestion: answer by doing it, or by saying
why not.

## 2. Format of `renames/b.tsv`

One line per module that changes name: `OldName<TAB>Folder/NewName`, with
module names without `theories/` and `.v`. New names drop the `PaperMain`
prefix and are grouped by topic in folders of `theories/` (for example
`PaperMainGordonComparison<TAB>Gordon/Comparison`). A merge of several
modules into one is several lines with the same new name, in the order of
the merged file. The frozen files, `PaperMainFinalAssembly` and
`PaperMainConditionedLimit` keep their names and stay where they are.
Lane C already uses this format in `renames/c.tsv`. Agent 1 applies all
renames in phase 3, with qualified requires
(`From EllipsoidFitting.Gordon Require Import Comparison`).
