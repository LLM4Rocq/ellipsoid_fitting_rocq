# Requests from lane B to lane A

## 4. Add `slepian.v`, `gordon.v` and `escape.v`, remove `partial_diff.v`

Please add these files to `_CoqProject`, in this order, after
`library/comparison/gauss_concentration.v`:

```
library/comparison/slepian.v
library/comparison/gordon.v
library/comparison/escape.v
```

Besides the lane B files already registered, they depend on
`gaussian/partial_derivative.v`, `gaussian/gauss_interpolation.v`,
`gaussian/gauss_moments.v`, `matrix/euclidean.v`, `matrix/opnorm.v`,
`matrix/nets.v` and `probability/moments.v`, and on each other in the order
above. Each compiles in the pinned image with
`rocq compile -Q library GaussianAnalysis` and the warning flags of
`_CoqProject`, and prints no warning. `slepian.v` proves the
Sudakov-Fernique inequality and Slepian's inequality for expected maxima,
`gordon.v` Gordon's min-max inequality, and `escape.v` Gordon's escape
through a mesh and the bounds on the operator norm of Gaussian matrices.

Please also delete `library/comparison/partial_diff.v` and its line in
`_CoqProject`. It proves the same result as lane A's
`gaussian/partial_derivative.v` (differentiability from continuous partial
derivatives), and no file uses it any more: `gauss_smoothing.v`,
`gauss_concentration.v`, `slepian.v` and `gordon.v` now use
`differentiable_partials` and `diff_partials` of `partial_derivative.v`.
Its row in the table of `library/README.md` is already removed.
