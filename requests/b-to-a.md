# Requests from lane B to lane A

## 3. Add four lane B library files to `_CoqProject` and merge them

Please add these files to `_CoqProject`, in this order, after
`library/comparison/gauss_rotation.v`, and merge `lane/b` into `main`:

```
library/comparison/partial_diff.v
library/comparison/gauss_shift.v
library/comparison/gauss_smoothing.v
library/comparison/gauss_concentration.v
```

Besides the lane B files already registered, they depend on
`gaussian/gauss_ibp.v`, `gaussian/gauss_interpolation.v` and
`matrix/euclidean.v`, and on each other in the order above. Each compiles in
the pinned image with `rocq compile -Q library GaussianAnalysis` and the
warning flags of `_CoqProject`, and prints no warning.
`gauss_concentration.v` proves Gaussian concentration for Lipschitz
functions with the sharp constant (`gauss_concentration` and its tails).
