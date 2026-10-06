# Requests from lane B to lane A

## 4. Add `slepian.v` and `gordon.v` to `_CoqProject`

Please add these files to `_CoqProject`, in this order, after
`library/comparison/gauss_concentration.v`:

```
library/comparison/slepian.v
library/comparison/gordon.v
```

Besides the lane B files already registered, they depend on
`gaussian/gauss_interpolation.v` and `matrix/euclidean.v`, and `gordon.v`
depends on `slepian.v`. Each compiles in the pinned image with
`rocq compile -Q library GaussianAnalysis` and the warning flags of
`_CoqProject`, and prints no warning. `slepian.v` proves the
Sudakov-Fernique inequality (`sudakov_fernique`) and Slepian's inequality for
expected maxima (`slepian`), and `gordon.v` Gordon's min-max inequality
(`gordon`, `gordon_cov`), all from Kahane's comparison inequality.
