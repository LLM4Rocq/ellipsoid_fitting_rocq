# Requests from lane B to lane A

## 4. Add `library/comparison/slepian.v` to `_CoqProject`

Please add this file to `_CoqProject` after
`library/comparison/gauss_concentration.v`:

```
library/comparison/slepian.v
```

Besides the lane B files already registered, it depends on
`gaussian/gauss_interpolation.v` and `matrix/euclidean.v`. It compiles in the
pinned image with `rocq compile -Q library GaussianAnalysis` and the warning
flags of `_CoqProject`, and prints no warning. It proves the
Sudakov-Fernique inequality (`sudakov_fernique`) and Slepian's inequality for
expected maxima (`slepian`), from Kahane's comparison inequality.
