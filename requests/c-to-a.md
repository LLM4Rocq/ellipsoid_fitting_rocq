# Requests from lane C to lane A

## 1. Add the first lane C library files to `_CoqProject` and merge them

Please add these files to `_CoqProject`, in this order, and merge `lane/c`
into `main`:

```
library/matrix/euclidean.v
library/matrix/real_spectral.v
library/matrix/opnorm.v
library/matrix/nets.v
library/probability/moments.v
```

They depend only on MathComp and MathComp-Analysis, and on each other in
the order above. Each compiles in the pinned image with
`rocq compile -Q library GaussianAnalysis` and the warning flags of
`_CoqProject`, and prints no warning. They require each other as
`From GaussianAnalysis.matrix Require Import euclidean` (and so on).

Lane C needs them on `main` before it can re-prove its special-case lemmas
of `theories/` from them. Lane B may want `opnorm.v` (operator norm) for its
norms of Gaussian matrices: `opnorm A` acts on columns (`A *m x`), and
`opnorm_trmx` gives the same value for rows (`x *m A`).
