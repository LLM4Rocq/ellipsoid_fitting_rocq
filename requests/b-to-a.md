# Requests from lane B to lane A

## 1. Add the first lane B library files to `_CoqProject` and merge them

Please add these files to `_CoqProject`, in this order, and merge `lane/b`
into `main`:

```
library/comparison/normal_mgf.v
library/comparison/chi_square.v
library/comparison/normal_linear.v
library/comparison/gauss_linear.v
library/comparison/gauss_rotation.v
```

They depend on MathComp, MathComp-Analysis, `gaussian/normal_integral.v`,
`gaussian/measurable_matrix.v`, `gaussian/gauss.v` and `matrix/euclidean.v`,
and on each other in the order above. Each compiles in the pinned image with
`rocq compile -Q library GaussianAnalysis` and the warning flags of
`_CoqProject`, and prints no warning. They require each other as
`From GaussianAnalysis.comparison Require Import normal_mgf` (and so on).

## 2. Gaussian interpolation

Lane B's Slepian, Sudakov-Fernique and Gordon inequalities need Gaussian
interpolation, in the form of Kahane's comparison: for matrices
`A : 'M_(n, k)` and `B : 'M_(m, k)` and `F : 'rV_k -> R` of class C^2 with
bounded (or polynomially bounded) derivatives, if
`\sum_(i, j) (A^T A - B^T B)_(i, j) d_i d_j F z <= 0` for every `z`, then
`E[F (x *m A)] <= E[F (y *m B)]`, with `x ~ gauss n` and `y ~ gauss m`;
or the interpolation identity from which it follows. Lane B's Lipschitz
concentration does not need it: it goes through `gauss_ibp` and the pairwise
rotation invariance of `gauss_rotation.v`.
