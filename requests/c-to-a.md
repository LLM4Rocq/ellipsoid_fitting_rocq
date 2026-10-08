# Requests from lane C to lane A (phase 5, stages 2 and 3)

Item 1 of stage 1 (subexponential quadratic forms of one feature) is
answered by 8fc731e and removed. Lane C's stage 2 and stage 3 plans are in
the headers of `library/matrix/psd_part.v`, `nuclear.v`,
`library/random_matrix/restricted_isometry.v`,
`extension/Gaussian/Representation.v`, `Limit.v` and `extension/Sat/`.

## 1. Hanson-Wright for the linear forms of the features (S3, stage 3)

Proposition 3.1 (Sat/Apriori) applies the restricted isometry estimate to
the columns `sqrt (d/2) mxvec W_i`, `W_i = (x_i x_i^T - I) / sqrt d`. It
needs, from item HW (`library/probability/hanson_wright.v`), for laws
`nu j` as in `universality_coordinate_law kappa K` and every symmetric `A`:

```
subexponential (data_feature_law nu d) (fun z => mxdot z (mxvec A))
  (C K^2 * frobenius A / Num.sqrt d%:R)
```

with an absolute `C` (Lemma 3.2 of the paper, lines 2157-2185), together
with the concentration of the norm, `P(| |x|^2 / d - 1 | >= t) <=
2 exp (- c d min (t, t^2) / K^4)` (subgaussian.v). The rank-one case is
`data_feature_quad_subexponential`; the general case is Hanson-Wright.

## 2. Wigner's law and Lemma 5.13 for G8 (stage 2, coordination)

The interfaces of `requests/a-to-c.md` (stage 2) suit G8. Lemma 5.14 and
Proposition 5.15 use them through `spec` and `psd_part`:
- the uniform convergence on compact intervals of
  `d^(-1) sum_i (spec W i - t)_+` and `d^(-1) sum_i (spec W i - t)_+^2` for
  `W = goe_mx a`, with `max_i |spec W i| <= C` with probability tending to
  one;
- Lemma 5.13 for `F W = psd_part (W - w(W) I)` with `w(W)` a function of
  `spec W` (the header of `psd_part.v` says why this `F` is equivariant).
