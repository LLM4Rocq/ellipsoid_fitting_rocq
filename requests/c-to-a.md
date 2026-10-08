# Requests from lane C to lane A (phase 5, stages 2 and 3)

Item 1 of stage 1 (subexponential quadratic forms of one feature) is
answered by 8fc731e and removed. Lane C's stage 2 and stage 3 plans are in
the headers of `library/matrix/psd_part.v`, `nuclear.v`,
`library/random_matrix/restricted_isometry.v`,
`extension/Gaussian/Representation.v`, `Limit.v` and `extension/Sat/`.

## 1. Hanson-Wright for the linear forms of the features (S3, stage 3)

`extension/Sat/Apriori.v` proves the second a priori estimate
(`adjoint_bound`: `|L_X^* z|_F <= C sqrt d |z|`, hence
`nuclear (L_X^* z) <= C d |z|`) under one hypothesis, which is the
Hanson-Wright inequality (item HW, Lemma 3.2 of the paper, lines 2157-2185):
for `0 < d`, laws `nu j` (`j < d`) as in
`universality_coordinate_law kappa K`, and every `y : 'rV[R]_(d * d)` with
`mxdot y y = 1`,

```
subexponential (data_feature_law nu d) (fun z => mxdot z y)
  (Chw * K ^+ 2 / Num.sqrt d%:R)
```

with an absolute constant `Chw`. By `data_feature_dot` this is
`subexponential (tuple_prod nu d) (quad_form A) (Chw * K ^+ 2)` for every
`A : 'M_d` with `frobenius A = 1` (not necessarily symmetric), so any of
these forms suits. The first a priori estimate (the Gram matrices `Q_I`)
and Lemma 3.12 (S7, and lane B's Corollary 3.13) need the same hypothesis.
Could you say when HW is planned? If lane A has no time for it soon, lane C
can write it in `library/probability/hanson_wright.v`.

The concentration of the norm is proved for the coordinate laws in
`Apriori.v` (`sqnorm_tail`, Bernstein's inequality for `x_j^2 - 1`), so the
planned result of `subgaussian_matrix.v` is not needed for S3; if it lands
in the library, `Apriori.v` will use it instead.

## 2. Wigner's law and Lemma 5.13 for G8 (stage 2, coordination)

The interfaces of `requests/a-to-c.md` (stage 2) suit G8. Lemma 5.14 and
Proposition 5.15 use them through `spec` and `psd_part`:
- the uniform convergence on compact intervals of
  `d^(-1) sum_i (spec W i - t)_+` and `d^(-1) sum_i (spec W i - t)_+^2` for
  `W = goe_mx a`, with `max_i |spec W i| <= C` with probability tending to
  one;
- Lemma 5.13 for `F W = psd_part (W - w(W) I)` with `w(W)` a function of
  `spec W` (the header of `psd_part.v` says why this `F` is equivariant).
