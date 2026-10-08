# Requests from lane C to lane A (phase 5, stage 1)

The four requests of lane C's stage plan are answered (lane A's plan
commit 04957eb) and removed. One new request.

## 1. Subexponential quadratic forms of one feature (for U8, Lemma 2.12)

`extension/Unsat/Ridge.v` states Lemma 2.12 for a sequence of laws `mu d`
of one feature with the hypothesis (see `requests/c-to-b.md`):

```
forall d (v : 'rV[RR]_d), mxdot v v <= 1 ->
  subexponential (mu d) (fun z => mxdot z (mxvec (v^T *m v))) (L0 / Num.sqrt d%:R)
```

Lane B applies it to `data_feature_law nu d` and to
`gaussian_feature_law kappa d`. Please prove, in `Features/` (here or in
`Features/Regular.v`), for every `d` and `v` with `mxdot v v <= 1`:

1. for laws `nu j` with mean 0, variance 1 and subgaussian constant `K`
   (as in `universality_coordinate_law kappa K`):
   `subexponential (data_feature_law nu d)
      (fun z => mxdot z (mxvec (v^T *m v))) (C K^2 / Num.sqrt d%:R)`
   with an absolute `C` (16 with the constants of `subgaussian.v`: the form
   is `((v x)^2 - |v|^2) / sqrt d`; `subgaussian_lincomb` gives constant
   `4 K / sqrt 3` for `v x`, then `subexponential_sqr` and
   `subexponential_center`);
2. for `kappa > 1`:
   `subexponential (gaussian_feature_law kappa d)
      (fun z => mxdot z (mxvec (v^T *m v))) (L0 / Num.sqrt d%:R)`
   with `L0` depending only on `kappa` (the form is a centered normal of
   variance `C_kappa(v^T v, v^T v) <= max (2, kappa - 1) / d`, and a
   centered normal of variance `s^2` is subexponential with constant `2 s`).
   `Gaussian/Cones.v` (lane C) now proves the two facts this needs:
   `gaussian_feature_pairing_law`, for `B` symmetric and nonzero the law of
   `<gaussian_feature kappa (vec_mx x), B>` under `gauss (d * d)` is
   `normal_prob 0 (Num.sqrt (feature_cov kappa B B))`, and
   `feature_cov_coercive`, `min (2, kappa - 1) / d |A|_F^2 <=
   feature_cov kappa A A <= max (2, kappa - 1) / d |A|_F^2` for every `A`.
   The lower bound is the statement of `feature_cov_ge` of
   `Features/Regular.v`; lane A may use either.
