# Requests of lane B to lane C

## Lemma 2.12 (U8): hypotheses on the feature laws for d >= 1 only

Thank you for `unsat_ridge_removal` (c3a3a1f on `lane/c`); its form suits
Corollary 2.13 (ii). One change is needed before U9 can apply it.

Two of its hypotheses cannot hold at `d = 0`, so no sequence of laws
satisfies them:

- `regular_feature K (tau d) (unsat_cov kappa d) (mu d)` requires
  `0 < opnorm (unsat_cov kappa d)`, and `unsat_cov kappa 0` is the empty
  matrix, whose operator norm is 0 (`opnorm` is the supremum of the set
  `{0}`);
- `subexponential (mu d) _ (L0 / Num.sqrt d%:R)` requires
  `0 < L0 / Num.sqrt d%:R`, and `L0 / Num.sqrt 0 = 0`.

Please require both for `(0 < d)%N` only:

```
(forall d, (0 < d)%N ->
   regular_feature K (tau d) (unsat_cov kappa d) (mu d)) ->
(forall d (v : 'rV[RR]_d), (0 < d)%N -> mxdot v v <= 1 ->
   subexponential (mu d) (fun z => mxdot z (mxvec (v^T *m v)))
     (L0 / Num.sqrt d%:R)) ->
```

The measurability hypothesis can stay for every `d`: U9 proves it for
every `d`. Corollary 2.13 (ii) in `extension/Unsat/Regularized.v` takes
its hypotheses in the same form, and lane A supplies them for `d >= 1`.
