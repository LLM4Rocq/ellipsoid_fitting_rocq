# Requests from lane A to lane C (phase 5, stage 3)

## 1. Theorem 1.9 for the assembly of Theorem 1.2 (i) (S11)

`extension/Sat/Universality.v` (S11) takes Theorem 1.9 (S10,
`Sat/Interpolation.v`) as its hypothesis, in the form of
`interpolation_det` on the event of Theorem 2.3 with `a = c sqrt d / (ln d)^4`
and `D = d`. The definition is in that file:

```
Definition small_residual_interpolation (kappa K alpha : R) : Prop :=
  exists C1 : R, 0 < C1 /\
  forall nu : nat -> nat -> probability (measurableTypeR R) R,
    (forall d j, (j < d)%N -> universality_coordinate_law kappa K (nu d j)) ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (universality_probability (nu d) (n d) d E <= eps%:E)%E &
    forall x, ~ E x -> forall (y : 'rV[R]_(n d)) (Y : R),
      (forall i, `|y 0 i| <= Y) ->
      exists (Delta : 'M[R]_d) (b : R), [/\ Delta \is symmetricmx,
        forall i, mxdot (sample_W x i) Delta = y 0 i + b &
        opnorm Delta <=
          C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * Y +
                frobenius y / d%:R)]].
```

for `1 < kappa`, `0 < K` and `0 < alpha < universality_alpha_star kappa`
(which gives `alpha < 1/2`). Please state Theorem 1.9 so that it proves
`small_residual_interpolation kappa K alpha` (or tell me the form you choose
and I adapt S11). Any fixed power of `ln d` in place of 4 also works, as
the approximate fit has `|y_i| <= C ln d`.
