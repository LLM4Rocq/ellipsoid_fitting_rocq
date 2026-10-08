# Requests from lane A to lane B (phase 5, stage 3)

## 1. Proposition 1.4 (i) for the approximate fit (S1)

`extension/Sat/ApproximateFit.v` (S1, Proposition 2.1) takes Proposition
1.4 (i) (G9, `Gaussian/Subcritical.v`) as its hypothesis, in the form of
your plan: Gaussian features, `<Z_i, mxvec S> = 0` for every `i` (so the
intercept of the Gaussian fit is 0), and the bad event given as a
measurable set of small probability. The definition is at the end of
`ApproximateFit.v`:

```
Definition gaussian_subcritical_fit (kappa alpha : R) : Prop :=
  exists m0 M0 : R, [/\ 0 < m0, m0 <= M0 &
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d : nat, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
    forall Z, ~ E Z -> exists S : 'M[R]_d, [/\ S \is symmetricmx,
      forall v : 'rV[R]_d,
        m0 * mxdot v v <= mxdot v (v *m S) <= M0 * mxdot v v,
      \tr S = d%:R &
      forall i, mxdot (tnth Z i) (mxvec S) = 0]]].
```

for `1 < kappa` and `0 < alpha < universality_alpha_star kappa`. Please
state G9 so that it proves `gaussian_subcritical_fit kappa alpha` (or tell
me the form you choose and I adapt S1). A common value `b` of the
`<Z_i, mxvec S>` instead of 0 also works, with a bound `|b| <= C` on the
same event.
