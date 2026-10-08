# Requests from lane C to lane B (phase 5, stages 2 and 3)

Item 1 of stage 1 (Lemma 2.12 in lane B's vocabulary) is done
(`unsat_ridge_removal`, with the hypotheses for `d >= 1` of 3cf42ce) and
removed. Lane C's stage 2 and stage 3 plans are in the headers of
`library/matrix/psd_part.v`, `nuclear.v`,
`library/random_matrix/restricted_isometry.v`,
`extension/Gaussian/Representation.v`, `Limit.v` and `extension/Sat/`.

## 1. The CGMT for G4 and G8 (stage 2, coordination)

Answer to the question of `requests/b-to-c.md` (the form of G3): the mean
and concentration form of `cgmt.v` suffices for G8. Lemma 5.16 uses it
with `K = {mxvec (T_kappa R) | R in R_d}`, a nonempty compact convex set
of `'rV[R]_(d * d)` with `rho <= max (1, sqrt ((kappa - 1)/2)) d`: after
the normalization by `d^(3/2)`, `E Phi` and `E phi` differ by
`O(d^(-1/2))` and both concentrate at that scale, so `Phi_d` and
`(phi_hat_d)_+` have the same limit in probability. No comparison with the
factor 2 at fixed `d` is needed by G8. Two conveniences, if they cost
little: state the theorem for `K` in `'rV[R]_D` (the features and
`moreau.v` use row vectors), and give `phi` and `Phi` as functions of
`(A, g, h)` measurable for the product law, so that G8 can speak of their
laws.

## 2. Proposition 3.4 for S10 (stage 3): the exact form

Theorem 1.9 (`small_residual_interpolation_limit` of
`extension/Sat/Interpolation.v`, which proves lane A's hypothesis
`small_residual_interpolation`) takes Proposition 3.4 as its hypothesis
`light_tail_bound kappa K alpha`, defined in that file:

```
Definition light_tail_bound (kappa K alpha : R) : Prop :=
  exists K1 gam : R, [/\ 0 < K1, 0 < gam &
  forall C0 : R, 0 < C0 ->
  forall nu : nat -> nat -> probability (measurableTypeR R) R,
    (forall d j, (j < d)%N -> universality_coordinate_law kappa K (nu d j)) ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (universality_sample_law (nu d) (n d) d E <= eps%:E)%E &
    forall x, ~ E x -> forall (I : {set 'I_(n d)}) (h t : 'rV[R]_(n d)),
      #|I|%:R <= C0 * d%:R * ln (d%:R : R) ->
      supported I h -> supported (~: I) t ->
      (forall i, K1 * d%:R * t 0 i ^+ 2 <= mxdot t t) ->
      l1_norm h <= d%:R * frobenius t ->
      gam * d%:R * frobenius t <= nuclear (sample_adj x (h + t))]].
```

for `1 < kappa`, `0 < K` and `0 < alpha < 1/2`. Two differences with the
paper's display: the heads are bounded by `|h|_1 <= d |t|_2` instead of
`d^(2/3) |t|_2` (the paper notes that any exponent in `(1/2, 1)` works;
the exponent 1 is what `light_count` allows, `r <= d`, and it saves
`powR`), and `t` is not normalized (`K1 d t_i^2 <= |t|^2`, so homogeneity
reduces it to your unit light tails). `sample_adj x` is `coef_adj` of
`sample_W x i = (x_i x_i^T - I) / sqrt d` (`Sat/Apriori`, with
`paper_main_point x i` a column), `supported` and `supp` are those of
`library/random_matrix/restricted_isometry.v`, `l1_norm h = sum_i |h_i|`
(`Sat/Interpolation`). If another form suits you better, say which and I
adapt Theorem 1.9.
