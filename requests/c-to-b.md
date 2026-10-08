# Requests from lane C to lane B (phase 5, stage 1)

## 1. Lemma 2.12 (U8) in lane B's vocabulary: proved

Answer to `requests/b-to-c.md` (the form of Lemma 2.12 for Corollary 2.13
(ii)). `extension/Unsat/Ridge.v` now proves `unsat_ridge_removal` below,
with `C = max (2, kappa - 1) / min (2, kappa - 1) + 1`. Its `ln` is the
logarithm of MathComp-Analysis (`exp.v`), which `Ridge.v` imports after
`Reals`; a file that imports only `Reals` reads `ln` as Stdlib's
`Rpower.ln`, which `RlnE` of `Rstruct_topology` converts. The statement
is at Stdlib's `R`, with `RR := (R : realType)` as in
`Features/Definitions.v`, the definitions of
`library/convex/least_squares.v` and `extension/Unsat/LeastSquares.v`, and
`subexponential` of `library/probability/subgaussian.v`:

```
Theorem unsat_ridge_removal (alpha kappa K L0 : R) :
  0 < alpha -> 1 < kappa -> 0 < K -> 0 < L0 ->
  exists2 C : R, 0 < C &
  forall (n : nat -> nat) (mu : forall d, probability 'rV[RR]_(d * d) RR)
         (tau beta : nat -> R),
    universality_density_tends_to n alpha ->
    (forall d, regular_feature K (tau d) (unsat_cov kappa d) (mu d)) ->
    (forall d (v : 'rV[RR]_d), mxdot v v <= 1 ->
       subexponential (mu d) (fun z => mxdot z (mxvec (v^T *m v)))
         (L0 / Num.sqrt d%:R)) ->
    (forall d c, measurable [set Z : (n d).-tuple 'rV[RR]_(d * d) |
       c < unsat_ridge_value kappa (n d) d (beta d) Z - unsat_value (n d) d Z]) ->
    (forall d, 0 <= beta d) ->
    paper_main_tends_to
      (fun d => tuple_prod (fun=> mu d) (n d)
        [set Z | C * beta d * ln d%:R <
                 unsat_ridge_value kappa (n d) d (beta d) Z -
                 unsat_value (n d) d Z]) 0.
```

Differences with the form of `b-to-c.md`:

1. One more hypothesis on the law of one feature: its quadratic forms are
   subexponential with constant `L0 / sqrt d` (Lemma 4.3 bounds the
   operator norm of `sum_i eps_i Z_i` through them, by nets and Bernstein's
   inequality). Both feature laws satisfy it: the data features with
   `L0 = C K^2` (`mxdot (unsat_feature d x) (mxvec (v^T *m v)) =
   ((v x)^2 - |v|^2) / sqrt d`; `subgaussian_lincomb`, `subexponential_sqr`
   and `subexponential_center`), the Gaussian features with
   `L0 = 2 sqrt (max (2, kappa - 1))` (the quadratic form is normal with
   variance `C_kappa(v^T v, v^T v) <= max (2, kappa - 1) / d`). Lane C asks
   lane A for these two facts (`requests/c-to-a.md`), since lane A owns the
   two laws.
2. The measurability of the gap events, for every threshold `c`, is a
   hypothesis: it follows from the measurability of `ls_value` that lane B
   plans in `convex/least_squares.v`, and Ridge.v needs it to compare
   measures.
3. `C0` and the bound on `tau` are not needed: `tau` is arbitrary.
4. `0 <= beta d` is enough.

The proof: with `s_d^2` of order `ln d`, the small-ball method in Markov
form (`library/probability/small_ball_method.v`) shows that with
probability tending to one every `(theta, b)` with `theta` in
`unsat_domain d` and `C_kappa(theta, theta) + b^2 >= s_d^2` has
`(1/n) sum_i (<Z_i, theta> - b)^2 >= c (C_kappa(theta, theta) + b^2)`;
near-minimizers of the unregularized problem then have
`lambda |theta|^2 + b^2 <= C s_d^2`, so the gap is at most
`C beta ln d`. If another form suits U9 better, tell me here.
