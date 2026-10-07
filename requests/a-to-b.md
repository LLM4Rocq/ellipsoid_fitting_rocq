# Requests from lane A to lane B (phase 5, stage 1)

Lane A's stage 1 plan is in the headers of `library/probability/subgaussian.v`,
`subgaussian_matrix.v`, `efron_stein.v`, `tuple_rows.v`,
`extension/Features/Definitions.v`, `Features/Regular.v`,
`extension/Model/Rows.v`, `Model/Measurability.v`,
`extension/Unsat/GoeBridge.v` and `Unsat/FourthMomentThree.v`. Lane A uses
lane B's vocabulary and defines no other version of it: `regular_feature` of
`library/convex/least_squares.v`, and `unsat_feature`, `unsat_features`,
`unsat_cov` and `unsat_value` of `extension/Unsat/LeastSquares.v`.

At Stdlib's `R`, the measurable structure of `library/gaussian/measurable_matrix.v`
is found on `'rV[RR]_(d * d)` with `Local Notation RR := (R : realType)`, not
on `'rV[R]_(d * d)` (as in `theories/Gaussian/Law/LibraryBridge.v` and
`extension/Features/Definitions.v`). `probability 'rV[R]_(d * d) R` does not
elaborate there; `probability 'rV[RR]_(d * d) RR` does.

## 1. Corollary 2.13 (ii), for the stage theorem

`extension/Unsat/FourthMomentThree.v` applies Corollary 2.13 (ii) of
`extension/Unsat/Regularized.v` with `mu d = data_feature_law (nu d) d` and
`nu d = gaussian_feature_law kappa d` (both in
`extension/Features/Definitions.v`). The form planned in `Regularized.v`
suits. Precisely:

```
Theorem unsat_value_concentration (kappa alpha K C0 : R) :
  1 < kappa -> 0 < alpha -> 0 < K -> 0 <= C0 ->
  forall (n : nat -> nat) (mu nu : forall d, probability 'rV[RR]_(d * d) RR)
         (tau : nat -> R),
  universality_density_tends_to n alpha ->
  (forall d, regular_feature K (tau d) (unsat_cov kappa d) (mu d)) ->
  (forall d, regular_feature K (tau d) (unsat_cov kappa d) (nu d)) ->
  (exists D, forall d, (D <= d)%N -> tau d <= C0 / ln d%:R ^+ 3) ->
  exists c : nat -> R, forall eps : R, 0 < eps ->
    paper_main_tends_to (fun d => tuple_prod (fun=> mu d) (n d)
      [set Z | eps < `|unsat_value (n d) d Z - c d|]) 0 /\
    paper_main_tends_to (fun d => tuple_prod (fun=> nu d) (n d)
      [set Z | eps < `|unsat_value (n d) d Z - c d|]) 0.
```

The name is a proposal. Hypotheses required only for every large `d`, and a
regularity constant `K` that may differ between `mu` and `nu`, are fine too.
Lane A provides the hypotheses: `data_feature_law (nu d) d` is regular with
`tau d = C / sqrt d` (`Features/Regular.v`), and `gaussian_feature_law kappa d`
through your Gaussian case of (2.10) (item 3).

## 2. The fitting error as a least squares value

As planned in `LeastSquares.v`: for every sample `x` (with `d >= 1` if
needed),
`universality_fitting_error n d x = 2 * unsat_value n d (unsat_features n d x)`.

## 3. The Gaussian case of (2.10) for a law given by its values

`gaussian_feature_law kappa d` is the image of `gauss (d * d)` under
`g |-> g *m gaussian_feature_mx kappa d`, an mfun declared in
`Features/Definitions.v`. To apply (2.10) without depending on which mfun
instance builds the law, please state it for any law `nu` on `'rV[R]_N`
given by its values:

```
(forall A, measurable A -> nu A = gauss k ((fun x => x *m S) @^-1` A)) ->
S != 0 -> regular_feature (3 `^ (1/4)) (Num.sqrt 2 * opnorm (S^T *m S)) (S^T *m S) nu
```

(or with the constants you choose), as `cf_rV_tuple_prod` of
`fourier/charfun_rV.v` takes the law of its sum.
