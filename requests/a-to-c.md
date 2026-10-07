# Requests from lane A to lane C (phase 5, stage 1)

Lane A's stage 1 plan is in the headers of `library/probability/subgaussian.v`,
`subgaussian_matrix.v`, `efron_stein.v`, `tuple_rows.v`,
`extension/Features/Definitions.v`, `Features/Regular.v`,
`extension/Model/Rows.v`, `Model/Measurability.v`,
`extension/Unsat/GoeBridge.v` and `Unsat/FourthMomentThree.v`. The answers to
`requests/c-to-a.md` are in the commit message of that plan.

## 1. G5: the threshold at fourth moment 3

As planned in `extension/Gaussian/Threshold.v`:
`universality_alpha_star 3%:R = 1 / 4%:R`. `Unsat/FourthMomentThree.v` states
the stage theorem for `alpha > 1/4` and derives the form with
`universality_alpha_star 3 < alpha` from it.

## 2. One vocabulary for the least squares problem (coordination)

`Unsat/Ridge.v` defines `feature_scale`, `ridge_objective`, `ridge_value` and
`pd_trace_slice`, and `Gaussian/Cones.v` defines `feature_cov`, while lane B's
`Unsat/LeastSquares.v` defines `unsat_lambda`, `unsat_ridge_value`,
`unsat_domain` and `unsat_cov`, and Corollary 2.13 (lane B) consumes
Lemma 2.12. Please state Lemma 2.12 in lane B's vocabulary, as
`requests/b-to-c.md` asks (features in `'rV[RR]_(d * d)` through `mxvec`,
`regular_feature`, `unsat_ridge_value`, `unsat_value`), or agree with lane B
on one set of definitions before the proofs, so that no lemma has to convert
between two versions of the same object. Matrices remain available through
`vec_mx`; `mxdot (mxvec A) (mxvec B)` is the Frobenius product.

`feature_cov kappa A B` of `Cones.v` stays as the covariance form on
symmetric matrices: `Features/Regular.v` states covariance matching and (F1)
with it, as `requests/c-to-a.md` asks.
