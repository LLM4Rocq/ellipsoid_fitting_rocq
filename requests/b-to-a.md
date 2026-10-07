# Requests of lane B to lane A

These are the interfaces that lane B's stage 1 items (U4 to U7, U9) expect
from lane A. Lane B offers in return the definitions of
`library/convex/least_squares.v` (`ls_objective`, `ls_barrier_value`,
`ls_value`, `regular_feature`) and of `extension/Unsat/LeastSquares.v`
(`unsat_feature`, `unsat_features`, `unsat_cov`, `unsat_lambda`,
`unsat_domain`, `unsat_ridge_value`, `unsat_value`), which compile now.

## 1. Fubini at one coordinate of `tuple_prod` (U12 or U2)

Theorem 2.9 (`convex/barrier_lindeberg.v`) conditions on all the features
but one, as Efron-Stein does. Please add to `probability/` (for instance
`efron_stein.v` or `tuple_rows.v`), for `T : measurableType d`,
`mu : nat -> probability T R`, `n`, `i : 'I_n`:

```
Lemma integral_tuple_prod_set (F : n.-tuple T -> \bar R) :
  measurable_fun setT F -> (forall x, 0 <= F x) ->
  \int[tuple_prod mu n]_x F x =
    \int[tuple_prod mu n]_x \int[mu i]_t F (tuple_set x i t).

Lemma integrable_tuple_prod_set (F : n.-tuple T -> \bar R) :
  (tuple_prod mu n).-integrable setT F ->
  \int[tuple_prod mu n]_x F x =
    \int[tuple_prod mu n]_x \int[mu i]_t F (tuple_set x i t).
```

with the measurability of `x |-> \int[mu i]_t F (tuple_set x i t)` (it does
not depend on `x i`) and, in the integrable case, the integrability of
`t |-> F (tuple_set x i t)` for almost every `x`. The names are proposals.
If lane A prefers to state them with the coordinate `i` split off
(`tuple_cons` after a permutation), that is fine as long as the form above
follows.

## 2. Efron-Stein for `tuple_prod` (U2)

The variance bound (2.13) of Theorem 2.9 uses Efron-Stein in the form
"variance at most the sum of the expected conditional variances":

```
Theorem efron_stein (F : n.-tuple T -> R) :
  F \in Lfun (tuple_prod mu n) 2%:E ->
  'V_(tuple_prod mu n)[F] <=
    \sum_(i < n) \int[tuple_prod mu n]_x
       'V_(mu i)[fun t => F (tuple_set x i t)].
```

or the same with the right side written
`\int[tuple_prod mu n]_x \int[mu i]_t (F (tuple_set x i t) - m i x) ^+ 2`
for `m i x = \int[mu i]_s F (tuple_set x i s)`. Lane B then uses
"variance at most the second moment about any point" with the
leave-one-out value as the point.

## 3. The form of U2's regularity result, for U9 and U10

Corollary 2.13 (`extension/Unsat/Regularized.v`) is stated for two
sequences of feature laws on `'rV[R]_(d * d)` with
`regular_feature K (tau d) (unsat_cov kappa d) (mu d)` (at Stdlib's `R`).
For U10, lane A will need, in this form:

- Proposition 2.6 at kappa = 3 (then every kappa): for coordinate laws
  `nu d j` with `universality_coordinate_law kappa K`, the law of
  `unsat_feature d x`, with `x` the column of `d` independent coordinates of
  laws `nu d j`, is `regular_feature C (C / sqrt d) (unsat_cov kappa d)`,
  with `C` depending only on `kappa` and `K`;
- for the Gaussian twin, `gauss_regular_feature` (lane B,
  `convex/barrier_lindeberg.v`) applied to a matrix `S` with
  `S^T S = unsat_cov kappa d`; at kappa = 3, the GOE feature of the bridge.
- (U12) the law of `unsat_features x` under `universality_sample_law nu n d`
  is `tuple_prod (fun=> mu d) n`, with `mu d` the law of one feature.

If lane A prefers another form (features as matrices, another name for
the covariance), please say so here before lane B proves U9 against it.
