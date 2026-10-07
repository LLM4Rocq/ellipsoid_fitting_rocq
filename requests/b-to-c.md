# Requests of lane B to lane C

## Lemma 2.12 (U8), in the form that Corollary 2.13 (ii) uses

`extension/Unsat/Regularized.v` (lane B, U9) proves Corollary 2.13 (ii)
from Corollary 2.13 (i) and Lemma 2.12 (paper, lines 1476-1494). Lane B
expects from `extension/Unsat/Ridge.v` the following statement at Stdlib's
`R`, with the definitions of `library/convex/least_squares.v` and
`extension/Unsat/LeastSquares.v` (both compile now: `regular_feature`,
`unsat_cov`, `unsat_ridge_value`, `unsat_value`):

```
Theorem unsat_ridge_removal (alpha kappa K C0 : R) :
  0 < alpha -> 1 < kappa -> 0 < K -> 0 <= C0 ->
  exists2 C : R, 0 < C &
  forall (n : nat -> nat) (mu : forall d, probability 'rV[R]_(d * d) R)
         (tau beta : nat -> R),
    universality_density_tends_to n alpha ->
    (forall d, regular_feature K (tau d) (unsat_cov kappa d) (mu d)) ->
    (exists D, forall d, (D <= d)%N -> tau d <= C0 / ln d%:R ^+ 3) ->
    (forall d, 0 < beta d) ->
    paper_main_tends_to
      (fun d => tuple_prod (fun=> mu d) (n d)
        [set Z | C * beta d * ln d%:R <
                 unsat_ridge_value kappa (n d) d (beta d) Z -
                 unsat_value (n d) d Z]) 0.
```

Notes.
- Lane B applies it once to the data features and once to the Gaussian
  features, each a regular feature with covariance `unsat_cov kappa d`, so
  the hypotheses must be about one law. Lane C may add hypotheses that both
  laws satisfy, if the proof needs them: for instance that `mu d` is carried
  by the `mxvec` of the symmetric matrices (Lemma 4.3 works with features in
  S^d), or the subgaussian feature bound of the data. Please state them on
  the law of one feature, and say here which ones.
- One sequence `beta d` at a time is enough for lane B (the paper uses
  `beta d = (q d / ln d)^(1/3)`); the event "for every beta > 0" is not
  needed.
- The lower bound `0 <= unsat_ridge_value - unsat_value` is deterministic;
  lane B proves it in `convex/least_squares.v` (`ls_value` is
  nondecreasing in `beta`), together with the measurability of `ls_value`
  as a function of the tuple of features (`measurable_ls_value`), which the
  event above needs.
- If another form suits the proof better (a high-probability event with an
  explicit probability bound, features as matrices), please say so here
  before lane B proves U9 against this one.
