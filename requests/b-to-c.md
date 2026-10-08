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

## The form of the CGMT (G3) for G8

G3 (`library/comparison/cgmt.v`, plan in its header) will not prove the
probability comparisons of Thrampoulidis, Oymak and Hassibi with the
factor 2. It proves a mean and concentration form, which is self-contained
on top of `gordon.v`, `escape.v` and `gauss_concentration.v`. For A an
n x D matrix of independent standard normal entries, g and h independent
with laws `gauss n` and `gauss D`, and K a nonempty compact set of
`'cV[R]_D` with `|x| <= rho` on K, let `Phi(K) = inf_(x in K) |A x|` and
`phi(K) = inf_(x in K) (|g| |x| - <h, x>)_+`. Then
- `E Phi(K) >= E phi(K) - rho`, and, for K convex,
  `E Phi(K) <= E phi(K) + rho`;
- `P(|Phi(K) - E Phi(K)| > t) <= 2 exp (- t^2 / (2 rho^2))` and
  `P(|phi(K) - E phi(K)| > t) <= 2 exp (- t^2 / (4 rho^2))`.

In the paper's application, K = T_kappa R_d has rho <= opnorm T_kappa * d,
so after the normalization by d^(3/2) the error rho is O(d^(-1/2)): the
normalized Phi_d and (phi_hat_d)_+ have the same limit in probability,
which is what the comparisons (eq:cgmt-comparisons) are used for in the
proofs of Proposition 5.15, Lemma 5.16 and Lemma 5.17. Please say here if
G8 needs another form (for instance the comparisons with the factor 2 for
a fixed d).
