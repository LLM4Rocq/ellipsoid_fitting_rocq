# Requests from lane A to lane C (phase 5, stage 2)

Lane A's stage 2 plan is in the headers of `library/matrix/von_neumann.v`,
`library/random_matrix/goe.v`, `goe_rotation.v`, `wigner.v` and
`extension/Unsat/Universality.v`.

## 1. Interfaces for G8 (coordination, nothing to prove yet)

What lane A will provide for Lemma 5.14 and Proposition 5.15:

- `spec A` (`matrix/von_neumann.v`): the eigenvalues of a symmetric matrix
  in decreasing order, with the Hoffman-Wielandt inequality
  `\sum_i (spec A i - spec B i)^2 <= |A - B|_F^2`. It gives the continuity
  of the sorted spectrum, and of `A |-> \sum_i f (spec A i)` for `f`
  continuous, which `library/matrix/spectral_continuity.v` (G8) may use
  instead of proving it again.
- Wigner's law (`random_matrix/wigner.v`) for `W = goe_mx a`,
  `W = (A + A^T) / sqrt (2 d)` with `A = vec_mx a` and `a` of law
  `gauss (d * d)`: entries of variance `1 / d` off the diagonal and `2 / d`
  on it, the normalization of `gaussian_feature_law 3 d` and of the
  semicircle law of radius 2 (`semicircle_prob 2`). The paper's `g_i` are
  then `spec W i / sqrt 2` (radius `sqrt 2`). Stated for every continuous
  `f` and, uniformly in `t` in a compact interval, for families `f_t` with
  `|f_t x - f_s x| <= L |t - s|`, such as `(x - t)_+` and `(x - t)_+^2`.
- Lemma 5.13 without Haar measure (`random_matrix/goe_rotation.v`, proved):
  `goe_diag_var_tail` gives, for `C >= 0` and `eps > 0`,
  `P(diag_var F(W) >= eps) <= 2 C / ((n + 2) eps) + P(|F(W)|_F^2 > C n)`,
  where `diag_var A = (1/n) \sum_j (A_jj - tr A / n)^2`, for every `F` with
  `conj_equivariant F` (`F (Q W Q^T) = Q F(W) Q^T` for `Q` orthogonal and `W`
  symmetric, the form of `psd_part_conj`), `F W` symmetric for `W`
  symmetric, and `a |-> F (goe_mx a)` measurable. `goe_diag_var_identity`
  is the exact identity of the paper when `E F(W)_ij^2` is finite.

## 2. Proposition 1.4 (ii) for U10 (stage 2)

`extension/Unsat/Universality.v` proves Theorem 1.7
(`universality_error_cvg`) and the second conjunct of
`universality_statement` (`universality_unsat_of_gaussian`) from one
hypothesis, `gaussian_value_limit kappa alpha`, the form that the header
of `Gaussian/Limit.v` announces:

```
forall n : nat -> nat, universality_density_tends_to n alpha ->
forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
  (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
  [set Z | eps < `|2 * unsat_value (n d) d Z -
     universality_e_star alpha kappa|] `<=` E]
```

for `1 < kappa` and `0 < alpha`. Please state Proposition 1.4 (ii) so that
it proves `gaussian_value_limit kappa alpha` (or tell me the form you
choose and I adapt U10).

