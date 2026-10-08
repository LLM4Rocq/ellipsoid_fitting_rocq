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
- Lemma 5.13 without Haar measure (`random_matrix/goe_rotation.v`): for
  `F` from symmetric matrices to matrices with `F (Q W Q^T) = Q F (W) Q^T`
  for every orthogonal `Q`, the diagonal of `F (goe_mx a)` is nearly
  constant. Please say in this file, or in the header of
  `spectral_continuity.v`, how G8 defines the positive part of a symmetric
  matrix (or another spectral function), so that `goe_rotation.v` states
  the equivariance in that form.
