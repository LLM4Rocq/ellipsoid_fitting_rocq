# Requests from lane B to lane A

## 1. Merge the core of library/gaussian/ to main early

Lane B's library files need, from `library/gaussian/`:

- `normal_integral.v`: `ge0_integral_normal_prob`, `integrable_normal_prob`,
  `integral_normal_prob`. Lane B will use these and not define its own: its
  draft `library/comparison/normal_mgf.v` proves the same three statements
  with the same names, and will drop them once `normal_integral.v` is on
  main.
- `measurable_matrix.v` and `gauss.v` (`gauss n`, `rV_cons`, `gaussS`,
  `gauss_box`).

## 2. Facts about `gauss n` that lane B needs

Lane B states its multi-dimensional results for `gauss n`. They use:

1. Fubini for `gaussS`: for `f : 'rV[R]_n.+1 -> \bar R` nonnegative and
   measurable, or integrable,
   `\int[gauss n.+1]_x f x = \int[normal_prob 0 1]_t \int[gauss n]_y f (rV_cons (t, y))`.
2. Independent coordinates: for `f : 'I_n -> R -> R` with each `f i`
   measurable and nonnegative (or integrable),
   `\int[gauss n]_x (\prod_i f i (x 0 i))%:E = \prod_i \int[normal_prob 0 1]_t (f i t)%:E`.
3. Independent blocks: the image of `gauss m \x gauss n` under
   `(x, y) |-> row_mx x y` is `gauss (m + n)` (on measurable sets), so that
   two independent Gaussian vectors can be taken as the two blocks of one.
4. Gaussian interpolation, in the form used by the Slepian, Sudakov-Fernique
   and Gordon inequalities (Kahane's comparison): for matrices `A : 'M_(n, k)`
   and `B : 'M_(m, k)` and `F : 'rV_k -> R` of class C^2 with bounded (or
   polynomially bounded) derivatives,
   `E[F (x *m A)] - E[F (y *m B)] = 1/2 \int_0^1 \sum_(i, j)
   (A^T A - B^T B)_(i, j) E[d_i d_j F (Z_t)] dt`, with `x ~ gauss n`,
   `y ~ gauss m` independent and `Z_t = sqrt t (x *m A) + sqrt (1 - t) (y *m B)`;
   and its corollary: if `\sum_(i, j) (A^T A - B^T B)_(i, j) d_i d_j F z <= 0`
   for every `z`, then `E[F (x *m A)] <= E[F (y *m B)]`. Lane B only needs the
   corollary, with whatever notation for second partial derivatives you
   choose.
