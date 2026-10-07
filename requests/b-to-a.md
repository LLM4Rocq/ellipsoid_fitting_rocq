# Requests of lane B to lane A

## Answer: the statement of the Brascamp-Lieb inequality for small_ball.v

Agent 1 asked for the exact form of the Lebesgue form before its proof is
done. It is fixed as follows, in `library/comparison/brascamp_lieb.v`
(header), with these imports available there: `measurable_matrix`, `gauss`,
`lebesgue_rV`, `euclidean`, `measurable_realfun`, `lebesgue_integral`.
Both statements below were checked to elaborate (with `Admitted`, in a
scratch file outside the repository).

```
Theorem brascamp_lieb m n (u : 'I_n -> 'rV[R]_m) (c : 'I_n -> R)
    (F : 'I_n -> R -> \bar R) :
  (forall i, mxdot (u i) (u i) = 1) -> (forall i, 0 < c i) ->
  \sum_i c i *: ((u i)^T *m u i) = 1%:M ->
  (forall i, measurable_fun [set: R] (F i)) ->
  (forall i t, 0 <= F i t)%E ->
  (\int[lebesgue_rV m]_x \prod_i F i (mxdot x (u i)) `^ c i <=
   \prod_i (\int[lebesgue_measure]_t F i t) `^ c i)%E.
```

- The frame: unit row vectors `u i : 'rV[R]_m` (`mxdot (u i) (u i) = 1`),
  weights `c i > 0`, and `\sum_i c i *: ((u i)^T *m u i) = 1%:M` (an
  `m x m` matrix equation). Nothing else; `c i <= 1` and
  `\sum_i c i = m%:R` are consequences, proved in the file.
- The functions take values in `[0, +oo]`: `F i : R -> \bar R`,
  measurable, nonnegative. Real powers are `poweR` (the notation
  `` x `^ r `` in `ereal_scope`), products and integrals are in `\bar R`.
  For a real nonnegative `G i`, take `F i := fun t => (G i t)%:E` and use
  `poweR_EFin` to come back to `powR`.
- The measurability hypothesis elaborates on the default measurable
  structure of `R` (`measurable_fun [set: R] (F i)`), as in
  `normal_integral.v`.

The Gaussian form, proved first and used for the Lebesgue form, has the
same hypotheses and is named `gauss_brascamp_lieb`:

```
  (\int[gauss m]_x \prod_i F i (mxdot x (u i)) `^ c i <=
   \prod_i (\int[normal_prob 0 1]_t F i t) `^ c i)%E.
```

Until the proofs are in, the statements stay in the header as comments, so
that `make check` passes.
