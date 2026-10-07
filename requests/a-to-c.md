# Requests of lane A to lane C

## The forms of Lemma 3.5 and of the whitening matrix used by small_ball.v

`library/fourier/small_ball.v` (lane/a) proves the vector small-ball
estimate from three results of lane C that are not in the library yet.
Any equivalent statement will do, and lane A adapts to what lands. These
are the forms the file uses directly, so stating them this way saves a
conversion.

1. The bound of Lemma 3.5 (`fourier/gauss_factor.v`), with a constant
   that depends only on `v`, `lambda` and `eps`
   (`vector_small_ball_fourier` takes the inner statement for each law):

   ```
   0 < v -> 0 < lambda -> 0 < eps ->
   exists2 C : R, 0 < C &
   forall (mu : probability (measurableTypeR R) R) (r s : R),
     (\int[mu]_x ((x ^+ 2)%R)%:E <= v%:E)%E ->
     conc_fun mu lambda <= 1 - eps ->
     0 < r <= s -> s <= 2^-1 ->
     (\int[lebesgue_measure]_u
        (cf_norm mu u `^ (r ^- 2) *
         expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2)))%:E <= (r * C)%:E)%E
   ```

2. The whitening matrix (`matrix/`), applied to
   `S = \sum_(k < n) (w k)^T *m w k`:

   ```
   S \is symmetricmx ->
   (forall x : 'rV[R]_m, mxdot x x <= mxdot (x *m S) x) ->
   exists W : 'M[R]_m,
     W *m S *m W^T = 1%:M /\
     forall x : 'rV[R]_m, frobenius (x *m W) <= frobenius x
   ```

3. The first half of Lemma 3.5, for the corollary in the paper's form:
   for `M > 0` there is `c > 0` such that `conc_fun mu (8^-1) <= 1 - c`
   for every law `mu` on the line with `\int[mu]_x x%:E = 0`,
   `\int[mu]_x ((x ^+ 2)%R)%:E = 1` and
   `(2^-1)%:E <= \int[mu]_x ((x ^+ 2 * \1_[set y | `|y| <= M] x)%R)%:E`.
