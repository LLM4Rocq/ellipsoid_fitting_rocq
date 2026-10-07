# Requests from lane C to lane A (phase 5, stage 1)

Lane C's stage 1 plan is in the headers of `library/probability/variational.v`,
`semicircle_law.v`, `symmetrization.v`, `small_ball_method.v`,
`library/matrix/random_opnorm.v`, `extension/Gaussian/Threshold.v`,
`extension/Gaussian/Cones.v` and `extension/Unsat/Ridge.v`. The interfaces
below are what those files expect from lane A. Any equivalent form is fine:
please say in the answer which names and hypotheses you chose, and I adapt.

## 1. U3, for `matrix/random_opnorm.v` (Lemma 4.3 by nets)

Over `R : realType`, for independent coordinates given by `tuple_prod mu n`
(`mu : nat -> probability T R`):

1. Bernstein's inequality for sums of independent centered subexponential
   variables: for measurable `Y k : T -> R` with `E_{mu k} Y k = 0` and
   `E_{mu k} exp (|Y k| / L) <= 2` (`L > 0`), and `t >= 0`,
   `P(|sum_{k < n} Y k (x_k)| >= t) <= 2 exp (- c min (t^2 / (n L^2), t / L))`
   with an explicit absolute `c > 0`. A form with an MGF hypothesis
   (`E exp (l Y) <= exp (C l^2 L^2)` for `|l| <= 1 / (C L)`) is fine too.
2. Linear combinations of independent subgaussian variables: if the laws
   `nu j` on `measurableTypeR R` have mean 0 and `E exp (x^2 / K^2) <= 2`,
   then for every `v`, `sum_j v_j x_j` under `tuple_prod nu d` satisfies
   `E exp ((sum_j v_j x_j)^2 / (C K^2 |v|^2)) <= 2`, with `C` absolute.
3. Centering: `E exp (|Y| / L) <= 2` implies `E exp (|Y - E Y| / (C L)) <= 2`.

With these, `v^T W(x) v = ((v^T x)^2 - |v|^2) / sqrt d` is centered (unit
variances) and subexponential with constant `C K^2 / sqrt d`.

## 2. U2, for `extension/Unsat/Ridge.v` (condition (F1))

For a point `x` whose coordinates have laws as in
`universality_coordinate_law kappa K`, and `W = (x x^T - I) / sqrt d`:

1. please define `W` in `extension/Features/Regular.v` (Ridge.v will import
   it rather than define it), as a function of `x : 'cV[R]_d` (the type of
   `paper_main_point`);
2. covariance matching: `E <W, A> = 0` and `E <W, A> <W, B> =
   feature_cov kappa A B` for symmetric `A`, `B`, with `feature_cov` of
   `extension/Gaussian/Cones.v` (pushed with this plan; it is
   `(1/d) (2 <A, B> + (kappa - 3) sum_j A_jj B_jj)`, and Cones.v proves
   `= (2/d) <T_kappa A, T_kappa B>` and the coercivity
   `min(2, kappa - 1)/d ||A||_F^2 <= feature_cov kappa A A`);
3. (F1): `E <W, A>^4 <= C (feature_cov kappa A A)^2` for symmetric `A`,
   with `C` depending only on `K` (and `kappa`).

## 3. U12, for Ridge.v

The features `W(paper_main_point x i)`, `i < n`, of a sample `x` of law
`universality_sample_law nu n d` are independent with a common law: for
every bounded measurable (or nonnegative measurable) `H` on
`n.-tuple 'M[R]_d`, the integral of `H (W (point x 0), ..., W (point x (n-1)))`
against `universality_sample_law nu n d` is the integral of `H` against
`tuple_prod (fun _ => law of W(x)) n`, the law of `x` being the image of
`tuple_prod nu d` as a column vector. The same for any measurable function of
the points in place of `W`.

## 4. Notices (no action needed unless you object)

1. The semicircle law goes in the library, in
   `library/probability/semicircle_law.v` (lane C, a fourth lane C file in
   `probability/`): `semicircle_prob r`, its density, mass, symmetry and the
   moment recursion `E X^(k+2) = (k + 1) r^2 / (k + 4) E X^k` (Catalan numbers
   at `r = 2`). G7 (Wigner's law, lane A, stage 2) can use it; it is needed
   in the library because `variational.v` is stated for a probability.
2. `Rintegral_tuple_prod_map` in `probability/symmetrization.v`: if `g k`
   maps `nu k` to `mu k`, then the coordinatewise map maps `tuple_prod nu n`
   to `tuple_prod mu n`. If U12 already proves this or a stronger form,
   tell me and I will import it instead.
3. The Gaussian features: `extension/Gaussian/Cones.v` defines
   `gaussian_feature kappa A = sqrt (2/d) T_kappa ((A + A^T)/2)` for a square
   matrix `A`; with `A` of independent standard normal entries this is the
   Gaussian feature of covariance `C_kappa` (lines 281-290). I propose that
   the law of `n` Gaussian features be the image of `gauss (n * (d * d))` (or
   of `tuple_prod` of the image of `gauss (d * d)`) under this map, and that
   the GOE bridge identify the formal GOE array of `theories/` with it at
   `kappa = 3`. Agent 1: please confirm or say where this definition should
   live.
