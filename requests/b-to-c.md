# Requests of lane B to lane C

## Corollary 3.13 and Proposition 3.1 (iii) for Proposition 3.4 (S9)

`extension/Sat/LightTail.v` (S9) proves Proposition 3.4 in the form of
`requests/c-to-b.md`, item 2, with `nuclear` and `coef_adj` of
`library/matrix/nuclear.v`. The one-stage bound is proved:
`stage_small_ball` of `extension/Sat/OneStage.v` (Lemma 3.14, given the
revealed coordinates), with the blocks written by column maps
`cU : 'I_p -> 'I_d` (revealed columns) and `cJ : 'I_q -> 'I_d` (fresh
columns), `u_i = (x_(i, cU a))_a` (`stage_row cU x i`, a row vector) and
`Sigma_t = sum_i t_i^2 u_i^T u_i`, a `p x p` matrix. Two inputs of lane C:

1. Corollary 3.13, in the form of the sorted eigenvalues `spec` of
   `library/matrix/von_neumann.v`: for the blocks of the stages (given by
   `cU`, with `c0 d <= p <= d`), every `eps` in `(0, 1)` and every large
   `K`, a measurable event of probability tending to one on which, for
   every `I` (with `|I| <= C0 d ln d`, or every `I`) and every `t` with
   `|t|_2 = 1`, `|t|_oo <= (K d)^(-1/2)` and `t_i = 0` for `i` in `I`,
   `spec Sigma_t` has its first `p - floor (eps p)` entries at least
   `mu` (an absolute constant, `1/8` in the paper). With `spec`, the good
   event of each stage is closed in the revealed coordinates
   (`spec_lipschitz`), which the sequential revealing needs, and
   `spec_decomposition` gives the matrix `Q` that `stage_small_ball` takes.
   Any equivalent form is fine; please say which you choose.
2. Proposition 3.1 (iii): the name of the map `L_X^*` of a sample (I
   expect `coef_adj` of the matrices `W_i = (x_i x_i^T - I) / sqrt d` of
   `Sat/Apriori.v`) and the form of the bound
   `nuclear (L_X^* z) <= C d |z|_2` (a measurable event of probability
   tending to one, uniform in `z`), so that S9 and S10 use the same
   definitions.
