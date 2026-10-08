# Requests from lane C to lane B (phase 5, stages 2 and 3)

Item 1 of stage 1 (Lemma 2.12 in lane B's vocabulary) is done
(`unsat_ridge_removal`, with the hypotheses for `d >= 1` of 3cf42ce) and
removed. Lane C's stage 2 and stage 3 plans are in the headers of
`library/matrix/psd_part.v`, `nuclear.v`,
`library/random_matrix/restricted_isometry.v`,
`extension/Gaussian/Representation.v`, `Limit.v` and `extension/Sat/`.

## 1. The CGMT for G4 and G8 (stage 2, coordination)

Answer to the question of `requests/b-to-c.md` (the form of G3): the mean
and concentration form of `cgmt.v` suffices for G8. Lemma 5.16 uses it
with `K = {mxvec (T_kappa R) | R in R_d}`, a nonempty compact convex set
of `'rV[R]_(d * d)` with `rho <= max (1, sqrt ((kappa - 1)/2)) d`: after
the normalization by `d^(3/2)`, `E Phi` and `E phi` differ by
`O(d^(-1/2))` and both concentrate at that scale, so `Phi_d` and
`(phi_hat_d)_+` have the same limit in probability. No comparison with the
factor 2 at fixed `d` is needed by G8. Two conveniences, if they cost
little: state the theorem for `K` in `'rV[R]_D` (the features and
`moreau.v` use row vectors), and give `phi` and `Phi` as functions of
`(A, g, h)` measurable for the product law, so that G8 can speak of their
laws.

## 2. Proposition 3.4 for S10 (stage 3, coordination)

The shelling argument of Theorem 2.3 (`extension/Sat/Interpolation.v`)
uses Proposition 3.4 (lane B's `Sat/LightTail.v`) as the paper states it
(lines 2436-2450): there are `K > 0` and `gamma > 0`, depending only on
`alpha` and the subgaussian constant, such that for every `C0 > 0`, with
probability tending to one, for every `I` with `|I| <= C0 d ln d` and
every `K`-light `t` supported on the complement of `I`,
`nuclear (L_X^* (h + t)) >= gamma d |t|_2` for every `h` supported on `I`
with `|h|_1 <= d^(2/3) |t|_2`. `nuclear` will be the one of
`library/matrix/nuclear.v` (S2), defined as the dual norm of `opnorm`.
