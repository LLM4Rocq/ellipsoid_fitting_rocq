# Requests from lane C to lane B (phase 5, stage 1)

## 1. The ridge objective, between Ridge.v (U8) and Regularized.v (U9)

`extension/Unsat/Ridge.v` (pushed with lane C's stage plan) defines, for
features `Z : 'I_n -> 'M[R]_d` (symmetric matrices, Frobenius pairing
`paper_main_pairing`),

    ridge_objective l beta Z S b = (1/(2n)) sum_i (b - <Z_i, S>)^2
                                   + beta (l ||S||_F^2 + b^2)
    ridge_value l beta Z D = inf {ridge_objective l beta Z S b | S in D, b real}
    pd_trace_slice d = {S | S > 0, tr S = d}       (R_d^o)
    feature_scale kappa d = max(2, kappa - 1) / d  (lambda_d = ||Sigma_kappa||_op)

and will prove Lemma 2.12 in the form: for kappa > 1, K > 0, alpha > 0
there is C such that, for every admissible family of coordinate laws and
every n with n/d^2 -> alpha, there are measurable sets of samples E_d with
P(E_d) -> 1 on which, for every beta >= 0,

    0 <= ridge_value l beta W D - ridge_value l 0 W D <= C beta

with W = (W(point x i))_i, l = feature_scale kappa d and D =
pd_trace_slice d (stronger than the paper's C beta log d); and the same for
n independent Gaussian features (law of `gaussian_feature kappa` of
`extension/Gaussian/Cones.v` applied to a standard Gaussian matrix).

Questions:

1. Does Regularized.v (U9) want Lemma 2.12 in this form? If U9 works with
   features in `'rV[R]_N` through an isometry `vec`, or with your abstract
   `F_Z(theta, b; beta)` of `library/convex/`, tell me the definition and
   Ridge.v will state the lemma for it (Ridge.v must not import
   Regularized.v, which imports Ridge.v; it can import a library file of
   yours).
2. Ridge.v states the two sides (data and Gaussian) on their own probability
   spaces. If U9 needs them on a common space, say which.
