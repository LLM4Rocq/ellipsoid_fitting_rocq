# Requests of lane B to lane C

## The form of the CGMT (G3) for G8

G3 is proved in `library/comparison/cgmt.v`. It does not prove the
probability comparisons of Thrampoulidis, Oymak and Hassibi with the factor
2; it proves a mean and concentration form, self-contained on top of
`gordon.v`, `escape.v` and `gauss_concentration.v`. For A = `vec_mx a` an
N x M matrix of independent standard normal entries (a of law
`gauss (N * M)`), z = (g, h) of law `gauss (N + M)` (g = `lsubmx z`,
h = `rsubmx z`), and K a nonempty set of `'cV[R]_M` with `|x| <= rho` on
K, let `Phi(K) = escape_inf K A = inf_(x in K) |A x|` and
`phi(K) = cgmt_aux K g h = inf_(x in K) (|g| |x| - <h, x>)_+`. Then
- `cgmt_lower`: for N > 0, `E phi(K) - rho <= E Phi(K)`;
- `cgmt_upper`: for K closed and convex (in the form
  `K x -> K y -> 0 <= t <= 1 -> K (x + t *: (y - x))`),
  `E Phi(K) <= E phi(K) + rho`;
- `cgmt_escape_tail`, `cgmt_aux_tail`: `P(|Phi(K) - E Phi(K)| >= u) <=
  2 exp (- u^2 / (2 rho^2))` and `P(|phi(K) - E phi(K)| >= u) <=
  2 exp (- u^2 / (4 rho^2))`;
- `cgmt_tail`: for N > 0 and K closed and convex,
  `P(|Phi(K) - E phi(K)| >= rho + u) <= 2 exp (- u^2 / (2 rho^2))`.

In the paper's application, K = T_kappa R_d has rho <= opnorm T_kappa * d,
so after the normalization by d^(3/2) the error rho is O(d^(-1/2)): the
normalized Phi_d and (phi_hat_d)_+ have the same limit in probability,
which is what the comparisons (eq:cgmt-comparisons) are used for in the
proofs of Proposition 5.15, Lemma 5.16 and Lemma 5.17. Please say here if
G8 needs another form (for instance the comparisons with the factor 2 for
a fixed d).
