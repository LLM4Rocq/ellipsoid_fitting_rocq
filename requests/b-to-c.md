# Requests from lane B to lane C

## Estimates of T7 and T4b (13 October 2026)

Asked by the master on 13 October 2026, since T4b is on the critical path.

- T7, done so far. On lane/b: library/probability/finite_mean.v (7f40730),
  the uniform means on finite types in which sat_mean is written. In
  scratch, compiling against the accepted definitions:
  - RandomSAT/Model.v (about 420 lines): sat_prefix_len t is the lifetime
    of the full solution set, the head split of a clause, and
    #|clause n k| = 'C(n, k) 2^k;
  - RandomSAT/Pivotal.v (about 380 lines): Var V_n <= 2 M times the sum
    over j < M of E min(M q_j, 1), q_j the killing chance after j clauses;
  - RandomSAT/Replacement.v (about 330 lines so far): q = 'C(b, k) /
    ('C(n, k) 2^k) with b the number of forced variables, and the bounds
    on this fraction.
  The route follows the Lean development of the collection (variance by a
  recursion over the clause process, forcing by the erasure of one
  variable), whose finite averages match the definitions.
- T7, remaining: the replacement inequality (about 200 lines); Forcing.v
  (erasure of the head variable, binomial recursion, renaming symmetry,
  integrated forcing; about 800 lines); Theorem.v and SatVarianceTheorem.v
  (the powR constants and the assembly; about 300 lines). About 1,300
  lines, 6 to 10 hours of work.
- T4b: about 500 lines, 3 to 5 hours. The norm of sk_coupling from
  goe_opnorm_edge_tail and Gaussian tails of the diagonal entries; the row
  sums by Gaussian concentration of the sqrt (2 / n)-Lipschitz map
  a |-> |row i of goe_mx a| with a union bound over the rows, instead of
  chi-square laws; the entries by Gaussian tails and a union bound over
  the n^2 entries; measurability from continuity.
- Proposal: if T4a is close, I switch to T4b now and come back to T7 after
  it; T7's scratch files are stable. Otherwise I finish T7 first. I
  continue T7 until you say.
