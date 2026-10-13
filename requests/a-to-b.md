# Requests from lane A to lane B

## Review of the proof of T7 (13 October 2026)

Asked by the coordinator for the user on 13 October 2026: an independent
review of the proof of T7 on main c34a953, lane B's work:
`applications/RandomSAT/Model.v`, `Pivotal.v`, `Replacement.v`,
`Forcing.v` and `Variance.v`, `applications/SatVarianceTheorem.v` and
`library/probability/finite_mean.v`. Line numbers are those of main
c34a953; main 88a5dd4 does not change these files.

What was checked, and how:

- The mathematics against the manuscript (family 235,
  `source/sections/concentration.tex` and `forcing.tex`): each claim of
  the headers was compared with the Rocq statement it names, and the route
  of each file with the TeX.
- The Lean route: a script checked every `Lean:` reference of the seven
  files and of the two statement files against
  `lean/OAI/Probability/RandomSAT`. Each name is declared in the named file
  at the named line. The one exception is `finite_mean.v`, which gives no
  line on main (see its entry). The lemmas of `Pivotal.v`,
  `Replacement.v`, `Forcing.v` and `Variance.v` mirror the Lean
  declarations they cite: the insertion delay, the pivotal local bound,
  the occupation sums, the killing fraction, the binomial replacement sum
  and the forcing bound.
- The axioms of `sat_variance_theorem`, by `Print Assumptions` on main
  c34a953: the three `boolp` axioms (`propositional_extensionality`,
  `functional_extensionality_dep`, `constructive_indefinite_description`),
  as the README row says.
- The constant of `Variance.v`, by hand. Take `a = N^(1/K)`, `c = 4 a`,
  `g <= 3 K a`, `M = 2^(K+1) N` and `p = K / N`. With `N a^-(K-1) = a`
  and `M + 1 <= 2 M`, the bound `2 M c (g M p + (M + 1) M p a^-(K-1))` is
  at most `8 4^(K+1) K (3 K + 2^(K+2)) N^(1 + 2/K)`. This is the
  computation of `variance_arith`.

The mathematics is sound, and the route is the one the headers describe.
Two differences from the manuscript need clearer wording:
- the variance step replaces the lemmas 'Deletion variance bound' and
  'Pivotal pairs', and no file of the proof requires
  `efron_stein_omission.v`. The headers say so, but the provenance
  sentences of `Pivotal.v` and `SatVarianceTheorem.v` call the files
  formalizations of these lemmas;
- the binomial summation of `Forcing.v` removes the factor `e^(k M / n)`
  of the manuscript's bound (`eq:forcing-general-cap`). This is why the
  constant is only exponential in `k`; no header says so.

Checked with no finding: `Model.v` (header, statements and README row;
the Lean `clauseHeadEquiv` and `clauseHead_mean` have the shape of
`cjoin_bij` and `unif_mean_clause_split`), and the README rows of
`Model.v`, `Pivotal.v` (its `k <= n` is the hypothesis
`0 < #|clause n k|`, by `card_clause`), `Replacement.v` and `Forcing.v`.

### `applications/RandomSAT/Variance.v` (lane B), lines 30-31 and 40-41

The statement of `sat_variance_bound` (line 191) is existential:
`exists C : R, 0 < C /\ forall N, ...`. The constant
`8 4^(K+1) K (3 K + 2^(K+2))` is the witness that its proof chooses
(`pose C`), not part of a proved statement. The header (lines 30-31, and
"The constant here is explicit", lines 40-41) and the README rows of
`Variance.v` and `SatVarianceTheorem.v` state it as proved.

Proposal, preferred: state the explicit bound as a theorem and derive the
existential one from it. The present proof already proves it.

```
Theorem sat_variance_bound_explicit K N : (3 <= K)%N -> (K.+1 <= N)%N ->
  sat_capped_var R N K <=
    8 * 4 ^+ K.+1 * K%:R * (3 * K%:R + 2 ^+ K.+2) * N%:R `^ (1 + 2 / K%:R).
```

Then the header bullet of lines 30-31 would read:

> - sat_variance_bound_explicit: for K >= 3 and N >= K + 1,
>   sat_capped_var R N K <= C N^(1 + 2/K), with
>   C = 8 4^(K+1) K (3 K + 2^(K+2)); sat_variance_bound is its existential
>   form, the form of the statement. The proof takes a = N^(1/K), ...

Lines 40-41 would end: "The constant here is explicit
(sat_variance_bound_explicit) and holds for every n >= k + 1." In the
README row, `sat_variance_bound` becomes `sat_variance_bound_explicit`
for the displayed inequality.

If the code does not change, the wording changes instead. Lines 30-31:
"... sat_capped_var R N K <= C N^(1 + 2/K) for some C > 0. The proof
takes C = 8 4^(K+1) K (3 K + 2^(K+2)), a = N^(1/K), ...". Lines 40-41:
"The proof uses an explicit constant, valid for every n >= k + 1; the
statement, like the frozen one, only asserts that a constant exists."

Optional, lines 25-26: `kfrac_le_pow` gives `(b / (2 n))^k`, of which
"(b / n)^k" is a consequence; either is correct.

### `applications/SatVarianceTheorem.v` (lane B), lines 13-15 and 17-21

1. Lines 13-15, the constant. The same issue as in `Variance.v`. With the
   explicit lemma, proposed:

   > It is sat_variance_bound of RandomSAT/Variance.v, the existential
   > form of sat_variance_bound_explicit, whose constant is
   > C = 8 4^(k+1) k (3 k + 2^(k+2)); the headers of the files of
   > RandomSAT describe the proof.

   In the README row, "with `C = 8 4^(k+1) k (3 k + 2^(k+2))`" becomes
   "with the constant `C = 8 4^(k+1) k (3 k + 2^(k+2))` of
   `sat_variance_bound_explicit`". Without the lemma: "the proof takes
   `C = ...`".

2. Lines 17-21, the provenance. "with the lemmas before it" says that
   the lemmas 'Deletion variance bound' and 'Pivotal pairs' are
   formalized. They are not: the variance step is the recursion of the
   Lean development, as lines 25-27 say. Proposed:

   > A Rocq formalization of the credited argument of the proposition
   > 'Polynomial concentration' of 'A limiting satisfiability threshold
   > for every fixed clause size' (family 235 of the OpenAI math
   > collection, revision 1581d4cbd, source/sections/concentration.tex)
   > and of the proposition 'Integrated forcing' of
   > source/sections/forcing.tex, with the variance step of the Lean
   > development of the collection in place of the lemmas 'Deletion
   > variance bound' and 'Pivotal pairs'. The proof follows the route of
   > that development, in lean/OAI/Probability/RandomSAT:

### `applications/RandomSAT/Pivotal.v` (lane B), lines 10-16 and 48-50

The file formalizes the recursion of the Lean development, which replaces
the two lemmas of the manuscript (lines 48-54 say so), not the two lemmas
themselves. Proposed lines 10-16:

> Part of target T7 of phase 12 (see Model.v). A Rocq formalization of the
> variance step of the credited argument of the proposition 'Polynomial
> concentration' of 'A limiting satisfiability threshold for every fixed
> clause size' (family 235 of the OpenAI math collection, revision
> 1581d4cbd, source/sections/concentration.tex), in the recursive form of
> the Lean development of the collection, which replaces the lemmas
> 'Deletion variance bound' and 'Pivotal pairs' of the manuscript and
> which this file follows (lean/OAI/Probability/RandomSAT):

At lines 49-50, after the citation of `efron_stein_omission`, add:
"which the proof of T7 does not use".

### `applications/RandomSAT/Replacement.v` (lane B), lines 37-39

`kfrac_le_pow` (line 208) proves `kfrac b v r <= (b / (2 v))^r` for
`b <= v`, `r <= v` and `v > 0`. This is the inequality
`x <= (b / (2 v))^(k-1)` of the manuscript's proof of 'Replacing a
(k-1)-clause'; the header says `(b / v)^r`. `kfrac_small` (line 245) also
assumes `1 <= r < v`. Proposed:

> - Bounds on kfrac: kfrac b v r <= (b / (2 v))^r for b, r <= v and
>   v > 0 (kfrac_le_pow), the recursion in r (kfrac_succ) and its lower
>   bound (kfrac_succ_lower), and kfrac b v r <= 1 / (v + 1) when b <= r
>   and 1 <= r < v, for few forced variables (kfrac_small).

### `applications/RandomSAT/Forcing.v` (lane B), lines 54-58

The difference is stated, but not its consequence. The manuscript's bound
(`eq:forcing-general-cap`) is
`(k M / n) e^(k M / n) g + k M (M + 1) / (2 n) eps`. At `M = 2^(k+1) n`
its constant contains `e^(k 2^(k+1))`. The summation under the binomial
mean of the cap gives `g M p` without that factor; this is why the
constant of `Variance.v` is only exponential in `k`. Proposed, after
"which gives the term g M p":

> instead of the manuscript's (k M / n) e^(k M / n) g; at M = 2^(k+1) n
> this removes the factor e^(k 2^(k+1)) from the constant.

### `library/probability/finite_mean.v` (lane B), lines 32-37

On main c34a953 the provenance paragraph names no proposition or source
file, and its Lean reference has no line. Lane B's commit 3ad2b41 on
lane/b already rewrites it (lines 32-42 there). I checked its three new
references: `uniformMean` is at line 17 of `FiniteMean.lean`,
`uniformVariance` at line 107 and `uniformVariance_fin_succ` at line 322
of `Variance.lean`.

One precision for that version. "the statement of T7 is written with
these means": the statement uses `sat_mean` and `sat_var` of
`SatVarianceDefinitions.v`, which unfold to `unif_mean` and `unif_var` on
the tuples of clauses (`sat_capped_varE` of `Variance.v` passes from one
to the other by `by []`). Proposed: "the statement of T7 is written with
sat_mean and sat_var of SatVarianceDefinitions.v, which unfold to these
means."

Otherwise no finding: every name that the header cites exists, and the
README row matches the statements. The nonempty types it mentions are the
hypotheses of `unif_varE`, `unif_var_le`, `unif_var_pair` and
`unif_var_tuple_cons`.

### `applications/README.md`, the T7 row of the table of targets (master)

On main 88a5dd4 the row lists `probability/efron_stein_omission.v` and
`probability/finite_mean.v`. The proof uses only `finite_mean.v`.
`efron_stein_omission.v` is the general form of the manuscript's lemma
'Deletion variance bound', which the Lean route replaces. Proposed:
"`probability/finite_mean.v`; `probability/efron_stein_omission.v` (the
manuscript's lemma 'Deletion variance bound', not used by the proof)".
This entry is for the master. It is here because the coordinator asked
for all the findings in this file.

### Style (optional)

37 lines are longer than MathComp's 80 columns:
- `Model.v`: lines 107, 214, 271, 286, 321, 327, 336, 339, 409;
- `Pivotal.v`: 104, 132, 235, 387;
- `Replacement.v`: 73, 102, 116, 165, 362, 394;
- `Forcing.v`: 2, 119, 168, 256, 288, 369, 399, 482, 618, 663, 668, 696,
  707, 732, 749;
- `Variance.v`: 6, 139;
- `SatVarianceTheorem.v`: 4.

No rule of AGENTS.md fixes a line length, so this is only a suggestion.
