# Ellipsoid fitting in Rocq

This repository contains a Rocq proof of the three main results of *The sharp
SAT/UNSAT phase transition in random ellipsoid fitting* (Misiakiewicz and Wen,
[arXiv:2608.10184v1](https://arxiv.org/abs/2608.10184v1)).

Let x_1, ..., x_n be independent standard Gaussian points of R^d, with n = n(d)
growing with d.

1. **thm:main.** Let p(n, d) be the probability that some positive
   semidefinite matrix S satisfies x_i^T S x_i = d for every i. If
   limsup n/d^2 < 1/4, then p(n, d) tends to 1. If liminf n/d^2 > 1/4, then
   p(n, d) tends to 0.
2. **thm:conditioned.** For every alpha < 1/4 there are constants
   0 < lambda_- <= lambda_+, depending only on alpha, with the following
   property. If limsup n/d^2 <= alpha, then with probability tending to 1
   some S fits every point, has trace d, and satisfies
   lambda_- I <= S <= lambda_+ I.
3. **cor:alternative.** Let E be the event that some real weights y_i with
   sum y_i = 0 make sum y_i x_i x_i^T positive definite. If
   limsup n/d^2 < 1/4, then P(E) tends to 0. If liminf n/d^2 > 1/4, then
   P(E) tends to 1.

Each result also states that the events it measures are measurable.

`extension/` states a second theorem, which nothing proves yet: Theorem 1.2
of Koehler and Sohn, which extends the first result to points with
independent subgaussian coordinates (see below).

## Status

- **Proved.** The kernel accepts `ellipsoid_fitting_main : main_statement`
  (`theories/MainTheorem.v`). `make check` builds the proof, compares
  the axioms of this theorem with `check/assumptions.expected`, and checks
  that the statement and its definitions are unchanged.
- **Reviewed.** On 5 October 2026 Marc Lelarge compared the formal
  statement and its definitions with the paper and found no problem. The
  kernel checks that the statement is proved; this review is the check that
  it says what the paper says.
- **Axioms.** The theorem uses eight classical axioms and nothing else:
  excluded middle (`Classical_Prop.classic`), propositional extensionality
  and dependent functional extensionality (`boolp`, and Stdlib's
  `FunctionalExtensionality`), constructive indefinite description
  (`boolp`), Hilbert's epsilon (`Epsilon.epsilon_statement`), and the two
  decision axioms behind Stdlib's real numbers
  (`ClassicalDedekindReals.sig_forall_dec` and `sig_not_dec`).
  `check/assumptions.expected` gives their exact types. Nothing from the
  paper is assumed.
- **A second statement, not yet proved.** `extension/` states Theorem 1.2
  of Koehler and Sohn, *Universality and sharp thresholds for ellipsoid
  fitting* ([arXiv:2608.27372v1](https://arxiv.org/abs/2608.27372v1)): for
  points with independent coordinates of mean 0, variance 1, fourth moment
  kappa > 1 and subgaussian norm at most K, the same phase transition at a
  threshold alpha*(kappa), a well-conditioned positive definite fit below
  it, and above it the limit e*(alpha, kappa) > 0 of the optimal squared
  fitting error. The statement `universality_statement`
  (`extension/UniversalityStatement.v`) and its definitions
  (`extension/UniversalityDefinitions.v`) were reviewed against the paper
  and accepted before any proof, and are frozen: `make check` checks that
  their code is unchanged since commit `3c6afa1`, which added them to
  `main`. Phase 5 of `AGENTS.md` is the plan of the proof, and
  `extension/README.md` the feasibility study behind it.
- **Stage 1 of that proof.** `universality_unsat_fourth_moment_three`
  (`extension/Unsat/FourthMomentThree.v`) proves the first claim of
  Theorem 1.2 (ii) for coordinates of fourth moment 3, where the threshold
  alpha*(3) is 1/4: if n/d^2 tends to alpha > 1/4, the probability that
  some positive semidefinite S has x_i^T S x_i = d for every i tends to 0.
  The proof follows the paper: the least squares value of the quadratic
  features is bounded below for Gaussian data by the GOE gap of the first
  theorem's proof, and the Lindeberg argument with a barrier (the paper's
  Theorem 2.9 and Corollary 2.13, with its Lemma 2.12 to remove the ridge)
  shows that it concentrates around the same value for the data.

## What to read

The proof is checked by the kernel, so only the statement needs to be read.
It consists of:

- `theories/MainStatement.v`: the statement, with a comment that reads it.
- `theories/PaperMainDefinitions.v`: the definitions it uses (quadratic
  forms, positive semidefinite matrices, the three events, the probability,
  the limsup and liminf conditions).
- `theories/GaussianProbabilityProductDefinitions.v`, and the modules it
  imports (`GaussianProbabilityDefinitions.v`, `GaussianDefinitions.v`,
  `AnalysisIntegralDefinitions.v`): the law of n*d independent standard
  normal coordinates.

The reals are Stdlib's `R`, used through MathComp's structures. Vectors and
matrices are MathComp's.

The statement of the universality theorem is
`extension/UniversalityStatement.v`, with a comment that reads it. Its
definitions, in `extension/UniversalityDefinitions.v`, reuse those of
`theories/PaperMainDefinitions.v` that do not depend on the law of the
points, and take the law of independent coordinates from the library
(`tuple_prod`, `library/probability/lindeberg.v`).

## Building

Tested with:

| Package | Version |
|---|---|
| OCaml | 5.3.0 |
| Rocq (`rocq-core`) | 9.1.1 |
| Rocq Stdlib (`rocq-stdlib`) | 9.0.0 |
| Hierarchy Builder | 1.10.3 |
| MathComp | 2.6.0 |
| MathComp finmap | 2.2.4 |
| MathComp-Analysis, with `reals-stdlib` and `analysis-stdlib` | 1.16.0 |

To install them in a new opam switch:

```sh
opam switch create ellipsoid-fitting ocaml-base-compiler.5.3.0
opam repo add rocq-released https://rocq-prover.org/opam/released
opam repo add coq-released https://coq.inria.fr/opam/released
opam install --deps-only ./rocq-ellipsoid-fitting.opam
```

Then, from the repository root:

```sh
make check ROCQ_SWITCH=ellipsoid-fitting JOBS=8   # the switch created above
make check ROCQ_SWITCH= JOBS=8                    # the rocq on your PATH
```

On 5 October 2026 a full build took 13 minutes with `JOBS=12` on a 16-core
Mac (104 minutes of processor time). Compiling prints eleven warnings, all
at the two `HB.instance` commands of the frozen module
`theories/GaussianProbabilityProductDefinitions.v` (ten
`redundant-canonical-projection` and one `HB: no new instance is
generated`), whose code cannot change. The other modules print none.

## Layout

- `theories/`: 588 modules under the logical root `EllipsoidFitting`. The
  statement (`MainStatement.v`), the theorem (`MainTheorem.v`), the five
  definition modules of the statement, the top of the proof
  (`PaperMainResults.v`, `PaperMainFinalAssembly.v`,
  `PaperMainConditionedLimit.v`) and `Asymptotics.v` are at the top; the
  others are in 33 folders by topic (`Gaussian`, `Gordon`, `Matrix`, `Head`,
  ...), and `theories/A/B.v` is the module `EllipsoidFitting.A.B`. The
  14 subfolders of `Gaussian/` divide its modules further:
  `theories/Gaussian/C/D.v` is the module `EllipsoidFitting.Gaussian.C.D`.
- `extension/`: the universality theorem, under the logical root
  `EllipsoidUniversality` and at Stdlib's `R` like `theories/`: its
  statement and definitions, the feasibility study `extension/README.md`,
  and the folders of its proof: `Model/` (the law of the sample and the
  measurability of the events), `Features/` (the quadratic features of the
  points), `Unsat/` (the unsatisfiable phase), `Gaussian/` (the Gaussian
  model) and `Sat/` (the satisfiable phase).
- `library/`: the library `GaussianAnalysis`, 37 files of general results
  on Gaussian measures, Gaussian comparison and concentration, real
  matrices and probability, over an arbitrary `R : realType`, and the
  Fourier analysis of anti-concentration: characteristic functions of laws
  on the line and on row vectors, written without complex numbers, Levy
  concentration functions and Esseen's inequality, the Brascamp-Lieb
  inequality in Gaussian and Lebesgue form, the vector small-ball
  estimate of Koehler and Sohn, and the Fourier inversion theorem. The
  proof of the paper uses the library at Stdlib's `R`:
  `Gaussian/Law/LibraryBridge` identifies the library's Gaussian measure
  with the product law of the statement,
  `Analysis/RealsBridge` rewrites Stdlib's real functions into MathComp's,
  and 20 other modules of `theories/` require library files directly.
  `library/README.md` gives its conventions, its main results and their
  users. Phase 5 adds the directories `convex/` and `random_matrix/`.
- `check/Assumptions.v`: prints the axioms of the main theorem.
  `check/assumptions.expected` is the expected output.
- `scripts/check_sources.py`: checks that the statement, the theorem and the
  five definition modules of the statement have the same code as at the
  commit in `check/frozen-baseline`, and the statement of the universality
  theorem and its definitions the same code as at commit `3c6afa1`
  (comments may differ); that no module of `theories/`, `library/` or
  `extension/` contains `Admitted`, `Axiom`, `Parameter` or `Conjecture`;
  and that no module of `library/` requires a module of `theories/` or
  `extension/` or Stdlib's reals. `make check` runs it.
- `scripts/export_from_ellipsoid_rocq.py`: the script that copied the proof
  (see below).
- `scripts/unused.py`: lists the declarations of `theories/` that the main
  theorem does not use, from the `.glob` files of a build, and can delete
  them. Its docstring says how it decides. On the current tree it lists
  nothing.
- `scripts/stale_citations.py`: lists the names that the comments of
  `theories/`, `library/` and `extension/` cite but that no declaration
  defines, from the `.glob` files of a build and of the installed
  libraries. `make citations` runs it, and `make check` fails on a stale
  citation (`CITATIONS=no` skips it).

## Where the proof comes from

The proof was developed in
[LLM4Rocq/ellipsoid_rocq](https://github.com/LLM4Rocq/ellipsoid_rocq), in its
directory `analysis/`, and completed on 2 October 2026 (commit `212a249`).
Commit `29df54e` of this repository copies it from commit `9556cdd` of that
repository.

- The 647 modules copied are the dependency closure of `PaperMainResults`
  (the proof) and `PaperMainDefinitions` (the definitions of the statement).
  The only change is the logical root, `Tablet` replaced by
  `EllipsoidFitting`. The export script reproduces commit `29df54e`, not the
  current tree. To verify that commit against a checkout of the source
  repository, run in a checkout of commit `29df54e` of this repository:

  ```sh
  python3 scripts/export_from_ellipsoid_rocq.py ../ellipsoid_rocq 9556cdd --check
  ```

- Since then, what the main theorem does not use has been deleted twice:
  17 modules and 714 declarations of the other modules at the tag
  `phase1`, then 23 modules and 212 declarations of the other modules once
  the proof used the library. `scripts/unused.py` finds them from the
  `.glob` files of a build, and the proof builds without them. Some
  special-purpose proofs were replaced by results of the library, and the
  modules were renamed and grouped in folders.
  Deleted code stays in the history: a general result can be recovered
  from commit `29df54e`, where the modules have their original names, for
  example with `git show 29df54e:theories/OperatorSpaces.v`.
- `MainStatement.v` is the statement of
  `analysis/challenges/paper_main_results/Challenge.v` in the source
  repository, copied verbatim, as a definition instead of an admitted
  theorem. It is also, verbatim, the statement of `paper_main_results` in
  `PaperMainResults.v`.
- `MainTheorem.v` and `check/` replace the source repository's policy module
  `PaperMainPolicy` and its checking scripts.
- Not copied: the 153 other modules of `analysis/`, the challenge files,
  reports and journals, and the older Coquelicot development in `theories/`.

## Planned work

Of the three steps of the plan of `AGENTS.md`, the first and the third are
done, and the second is done in part.

1. `library/` states and proves the general results that the proof needed,
   over an arbitrary `R : realType`, in the style of MathComp-Analysis and
   independently of the paper: the standard Gaussian measure on `'rV[R]_n`
   and its integration by parts, Gaussian interpolation and the comparison
   inequalities of Kahane, Slepian, Sudakov-Fernique and Gordon, escape
   through a mesh, Gaussian concentration and the Poincare inequality, the
   spectral theorem for real symmetric matrices, operator norms and nets,
   Paley-Zygmund and the Lindeberg replacement method.
2. The proof of the paper uses these results at Stdlib's `R` in its
   modules on the comparison inequalities, the spectral theorem, the
   operator norms, the nets, the Paley-Zygmund inequality and the Lindeberg
   method; in its modules on the Gaussian integral on the line, whose
   kernel is the density of the normal law of MathComp-Analysis up to a
   constant (`Gaussian/Line/Kernel`, `Gaussian/Line/Mass`,
   `Gaussian/Line/Moments`, `Gaussian/Line/Expectation`,
   `Gaussian/Line/PolynomialIntegrability`, `Gaussian/Line/QuadraticMGF`);
   and, through `Gaussian/Law/LibraryBridge`, in its modules on the
   iterated Gaussian expectation: the coordinate Stein identities, the
   exchange and the rotation of coordinates, the integrability at every
   level of a continuous function of polynomial growth and the continuity
   of its marginals (`Gaussian/Iterated/Stein`,
   `Gaussian/Iterated/BlockRotation`, `Gaussian/Iterated/PolynomialGrowth`).
   What it no longer needed is deleted: `theories/` had 632 modules and
   102,415 lines at the tag `phase1`, and has 588 modules and 86,410 lines
   now. The library has 37 files and 21,005 lines.
3. The comments no longer describe how the modules were produced, and the
   modules are renamed and grouped in folders.

What remains:

- No human has reviewed the statements of the library yet. The table of
  main results in `library/README.md` is the place to start; the most
  general results are candidates for MathComp-Analysis.
- About 195 modules of `theories/`, those on the Gaussian measure, real
  analysis and matrix norms, still prove general facts in the special form
  that the paper needs, with lists of coordinates and Stdlib's `R`,
  although the library now states them in general: the interpolation
  between two covariances (`Gaussian/Covariance/Definitions` and five
  more; the `Projection` modules use it to compare quadratic Gaussian
  features with their Gaussian replacement, which the library does not
  state in that form), matrix norms (`Matrix/OperatorNorm`,
  `Matrix/FrobeniusNorm` and six more), real analysis in one variable and
  for functions of lists (`Analysis/CoordinateTopology`,
  `Analysis/TaylorRemainder` and ten more), and the machinery of the
  paper's Gibbs laws, soft min-max and cumulants. The facts about the
  iterated expectation that carry no continuity hypothesis (its linearity,
  monotonicity and the identities between its levels) are proved from its
  recursive definition and have no counterpart in the library.

The statement keeps its meaning throughout: `make check` checks after each
step that its code and the code of its definitions are unchanged.

Phase 5 of `AGENTS.md` plans the proof of the universality theorem of
`extension/` in three stages: the unsatisfiable phase at fourth moment 3,
then the Gaussian model and the unsatisfiable phase for every fourth
moment, then the satisfiable phase. Stage 1 is done (above). Its general
results go to `library/`.
