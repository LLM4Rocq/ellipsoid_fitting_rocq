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

- `theories/`: 605 modules under the logical root `EllipsoidFitting`. The
  statement (`MainStatement.v`), the theorem (`MainTheorem.v`), the five
  definition modules of the statement, the top of the proof
  (`PaperMainResults.v`, `PaperMainFinalAssembly.v`,
  `PaperMainConditionedLimit.v`) and two more modules are at the top; the
  others are in 36 folders by topic (`Gaussian`, `Gordon`, `Matrix`, `Head`,
  ...), and `theories/A/B.v` is the module `EllipsoidFitting.A.B`.
- `library/`: the library `GaussianAnalysis`, 26 files of general results
  on Gaussian measures, Gaussian comparison and concentration, real
  matrices and probability, over an arbitrary `R : realType`. The proof
  uses it at Stdlib's `R`: `Gaussian/LawBridge` identifies the library's
  Gaussian measure with the product law of the statement,
  `Analysis/RealsBridge` rewrites Stdlib's real functions into MathComp's,
  and 20 other modules of `theories/` require library files directly.
  `library/README.md` gives its conventions, its main results and their
  users.
- `check/Assumptions.v`: prints the axioms of the main theorem.
  `check/assumptions.expected` is the expected output.
- `scripts/check_sources.py`: checks that the statement, the theorem and the
  five definition modules of the statement have the same code as at the
  commit in `check/frozen-baseline` (comments may differ), and that no
  module contains `Admitted`, `Axiom`, `Parameter` or `Conjecture`.
  `make check` runs it.
- `scripts/export_from_ellipsoid_rocq.py`: the script that copied the proof
  (see below).
- `scripts/unused.py`: lists the declarations of `theories/` that the main
  theorem does not use, from the `.glob` files of a build, and can delete
  them. Its docstring says how it decides. On the current tree it lists
  only eight function equalities of `Analysis/RealsBridge`, kept so that the
  bridge is complete.

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
   method, and, through `Gaussian/LawBridge`, in its modules on the
   iterated Gaussian expectation: the coordinate Stein identities, the
   exchange and the rotation of coordinates, the integrability at every
   level of a continuous function of polynomial growth and the continuity
   of its marginals (`Gaussian/CoordinateStein`, `Gaussian/CoordinateSwap`,
   `Gaussian/BlockRotation`, `Gaussian/CoordinateMarginals`,
   `Gaussian/QuadraticMGF`). What it no longer needed is deleted:
   `theories/` had 632 modules and 102,415 lines at the tag `phase1`, and
   has 605 modules and 89,109 lines now. The library has 26 files and
   11,097 lines.
3. The comments no longer describe how the modules were produced, and the
   modules are renamed and grouped in folders.

What remains:

- No human has reviewed the statements of the library yet. The table of
  main results in `library/README.md` is the place to start; the most
  general results are candidates for MathComp-Analysis.
- About 215 modules of `theories/`, those on the Gaussian measure, real
  analysis and matrix norms, still prove general facts in the special form
  that the paper needs, with lists of coordinates and Stdlib's `R`,
  although the library now states them in general: the Gaussian integral
  on the line and Stein's identity (`Gaussian/Kernel`, `Gaussian/Mass`,
  `Gaussian/Moments`, `Gaussian/SteinIdentity` and eight more modules),
  the interpolation between two covariances
  (`Gaussian/CovarianceDefinitions` and five more; the `Projection`
  modules use it to compare quadratic Gaussian features with their
  Gaussian replacement, which the library does not state in that form),
  matrix norms (`Matrix/OperatorNorm`, `Matrix/FrobeniusNorm` and six
  more), real analysis for functions of lists (`Analysis/RectangleFubini`,
  `Analysis/ParameterIntegrals` and eight more), and the machinery of the
  paper's Gibbs laws, soft min-max and cumulants. The first group follows
  from the one-dimensional results of the library and can be re-proved from
  them as the modules on the iterated expectation were. The facts about the
  iterated expectation that carry no continuity hypothesis (its linearity,
  monotonicity and the identities between its levels) are proved from its
  recursive definition and have no counterpart in the library.

The statement keeps its meaning throughout: `make check` checks after each
step that its code and the code of its definitions are unchanged.
