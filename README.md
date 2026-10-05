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
Mac (104 minutes of processor time). The compiler prints some deprecation
warnings; they do not affect the proof.

## Layout

- `theories/`: 632 modules under the logical root `EllipsoidFitting`. They
  are `MainStatement.v`, `MainTheorem.v` and the 630 modules of the proof.
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
  them. Its docstring says how it decides. `unused.txt` is its output on the
  current tree.

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

- Since then, 17 of these modules and 714 declarations of the others have
  been deleted, because the main theorem does not use them.
  `scripts/unused.py` finds them from the `.glob` files of a build, and the
  proof builds without them. Deleted code stays in the history: a general
  result can be recovered from commit `29df54e`, for example with
  `git show 29df54e:theories/OperatorSpaces.v`.
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

This is the copy without what the main theorem does not use. The modules
keep their names from the source repository (many start with `PaperMain`),
many comments still describe how the port was made, and much of the general
mathematics is written for this paper only. The plan, described for the agents in `AGENTS.md`:

1. Build `library/` (logical root `GaussianAnalysis`): the general results
   of the proof (Gaussian integration by parts and interpolation,
   concentration, Slepian and Gordon comparison, the spectral theorem for
   real symmetric matrices, nets, moment inequalities), stated over an
   arbitrary `R : realType` in MathComp-Analysis style, independent of the
   paper. `library/README.md` gives its conventions.
2. Make the proof of the paper use the library, and delete what it no
   longer needs.
3. Remove notes about the port from comments, then rename the remaining
   modules and group them in folders.

These steps rename or remove modules and lemmas, so do not cite those names
yet. The statement keeps its meaning throughout: `make check` checks after
each step that its code and the code of its definitions are unchanged.
