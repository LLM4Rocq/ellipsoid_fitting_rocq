# Changelog

The changes made since the last tag, then the tagged versions of this
repository, newest first. Each date is that of the tagged commit. Every tag
is annotated, and its message says more: `git show phase8` prints the
message of `phase8`. Phases 2 and 3 have no tag. `stage1` and `stage2` mark
the first two stages of phase 5. [doc/README.md](doc/README.md) explains the
terms used here, such as phase, step 18 and the user.

## Unreleased

The changes since the tag `shifted`. None of them changes a Rocq statement,
definition or proof.

### On GitHub since 25 October 2026

Three commits. `make check` passed on the tree of each before the commit.

- 5893184e: Document the row-size condition and the reindexing statistic,
  in one table row of `extension/README.md` and the header comment of
  `extension/Shifted/SparseDimensions.v`; no lemma, statement, proof, check
  file or script changes (run d8bb8f380183817de780a550701eabc6).
- 15d9fb22: Correct the proof route and a log factor in the documentation,
  in `extension/README.md` and `doc/shifted-gaussian.tex` (run
  9fa6958cfb953fda340ef332415c0bc6).
- 0682ed25: Cite the tag shifted and its commits in
  `doc/shifted-gaussian.tex` (run 3bc585290b5e33d875c455fa6e33c579).

### The documentation cleanup

Documentation only: no `.v` file, check file, script, `Makefile` or
`_CoqProject` changes, and the checker reads the content of none of the
changed paths. `make check` last passed at 5893184e (run
d8bb8f380183817de780a550701eabc6).

- The README of 1,038 lines moved to `doc/details.md`, and the rules given
  to the AI agents, 2,910 lines, to `doc/history/agent-rules.md`. Each
  gained a short header; the rest of its text is unchanged. The same
  commit installs the short `README.md` and `AGENTS.md` that replace
  them. `CLAUDE.md` stays a symbolic link to `AGENTS.md`.
- New: `CHANGELOG.md` and `doc/README.md`.
- `.mcp.json` deleted: it started an MCP server that visitors do not have.

## shifted (2026-10-24, commit 305747af)

Step 18: the shifted-Gaussian extension, seven theorems on translated
samples, merged onto phase 14 under the repaired checker, with 23 new
library files.

## phase14 (2026-10-23, commit 5f81a422)

The PSD rank theorem of the positively shifted matching matrices and its
corollary on exact semidefinite lifts, with three new library files and the
check of the five general statements of the library that the user accepted.

## phase13 (2026-10-21, commit f16e6a26)

Four theorems of two manuscripts of the OpenAI math collection, the
satisfiability threshold of random k-SAT among them, with eight new library
files, the frozen statement of the PSD rank theorem, the check of the 70
general statements of the library that the user accepted, and the repaired
checks.

## phase12 (2026-10-13, commit 90468830)

Seven theorems of manuscripts of the OpenAI math collection whose proofs
reuse the library, formalized in `applications/` over an arbitrary
`realType`, with twelve new library files.

## phase11 (2026-10-12, commit 48ecb60d)

The optimal condition number at every fourth moment kappa > 1, for finite
and countable mixtures and their perturbations in total variation, with
the properties of its curve.

## phase10 (2026-10-09, commit eda8a065)

The robustness of the optimal condition number and a finite tensorization
constant for the latent-sign law, with reusable identities and the
corrections of the review of the phase 9 release.

## phase9 (2026-10-09, commit e4c46e12)

Four complements of the extensions of phase 8: robustness in total
variation, the tensorization bounds of the latent-sign law, the continuous
latent mixture and the endpoint expansions of the condition-number curve,
with the follow-ups of the review of the phase 8 release.

## phase8 (2026-10-09, commit a89ed1e6)

The three extensions of the mixture theorem: countable mixtures, the
optimal condition number at fourth moment 3, and the scope of the
latent-sign law.

## phase7 (2026-10-09, commit 7d0677c0)

The corollary for the latent-sign law, hardened checks and two generalized
library results.

## phase6 (2026-10-09, commit c3e555eb)

Exact fitting for finite mixtures of product laws and for the paired law.

## phase5 (2026-10-08, commit 112d6a20)

The universality theorem of Koehler and Sohn, completed by the satisfiable
phase.

## stage2 (2026-10-08, commit 1a217b5a)

Stage 2 of phase 5: the Gaussian model and the unsatisfiable phase for
every fourth moment.

## stage1 (2026-10-08, commit 17155b72)

Stage 1 of phase 5: the unsatisfiable phase at fourth moment 3.

## phase4 (2026-10-07, commit d3bb5fb4)

Fourier analysis, the Brascamp-Lieb inequality and the vector small-ball
estimate of Koehler and Sohn.

## phase1 (2026-10-05, commit 38158433)

The proof without the modules and declarations that the main theorem does
not use: 632 modules and 102,415 lines in `theories/`.
