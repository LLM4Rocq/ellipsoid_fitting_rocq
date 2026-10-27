# Documents

This folder holds the longer documents of the project. The short overview is
the [README.md](../README.md) at the root, and the guide for contributors and
AI coding agents is [AGENTS.md](../AGENTS.md).

| Document | What it is |
|---|---|
| [details.md](details.md) | The long README of the repository at commit 5893184e, kept as a record: each result with its phase and acceptance commit, the description of each check, the provenance of the proof and the open work. Its header says what changed, what is out of date and which of the records it cites are not public. |
| [history/agent-rules.md](history/agent-rules.md) | The rules given to the AI agents who worked on the repository, phase by phase, as they stood at commit 5893184e. [AGENTS.md](../AGENTS.md) says which of them still apply, and takes precedence over them. |
| [shifted-gaussian.tex](shifted-gaussian.tex), with [statements.bib](statements.bib) | The note *Centered ellipsoid fitting for non-centered Gaussian data*: the informal proof of the seven theorems on translated samples, S1 to S7. Its Appendix A names the statement and the theorem of each result and records where the formal proof departs from the text. |
| [formal_proof.tex](formal_proof.tex) | *The ellipsoid fitting transition at n = d^2/4: the proof as formalized*: the proof of the Gaussian theorem along the route of the formal proof, with the formal name of each result. Written on 6 October 2026 and not updated since. |
| [paper_correspondence.md](paper_correspondence.md) | A comparison, result by result, of the formal proof in `theories/` with the proof of Misiakiewicz and Wen, made at commit 3736fa2. Written on 6 October 2026 and not updated since. |

Git does not track PDFs. When a PDF is released, it is attached to a GitHub
release of this repository, whose notes give the commit of its sources and the
SHA-256 of the PDF. The GitHub release of `shifted-docs`, the documentation
release of 27 October 2026, has the PDF of the note `shifted-gaussian.tex`.

Commit messages and tag messages written before the move call these files by
their old names: `README.md` for the long README, now
[details.md](details.md), and `AGENTS.md` for the agents' rules, now
[history/agent-rules.md](history/agent-rules.md).

## Records cited in source comments

Comments in the `.v` files cite the records of the work as it was done. These
citations are in comments only; none is part of a proof.

- "AGENTS.md", most often with a section such as "Phase 12", means the agents'
  rules, now [history/agent-rules.md](history/agent-rules.md). It is cited on
  60 comment lines in 59 files.
- Paths under `reviews/` (11 lines in 10 files) and `notes/` (120 lines in 83
  files) name plans, reviews and audits of the project. They belong to its
  private records and are not in this repository.

Some header comments are dated: `extension/UniversalityStatement.v`, written on
7 October 2026, says that nothing proves its statement yet, while
`extension/UniversalityTheorem.v`, added the next day, proves it. These
comments stay as they are. Under the project's rules, a change to a `.v` file,
even to a comment, needs a full `make check` in the pinned image (see
[AGENTS.md](../AGENTS.md)). Three of the files whose comments cite the records
above are also check files that the checker requires to be byte-identical to a
fixed commit. The public records of the work are [details.md](details.md) and
the commit messages.

## Terms used in the comments and records

- **The user.** The person who directed the work, reviewed and accepted the
  statements, and took the decisions that comments cite.
- **Phase.** The work went in phases. Phases 1 and 4 to 14 each ended with a
  tag, `phase1` and `phase4` to `phase14`; phases 2 and 3 have none, and
  `stage1` and `stage2` mark the first two stages of phase 5. Step 18 merged
  the shifted-Gaussian extension onto phase 14 (tag `shifted`). The rules of
  phases 1 to 3 are in the section "Phases" of
  [history/agent-rules.md](history/agent-rules.md), and those of each later
  phase N in its section "Phase N".
- **Target.** A numbered theorem: T1 to T14 in `applications/` (T8 was
  deferred), S1 to S7 for translated samples.
- **Accepted, frozen.** The user reviewed a statement file and accepted it at a
  commit. From then on it is frozen: the checker compares its code, without
  its comments, with its code at a fixed commit, most often the one at which it
  was accepted.
- **Pinned.** A file that the checker requires to be byte-identical to a fixed
  commit, or to have a fixed SHA-256.
- **Lane, master.** Each of three AI agents (agent 1, 2 and 3) owned a lane: a
  set of files and a branch, `lane/a`, `lane/b` or `lane/c`. The agent who
  coordinated a phase merged the lanes: agent 1 in phases 1 to 5, and agent 3,
  the master, in phases 6 to 14.
- **Hub, VM.** Most of the agents' work was done on a virtual machine, in
  `/srv/ellipsoid-fitting/`, where they shared the git repository `hub.git`.
  Paths under `/srv/` are not public. Since 25 October 2026 the hub is an
  archive, and this GitHub repository is the authoritative one.
