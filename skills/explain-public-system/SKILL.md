---
name: explain-public-system
description: Explain this public mathematical research system to a lay reader, mathematician, formaliser, compute contributor, reviewer, or infrastructure contributor from clone-local evidence.
---

# Explain the public system

Use this skill when a reader asks what the repository is, how it works, what it
has proved, or how they can take part. Work only from tracked public files.
Never infer private state or turn an agent summary into proof authority.

## Build the explanation from the clone

1. Read `README.md` and `HUMAN_ENTRY.md` for the public promise.
2. Run the complete bounded overview:

   ```sh
   python3 scripts/query_corpus.py --overview --format card
   python3 scripts/query_corpus.py --papers
   ```

3. Read `docs/RESULTS.md` and the problem or paper handles relevant to the
   reader's question. Use `python3 scripts/query_corpus.py --ask "..."` for a
   narrower route. For a whole-system explanation, read the three companion
   papers below; for a bounded question, read only the papers and exact
   sections named by the corpus route.
4. Read `METHODOLOGY.md` before explaining proof status, and
   `CONTRIBUTING.md` before explaining participation or credit.
5. Use the companion papers when the reader wants depth:
   - `claim-faithful-publication-systems-paper.pdf` for claims and publication;
   - `cold-clone-to-proof-receipt.pdf` for navigation and verification;
   - `open-source-mathematics-strategy.pdf` for the open-source strategy.

The agent performs this reading on the reader's behalf. Do not make prior
knowledge of the repository, Lean, Git, or the paper set a condition of entry.
Expose the exact source, paper section, declaration, or contributor route
behind each important statement so that the reader can inspect as much or as
little of the evidence as they want.

## Match the reader

For a lay reader, define Lean, a formal statement, a problem frontier, and a
pull request in ordinary English. Lead with one concrete journey through a
problem rather than a file inventory.

For a mathematician, lead with the exact endpoint, strongest unconditional
results, no-go results, cited literature, and remaining mathematical cut.

For a formaliser, bind informal claims to declarations, assumptions, source
coordinates, and the pinned toolchain.

For a compute or agent contributor, show the `mine-open-problem` route, its
stop condition, and the return path. Explain that useful output includes a
counterexample, exact computation, corrected statement, reproducible failed
route, or tooling improvement.

For somebody asking how sustained work operates, show
`run-coupled-research-goals`. Explain the discovery goal and stewardship goal
in ordinary language, how a stable delta wakes the second role, and why proof
status, mathematical appraisal, paper prominence, and the next allocation of
effort remain separate decisions.

For an infrastructure contributor, show the architecture proposal route and
the distinction between improving the conversion machinery and advancing a
mathematical claim.

## Required shape

Answer four questions:

1. What is this repository trying to test?
2. What mathematical and technical objects are already here?
3. What can this reader do next, using one exact command or file?
4. What does that action not establish?

End with one copyable natural-language prompt appropriate to the reader, for
example: “Explain this repository to me as a mathematician and show me the
strongest result and exact remaining boundary,” or “Run one coupled research
cycle on a bounded frontier and return the evidence, consumer dispositions,
and next question.” The prompt is an entry convenience, not a new authority
surface.

Keep the authority order explicit: Lean checks the exact proposition in the
source; the claim registry controls the public description; papers explain;
external experts and mathematical communities decide broader acceptance over
time. Read the current problem count and status from
`python3 scripts/query_corpus.py --overview --format card`; do not freeze the
roster in this skill.
