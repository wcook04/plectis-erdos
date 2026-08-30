<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Papers

For the repository layout, sources of truth, build path, and release
infrastructure, start with the plain-language
[`ARCHITECTURE.md`](../ARCHITECTURE.md) at the repository root. The files in
this directory are authored papers with narrower jobs.

Each covered Erdős problem has its own canonical short problem note. Problems
#249 and #257 also have longer working-record papers, and
`erdos249-257-main-paper.tex` is retained as an archived joint record of those
two lanes. The joint record is legacy provenance, not an active gateway or the
canonical exposition route; readers should begin with the individual note for
the problem they are asking about.

Every formal statement links to the exact source
line on GitHub, pinned to the formal-source checkpoint named in
`docs/claims.json`, so a reader can go from a sentence of prose to the checked
proof in one click. The visible link text is theorem-specific: important
anchors use short authored mathematical labels, while the default links turn
the exact declaration name into a spaced, lower-case phrase. The file, line,
and declaration remain in each link target and are verified against the
released source by `scripts/check_release.py`. The document adds no mathematics
beyond what the Lean sources contain; the proofs are the sources it links to.

The manuscript layer (this `.tex` and the rendered PDF) is licensed CC-BY-4.0;
see `REUSE.toml` at the repository root.

The joint exposition is preserved for provenance and historical context, but
it is not a current integration gateway, canonical exposition authority, or
default mathematical recommendation. The eight individual problem notes are
the canonical paper layer. The #249 and #257 notes repeat the context, exact
status boundary, negative results, and surviving producers needed by a reader
who arrives through one problem; the other six notes are likewise standalone
routes and should not be assembled through the archived joint record.

## Erdős Problem Notes

The eight standalone notes

- `erdos-249-binary-totient-series.tex`
- `erdos-257-mersenne-support-subseries.tex`
- `erdos-68-factorial-denominator-irrationality.tex`
- `erdos-243-reciprocal-tail-rigidity.tex`
- `erdos-251-prime-gap-dyadic-series.tex`
- `erdos-269-three-prime-running-lcm.tex`
- `erdos-1041-lemniscate-newton-flow.tex`
- `erdos-1049-rational-base-lambert.tex`

are the problem-owned series. One note owns one Erdős problem, and each covers
the modules for that problem in the `ErdosProblems` expansion library.  The
#249 and #257 notes additionally point back to the reviewed gateway spine while
keeping the newer research interfaces explicitly unpromoted. A reader who
arrives at a single problem gets its statement, its checked results, its
negative results, and its surviving obligation without assembling them from the
gateway; deliberate repetition of shared context across notes is the design.

### Returning from a problem note to checked evidence

The notes are exposition, not proof authority.  To return from any note to the
machine-owned problem record, run the matching route below.  Each problem route
returns its exact paper/source record, checked module inventory, and open
obligation handles; the [complete eight-problem source map](../docs/SOURCE_MAP.md#complete-eight-problem-return-matrix)
keeps the same joins readable.  For a source-fingerprinted continuation packet,
use the route-memory command in the last column.

| Problem | Public problem route | Resumable route-memory handoff |
|---|---|---|
| #68 | `python3 scripts/query_corpus.py --route erdos_68` | `python3 scripts/query_route_memory.py --problem 68` |
| #243 | `python3 scripts/query_corpus.py --route erdos_243` | `python3 scripts/query_route_memory.py --problem 243` |
| #249 | `python3 scripts/query_corpus.py --route erdos_249` | `python3 scripts/query_route_memory.py --problem 249` |
| #251 | `python3 scripts/query_corpus.py --route erdos_251` | `python3 scripts/query_route_memory.py --problem 251` |
| #257 | `python3 scripts/query_corpus.py --route erdos_257` | `python3 scripts/query_route_memory.py --problem 257` |
| #269 | `python3 scripts/query_corpus.py --route erdos_269` | `python3 scripts/query_route_memory.py --problem 269` |
| #1041 | `python3 scripts/query_corpus.py --route erdos_1041` | `python3 scripts/query_route_memory.py --problem 1041` |
| #1049 | `python3 scripts/query_corpus.py --route erdos_1049` | `python3 scripts/query_route_memory.py --problem 1049` |

## Full Reasoning Records

Two additional papers retain the complete working context for the original
reviewed problem lanes:

- `erdos249-totient-reasoning-surface.tex`
- `erdos257-mersenne-reasoning-surface.tex`

They are separate rendered papers, not hidden source appendices and not
substitutes for the shorter problem notes. Each records checked premises,
finite evidence, failed and equivalent routes, and the obligations that remain.

These working records are not the canonical paper layer or an active gateway.
Declarations not selected as reviewed public claims live in a different
library; selected interfaces are registered in `docs/claims.json`, while the
Lean files remain their source authority. Kernel checking `ErdosProblems.lean`
does not promote an unregistered declaration into a reviewed claim. The
individual notes may restate reviewed claims, but their exact authority stays
in the registry. Every note states this, and the registry records it as
`publication_architecture.problem_series_boundary`.

The notes share `problem-note-preamble.tex`, which fixes the house macros and
the one pinned source revision every link resolves against. Links are validated
against that pinned commit rather than the working tree, so a note cannot decay
when a later wave moves declarations:

```sh
python3 ../scripts/check_problem_note_sources.py --coverage
```

Pinning buys safety at a price: a note whose links can never break can instead
fall silently behind. `--coverage` is the meter for that. It reports, per
problem, the fraction of the declarations that exist **now** which the note
actually links, and whether the modules have changed since the pin, and it
fails below `note_coverage_floor` in `docs/problem_index_source.json`. Drift is
therefore a failing check with a worklist attached, not something a reader
discovers.

When a note falls through the floor: rewrite it against the current source,
repin `\commit` in the shared preamble to a commit that is **pushed** (links
resolve on GitHub, so an unpushed local merge is not a valid pin), rebuild, and
refresh the digests in `docs/publication_contract.json`.

`docs/problems.json`, built by `scripts/build_problem_index.py`, is the
machine-readable index over the same material: one row per problem naming its
modules, its note, what is checked, what is not, and the obligation that
survives.

To add a note, write the `.tex`, add its stem to `PAPERS` and `NOTES` in the
`Makefile`, register it once in `docs/publication_contract.json` with class
`problem_note`, add its rendered PDF to the CC-BY override in `REUSE.toml`, add
its row to `publication_architecture.problem_series` in `docs/claims.json`, and
add its problem to `docs/problem_index_source.json`. The contract checker fails
if any of those five are missing.

`claim-faithful-publication-systems-paper.tex` is the printable architecture
and access guide. It names the real source files, reviewed records, generated
views, release commands, CI jobs, and human trust boundary, then follows one
claim from Lean proof to public page. The historical checker example appears
only after the architecture and illustrates its coverage limit; it is not a
score and adds no mathematical result.

That architecture paper remains a maintained draft. Its revision target and
cold-reader loop are recorded in
`claim-faithful-publication-systems-revision-brief.md`.

`cold-clone-to-proof-receipt.tex` is the agent-native navigation and
incremental-validation guide. It explains how a fresh checkout exposes the
whole mathematical option surface without compiling Lean, how an inhabiting
agent crosses from advisory navigation into a kernel-authored receipt, and how
focused builds and exact cache receipts avoid repeating unchanged work. Its
dogfood session is evidence of acceptance and replay, not a proof of optimal
reasoning or external novelty.

## Build

```sh
# with tectonic (recommended; fetches TeX packages on first run)
tectonic erdos249-257-main-paper.tex

# or with a TeX Live install
pdflatex erdos249-257-main-paper.tex && pdflatex erdos249-257-main-paper.tex

# or
make
```

The outputs include every stem in `PAPERS`: the three repository-level papers,
the two full reasoning records, and all eight problem notes. `make` also
synchronises every tracked reader-facing PDF to the repository root.

## Contents

The bullets below index the archived joint record for historical navigation;
the canonical reader route is the individual problem note for the question at
hand. The systems paper is outlined by its description above.

- The Mersenne–Lambert ladder that places both constants on one line.
- The [composite-dilation defect](../Erdos249257/CompositeDilationDefect.lean):
  an exact foreign-divisor correction, zero on prime support, with no arbitrary-
  support tail bound or irrationality conclusion.
- Erdős–Borwein-type irrationality (the #257 direction): full support at every base, plus named infinite-support cases.
- The totient constant `S` (Erdős #249): the unconditional denominator bound, the coprimality reading, and the exact reduction to finite certificates.
- Formalisation architecture and mathematical lessons: how infinite questions are separated from finite kernel-checkable witnesses.
- The formalisation method: how checked statements, finite computations, exact reductions, and the unresolved steps in Erdős #249 and #257 are kept distinct.
- Artefact availability, verification, and a conclusion stating the exact open boundaries once.
- Auxiliary binary-carry criteria and the compact declaration map in appendices.
- The sublogarithmic zero-window theorem for divisor coverage forced by a hypothetical rational support value.
