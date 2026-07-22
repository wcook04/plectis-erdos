<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Papers

For the repository layout, sources of truth, build path, and release
infrastructure, start with the plain-language
[`ARCHITECTURE.md`](../ARCHITECTURE.md) at the repository root. The files in
this directory are authored papers with narrower jobs.

`erdos249-257-main-paper.tex` is the mathematical gateway for readers who do
not read Lean. It states, in ordinary notation, what the Lean development
proves, cites, and leaves open.

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

There is deliberately no specialist companion note for #249 or #257. A former
#249-only note was scrapped and deleted (it survives only in git history)
because a one-sided companion does not give readers a coherent paper set for a
repository about both #249 and #257. Add specialist notes for those two
problems only as a matched pair; otherwise they keep one mathematical gateway
paper between them. That rule is about the balance of the gateway's own
subject and does not govern other problems.

## Erdős Problem Notes

The four short notes

- `erdos-243-reciprocal-tail-rigidity.tex`
- `erdos-251-prime-gap-dyadic-series.tex`
- `erdos-269-three-prime-running-lcm.tex`
- `erdos-1049-rational-base-lambert.tex`

are the problem-owned series. One note owns one Erdős problem, and each covers
the modules for that problem in the `ErdosProblems` expansion library. A reader
who arrives at a single problem gets its statement, its checked results, its
negative results, and its surviving obligation without assembling them from the
gateway; deliberate repetition of shared context across notes is the design.

The series is not a set of companions to the gateway. Its subject is a
different library, whose declarations are exact Lean propositions and are
**not** reviewed public claims: `docs/claims.json` carries no row for them, and
kernel checking `ErdosProblems.lean` does not promote them into one. Every note
states this, and the registry records it as
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

That twelve-page paper is still a draft, not a finished exemplar. Its revision
target and cold-reader loop are recorded in
`claim-faithful-publication-systems-revision-brief.md`.

## Build

```sh
# with tectonic (recommended; fetches TeX packages on first run)
tectonic erdos249-257-main-paper.tex

# or with a TeX Live install
pdflatex erdos249-257-main-paper.tex && pdflatex erdos249-257-main-paper.tex

# or
make
```

The outputs are `erdos249-257-main-paper.pdf` and
`claim-faithful-publication-systems-paper.pdf`; `make` also synchronises the
tracked reader-facing copies at repository root.

## Contents

The bullets below index the mathematical gateway paper; the systems paper is
outlined by its description above.

- The Mersenne–Lambert ladder that places both constants on one line.
- Erdős–Borwein-type irrationality (the #257 direction): full support at every base, plus named infinite-support cases.
- The totient constant `S` (Erdős #249): the unconditional denominator bound, the coprimality reading, and the exact reduction to finite certificates.
- Formalisation architecture and mathematical lessons: how infinite questions are separated from finite kernel-checkable witnesses.
- The formalisation method: how checked statements, finite computations, exact reductions, and the unresolved steps in Erdős #249 and #257 are kept distinct.
- Artefact availability, verification, and a conclusion stating the exact open boundaries once.
- Auxiliary binary-carry criteria and the compact declaration map in appendices.
- The sublogarithmic zero-window theorem for divisor coverage forced by a hypothetical rational support value.
