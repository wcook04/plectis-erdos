<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Documentation guide

The repository separates mathematical explanation, verification records, and
agent instructions. Choose the section that matches what you are trying to do.

## Read the mathematics

1. Start with the root [README](../README.md) for the scope and the eight-paper
   portfolio.
2. Read [Results and open boundaries](RESULTS.md) for a problem-by-problem
   account of what is checked and what remains unresolved.
3. Open the relevant paper from [The papers](papers/README.md). The eight
   problem papers are the main mathematical reading objects; specialist
   companions follow them.
4. Use [Related problems](RELATED_PROBLEMS.md) for the complete portfolio map
   and [Prior art](PRIOR_ART.md) for attribution and antecedents.

The canonical order of mathematical attention is the Palomar ranking in
[`PALOMAR_RESULT_SHOWCASE.json`](PALOMAR_RESULT_SHOWCASE.json). Human pages may
summarise that order but do not maintain a second ranking.

## Verify a claim

- [`claims.json`](claims.json) records public statements, statuses, Lean
  declarations, and exact remaining-open propositions.
- [External verification](EXTERNAL_VERIFICATION.md) presents the configured
  Comparator interfaces and their boundaries.
- [Source map](SOURCE_MAP.md) maps each problem, paper, and result family to
  Lean source.
- [Methodology](../METHODOLOGY.md) explains what Lean acceptance, repository
  checks, and mathematical review do and do not establish.
- [Reproducibility](REPRODUCIBILITY.md) gives the build and release checks.

Lean source checked by the pinned Lean kernel is formal proof authority.
Generated documentation, JSON indices, and papers are navigation or
exposition; they do not strengthen a theorem.

## Work on the repository

Agents and contributors should begin with the root
[`AGENTS.override.md`](../AGENTS.override.md), then use
[Agent workbench](AGENT_WORKBENCH.md) for corpus queries, claim handles, source
navigation, and focused builds. [Architecture](../ARCHITECTURE.md) explains the
repository layout and authority order.

The generated [Corpus orientation](ORIENTATION.md) and its machine source
[`orientation.json`](orientation.json) are technical navigation surfaces. They
are useful after a reader has chosen a problem or claim; they are not the
human introduction to the mathematics.

## Archive and provenance

The eight problem-specific papers listed in the root README are the canonical
public mathematical starting points. The combined
[`claim-faithful-publication-systems-paper.pdf`](../claim-faithful-publication-systems-paper.pdf)
is retained for archive and provenance. The
[`cold-clone-to-proof-receipt.pdf`](../cold-clone-to-proof-receipt.pdf) explains
the verification and navigation system. Neither adds another mathematical
problem or changes the claim registry.
