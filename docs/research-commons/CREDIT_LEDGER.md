<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Credit ledger

_Generated from the authored source registry by `scripts/build_source_attributions.py`; do not hand-edit._

People have told us things about this work that changed it. Each entry says what they told us, what changed because of it, and where to see the change. A name appears only after that person confirms they want to be named; until then the entry says the name is withheld. Thanking someone here does not mean they reviewed, checked or endorsed the mathematics.

Entries: `5`. Names withheld until confirmed: `5`. Named with permission: `0`. Anonymous at their request: `0`.

Published papers, forum posts and software are credited in [source attributions](SOURCE_ATTRIBUTIONS.md), and the [credit policy](CREDIT_POLICY.md) explains how credit works here. If an entry is about your advice and you would like to be named, to stay anonymous, or to correct the entry, [get in touch](https://wcook04.github.io/plectis/docs/contact.html#get-in-touch).

<a id="credit-correspondence-004"></a>

## 17 September 2026: Writing for a first-time reader

- **What they told us:** A mathematician said the #243 note used names that meant nothing on a first or second reading, defined notation it used once, and never said how restrictive its main hypothesis was.
- **What changed:** All sixteen problem papers were rewritten for a first-time reader, naming standard tools and saying how restrictive each hypothesis is, and the public writing rules now require it.
- **Where to see it:** [paper/243/erdos-243-reciprocal-tail-rigidity.tex, line 605](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L605-L605); [paper/243/erdos-243-reciprocal-tail-rigidity.tex, lines 713–735](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L713-L735); [skills/public-mathematical-writing/SKILL.md, lines 204–215](../../skills/public-mathematical-writing/SKILL.md?plain=1#L204-L215); [docs/papers/SHORT\_PAPER\_CONTRACT.md, line 15](../../docs/papers/SHORT_PAPER_CONTRACT.md?plain=1#L15-L15); [docs/papers/SHORT\_PAPER\_CONTRACT.md, line 23](../../docs/papers/SHORT_PAPER_CONTRACT.md?plain=1#L23-L23)
- **Problems:** #68, #243, #249, #251, #257, #269, #1041, #1049
- **Name:** withheld until they confirm (credited as a mathematician).
- **Full record:** [source attributions](SOURCE_ATTRIBUTIONS.md#source-correspondence-004)

<a id="credit-correspondence-005"></a>

## 15 September 2026: Showing where methods and ideas come from

- **What they told us:** A mathematician said the trouble with AI-assisted mathematics is that it rarely shows where its methods and ideas come from.
- **What changed:** A literature review was run for each of the eight problems, and each paper now credits its sources at the point where they are used.
- **Where to see it:** [paper/251/erdos-251-prime-gap-dyadic-series.tex, lines 70–75](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L70-L75); [docs/papers/SHORT\_PAPER\_CONTRACT.md, line 19](../../docs/papers/SHORT_PAPER_CONTRACT.md?plain=1#L19-L19)
- **Commits:** [029c90d414](https://github.com/wcook04/plectis-erdos/commit/029c90d4144d6087ba62d08ffc8b3cee1a9a165e), [7148c5ae4a](https://github.com/wcook04/plectis-erdos/commit/7148c5ae4a4a2f3802cccdeed62c394f64593340)
- **Problems:** #68, #243, #249, #251, #257, #269, #1041, #1049
- **Name:** withheld until they confirm (credited as a mathematician).
- **Full record:** [source attributions](SOURCE_ATTRIBUTIONS.md#source-correspondence-005)

<a id="credit-correspondence-002"></a>

## 6 August 2026: Leading the #249 paper with its exact theorem

- **What they told us:** A mathematician advised leading the #249 paper with its exact finite-level theorem, explaining the mechanism behind it, and comparing it precisely with the existing literature on regular sequences.
- **What changed:** The #249 paper now opens with the exact rank and basis, compares the result with work of Allouche and Shallit, Coons and Martin, and links a minimal Lean entry; the irrationality question stays open.
- **Where to see it:** [paper/249/erdos-249-binary-totient-series.tex, lines 22–24](../../paper/249/erdos-249-binary-totient-series.tex#L22-L24); [paper/249/erdos-249-binary-totient-series.tex, line 78](../../paper/249/erdos-249-binary-totient-series.tex#L78-L78); [paper/249/erdos-249-binary-totient-series.tex, line 77](../../paper/249/erdos-249-binary-totient-series.tex#L77-L77); [lean/Erdos249257/TotientMahlerDefect.lean, lines 935–1145](../../lean/Erdos249257/TotientMahlerDefect.lean#L935-L1145); [formalization.yaml, lines 159–216](../../formalization.yaml#L159-L216); [docs/EXTERNAL\_VERIFICATION.md, lines 534–544](../../docs/EXTERNAL_VERIFICATION.md?plain=1#L534-L544)
- **Problems:** #249
- **Name:** withheld until they confirm (credited as a mathematician).
- **Full record:** [source attributions](SOURCE_ATTRIBUTIONS.md#source-correspondence-002)

<a id="credit-correspondence-001"></a>

## 6 August 2026: Listing each checked result, with a cheap way to check it

- **What they told us:** A mathematician advised listing each selected result with its exact statement, proof source, novelty status, axioms and limits, and giving reviewers a cheap way to check the statements themselves.
- **What changed:** formalization.yaml now lists the selected results this way, and Comparator checks them against separately written statements, including an altered statement that must be rejected.
- **Where to see it:** [formalization.yaml, lines 1–60](../../formalization.yaml#L1-L60); [verification/comparator.json, lines 1–40](../../verification/comparator.json#L1-L40); [verification/comparator-negative-mismatch.json, lines 1–13](../../verification/comparator-negative-mismatch.json#L1-L13); [docs/EXTERNAL\_VERIFICATION.md, lines 4–14](../../docs/EXTERNAL_VERIFICATION.md?plain=1#L4-L14)
- **Commits:** [e062d93809](https://github.com/wcook04/plectis-erdos/commit/e062d93809b6a394a067b4ea1bbdac7b228e0510)
- **Problems:** #68, #243, #249, #251, #257, #269, #1041, #1049
- **Name:** withheld until they confirm (credited as a mathematician).
- **Full record:** [source attributions](SOURCE_ATTRIBUTIONS.md#source-correspondence-001)

<a id="credit-correspondence-003"></a>

## 5 August 2026: Earlier work on the #1049 Lambert value

- **What they told us:** A mathematician suggested comparing the #1049 construction with an earlier irrationality paper.
- **What changed:** The comparison was carried out: a source note and a Lean module recording where the two methods part are public, and the #1049 record cites the paper where they meet.
- **Where to see it:** [docs/primary-sources/reciprocal-tail/amdeberhan-zeilberger-1998-q-apery-source-closure.md, lines 1–41](../../docs/primary-sources/reciprocal-tail/amdeberhan-zeilberger-1998-q-apery-source-closure.md?plain=1#L1-L41); [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex, line 869](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L869-L869); [docs/PRIOR\_ART.md, lines 389–393](../../docs/PRIOR_ART.md?plain=1#L389-L393); [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean, lines 1–100](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L1-L100)
- **Commits:** [f5342c683a](https://github.com/wcook04/plectis-erdos/commit/f5342c683a321f752b6994423e1e9ec40979809f)
- **Problems:** #1049
- **Name:** withheld until they confirm (credited as a mathematician).
- **Full record:** [source attributions](SOURCE_ATTRIBUTIONS.md#source-correspondence-003)

Machine-readable version: [credit-ledger.json](credit-ledger.json).
