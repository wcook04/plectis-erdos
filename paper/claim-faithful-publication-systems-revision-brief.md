<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Revision brief: Lean publication-systems paper

The current twelve-page paper is an architecture note with one bounded case
study. Its useful feature is its order: it gives the reader a plain mental
model before implementation details, and one worked example (the finite
theorem, the open requirement, and the proved equivalence between the open
requirement and irrationality) carries every section. Future revisions should
keep that order and that recurrence while testing whether the paper actually
earns every page.

## Reader and decision

Write for a technically competent outsider who has never used Lean, has not
read this repository, and does not know its history. By the end, that reader
should be able to explain:

1. what Lean checks;
2. what a mathematician still has to judge;
3. how a reviewed public claim is connected to formal source;
4. what the release checks repeat;
5. what a passing release does not establish; and
6. where to inspect one complete example.

The paper's purpose is trust calibration, not exhaustive documentation.
Use ordinary mathematical and software language for that calibration. Give a
reader the public meaning before a claim identifier, declaration name, file
path, or repository-specific status label, and omit internal workflow
vocabulary that the argument does not need.

## Distinct job from `docs/ARCHITECTURE.md`

- `docs/ARCHITECTURE.md` is the living route map: current files, commands,
  ownership, regeneration, and maintenance.
- The PDF is the stable explanation: why authority is divided, how one claim
  crosses the boundary, and where the guarantee ends.

They should agree without becoming two independently exhaustive manuals.

## Cold-reader loop

Use simulated and human readers to find high-level failures, then revise by
the governing purpose rather than mechanically accepting sentence edits.
For each reading, record:

- the first point where the reader can explain the system back;
- the first claim they do not believe and why;
- any concept introduced before its purpose is clear;
- what they think the paper is trying to contribute;
- what they believe the checks prove;
- what they still cannot locate after reading; and
- what they would remove first.

The paper remains under a twelve-page ceiling, matching the 52,000-byte
source budget in `scripts/check_architecture_guide.py` (raised from 40,000 by
maintainer decision, July 2026, to admit the example-instantiated assurance,
coverage, and reuse material, then the cold-reader repairs and the
perimeter-contraction material). Prefer removing duplication,
making one worked example more concrete, and clarifying authority over adding
terminology, counts, scripts, or new claims of importance. A revision is not
ready merely because the TeX compiles: render every page, inspect the diagram
and tables at reading size, and leave no clipping, overlap, or layout warning.
