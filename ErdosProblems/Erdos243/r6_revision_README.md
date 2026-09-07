# Erdős #243: round-six revision and research packet

7 September 2026. The live input is the supplied `01_short_note.tex`, not an older PDF or an alternative manuscript. The title **Excluding the Bounded Negative Part**, the six-hypothesis flagship, the original-coordinate corollary, and the original main proof body are retained verbatim.

## The idea worth remembering

A positive integer orbit can fail to be monotone without defeating a height argument. Charge each height only at its first crossing. Fresh records supply pairwise-coprime old multipliers, and divisibility prevents a short jump across the corresponding CRT block. An overlap record need not be forbidden: its raw error already pays for its new height. This yields a weighted height theorem without centring. Conversely, when numerator coefficients are adjustable, a congruence can be solved by an arbitrarily large prime and the coefficient absorbs the quotient. That construction realises arbitrarily slowly unbounded errors in an actual positive rational series. The surviving distinction is the exact quotient-one constraint of unit fractions, not merely congruence, freshness, or rational-tail realisability.

## What is new in this return

`01_research_note.md` contains complete ordinary proofs of two candidates: a centring-free mixed/raw weighted record theorem for integral coefficients, and an adaptive Dirichlet construction of positive reduced rational terms with prime denominators, primitive fresh states, normalised vanishing, weighted critical rate, and negative error below any prescribed unbounded envelope. It also contains exact examples separating raw error from actual jump, showing the need for a nonintegrable weight, and showing the need for monotonicity of that weight.

These candidates are not independently refereed, Lean checked, or established as new against the full literature. They do not supply a new unconditional unit-fraction endpoint or solve Erdős #243. The r5 coefficient bounded-height result and the canonical weighted criterion are already admitted and are not claimed again as new progress.

## The files

- `01_research_note.md`: proofs, quantitative inequalities, constructions, scope and remaining questions.
- `02_failure_map.md`: which observables survive each counterexample, and what stronger information is needed.
- `03_editorial_route.md`: the reading route, exact edits, retained consequences, and companion migration.
- `04_long_record_and_source_notes.md`: source-current versus stale assertions, and exact formal boundaries.
- `05_sibling_notes.md`: live-paper-specific recommendations and genuine common mechanisms across the other seven notes.
- `06_references_and_assurance.md`: primary references, searches, verification record and limitations.
- `patches/edits.json`, `patches/short_note.patch`, `patches/apply_edits.py`: eighteen exact replacements against the input hash, with replay and output verification.
- `migrations/`: the original cut text, unchanged, and a map accounting for all 68 input labels. These are integration fragments, not a competing companion manuscript.
- `lean/UncentredRecordCharge.lean`: uncompiled finite candidate lemmas, including composition of the existing CRT cover and existing coefficient fence. No global weighted or Dirichlet theorem is labelled formalised.
- `checks/check_r6.py`, `checks/r6_receipt.json`: executed exact finite checks and their receipt.
- `short_note_preview.pdf`: the nine-page result of applying the edits with the supplied house support. The original PDF is 31 pages. The original-variable theorem is on page one; the complete flagship and its unchanged main proof are on page two.

## Apply and check

From this folder, with the supplied input available at a chosen path:

```sh
python patches/apply_edits.py --input /path/to/01_short_note.tex --output /path/to/revised_note.tex
python checks/check_r6.py
```

The edit program refuses a different source hash, an ambiguous replacement, an altered flagship, or an in-place overwrite. The generated TEX is intended for the existing repository build. No alternate whole-note TEX is shipped.

Integrate and reconcile the migrated fragments in the companion before publishing the short/long split. The supplied long assembly is not source-current at several named claims. Also update the release pin for newer scalar and finite modules: their presence in the ZIP is not evidence that the older public commit contains them.

No repository changes, Lean build, Comparator run, or Palomar submission were performed. The ordinary proofs and the exact finite checks have different evidential roles.
