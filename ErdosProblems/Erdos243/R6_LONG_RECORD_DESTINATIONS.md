# Erdős #243 — r6 long-record destinations (by label)

This is a destination map for the r6 short/long split. Frozen R
`public-source-redacted://release-final-20260905` was not
mutated. There is still no live `02_long_record.tex` under
`ErdosProblems/papers/`. Cut text lives as companions in this directory.

Live short note after the 18 exact edits:
`ErdosProblems/papers/erdos-243-reciprocal-tail-rigidity.tex`
(sha256 `f567a4aa6a20689e8214c373218e909c182d6e405566ddb62daefafe08f6b2a2`).
Title **Excluding the Bounded Negative Part**, `res:bounded`,
`res:originalbounded`, and the original main proof body are unchanged.

The new uncentred mixed/raw weighted-record theorem and the exact
rational-series construction are **not** in the short-note opening. They
remain ordinary companions: `UncentredRecordCharge.md`.

## Short-note anchors after the r6 labelled edits

| Label | Present in live short note | Destination |
|---|---|---|
| `res:bounded`, `res:originalbounded` | yes | keep |
| `sec:state`, `sec:defect`, `sec:descent`, `sec:barrier` | yes | keep required lemmas |
| `sec:transfer` | yes (new section id from E06) | keep ordinary canonical-tail proof |
| `sec:mass`, `res:mass`, `res:massscalar` | yes (aliased) | keep strongest scalar form |
| `sec:lcmrecords`, `res:weightedrecord`, `res:lcmbounded` | yes | keep; do not insert uncentred theorem |
| `res:cubicrate`, `sec:secondaryrate` | yes | compact secondary |
| `sec:open`, `res:frontier` | yes | keep `∃B: liminf F_B(X)/X=0` |
| `ex:sylvester`, `res:scale`, `ex:defect` | no | `r6_migrations/algebra_and_examples.tex` |
| `ex:crt`, `ex:reduced`, `res:gcdsparse` | no | `r6_migrations/reduced_tail_details.tex` |
| `ex:mass` | no | `r6_migrations/scalar_mass_versions.tex` |
| `res:excursions`, `eq:repair-entropy`, `res:lcmheight`, `res:prefixgcd`, `res:masshyp`, `res:variablerise` | no | `r6_migrations/frontier_and_formal_details.tex` |
| `sec:constant` … `app:residue` (appendices) | no | `r6_migrations/short_note_appendices.tex` |
| Formal Conjectures bibitem | no | `r6_migrations/formal_conjectures_reference.tex` |

Exact 68-label accounting: `r6_migrations/label_map.md`.
Source-current vs stale assertions: `r6_long_record_and_source_notes.md`.
Failure map: `r6_failure_map.md`. Packet README: `r6_revision_README.md`.

## Companion repairs still owed on any later long assembly

Same keyed repairs as `LONG_RECORD_DESTINATIONS.md` (r5): cubic exceptional
density per profile, mod-7 phases, shifted-sign trichotomy, demoted global
amplified/energy iff, integer covering windows, k=1/2 norms, variable-rise
quantifiers `∀ω ∃family ∃walk`. Add the r6 exact coefficient-series
realisation only as a companion with its non-unit and scale limitations.

## Not done this wave

No frozen-R mutation. No competing manuscript paste. No barrel import.
No Lean compile (parent serial fan-in). No Palomar POST.
