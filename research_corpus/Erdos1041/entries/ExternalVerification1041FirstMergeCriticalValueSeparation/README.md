# Erdős #1041 first-merge critical-value separation

This Comparator package exposes the exact Lean-checked numerical kernel of the
paper's first-merge critical-value separation theorem.  It consolidates the
source family into two endpoints:

1. the three all-degree regimes
   `S = 4, n >= 3`, `S = 3, n >= 4`, and `S = 2, n >= 6`, each cutoff being
   the first degree at which its inequality holds;
2. the general implication from the squared analytic connector estimate to
   strict length below two, with no sign hypothesis on the connector.

The source authority is
`ErdosProblems/Erdos1041/FirstMergeCriticalValueSeparation.lean`.  The
Mathlib-only challenge deliberately does **not** encode the paper's ordinary
covering-space continuation, univalence, area formula, or Pólya
area-capacity inequality.  Erdős #1041 remains open in the near-tie,
multiple-saddle, and unrestricted regimes.

## Exact paper routes

The application-ready paper revision is
`ErdosProblems/papers/erdos-1041-critical-value-separation.patch`.  The exact
reader-facing anchors are:

| Comparator declaration | Paper treatment | Exact boundary |
|---|---|---|
| `firstMerge_exact_convenient_thresholds` | `res:critical-value-thresholds` | `bdry:critical-value-separation` |
| `firstMerge_length_lt_two_of_squared_bound` | `res:critical-value-separation` (equations (4)--(5)) | `bdry:critical-value-separation` |

These routes are staging routes until the patch is promoted to the
authoritative public paper.  Comparator is semantic-parity assurance, not
proof authority or novelty authority.

`Challenge.lean` contains exactly two intended specification `sorry`s.  The
deliberate negative omits the threshold endpoint, so it must be rejected as an
incomplete solution.  Focused source/challenge/solution/deliberate-negative and
axiom-audit builds pass; both selected declarations use exactly `propext`,
`Quot.sound`, and `Classical.choice`.  Terminal Comparator/NanoDa,
public-identity, and paper-promotion receipts remain pending until recorded
explicitly.
