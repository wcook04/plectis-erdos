# Erdős #257: actual upper-successor counterexample endpoint

This package exposes the strongest source-current realized-run producer in the
half-value programme. It keeps the actual integer greedy remainder, an upper
transition of the concrete seam word, the literal finite right-run recurrence,
and the immediate-successor lower envelope.

Two declarations are selected. The first proves that the complete terminal
packet lower bound is exactly equivalent to the pulse-free successor lower
bound. The second proves that this successor condition produces an infinite
support whose reciprocal-Mersenne value is exactly `1/2`, and hence refutes
the universal irrationality assertion in Erdős Problem 257.

The result is conditional. No successor lower envelope is constructed, no
unconditional half-value representation is claimed, and the parent problem
remains open.

## Exact source and paper route

The source declarations are:

- `ErdosProblems.Erdos257.seamActualUpperRightPacketLinearEscape_iff_successorLinearEscape`;
- `ErdosProblems.Erdos257.half_mem_mersenneAchievementSet_of_actualUpperSuccessorLinearEscape`;
- `ErdosProblems.Erdos257.exists_rational_half_counterexample_of_actualUpperSuccessorLinearEscape`;
- `ErdosProblems.Erdos257.not_universal_of_actualUpperSuccessorLinearEscape`;
- `ErdosProblems.Erdos257.actualUpperSuccessorLinearEscape_completeCounterexample`.

The packet will route to theorem `res:actual-upper-successor` in
`paper/erdos-257-mersenne-support-subseries.tex`; the private staging paper is
`ErdosProblems/papers/erdos-257-mersenne-support-subseries.tex` and its public
base patch is `ErdosProblems/papers/erdos-257-mersenne-support-subseries.patch`.

## Comparator and Palomar boundary

`Challenge.lean` imports only Mathlib and spells out the integer greedy word,
the realized transition/run hypothesis, and both selected conclusions.
`Solution.lean` transports the exact source-current declarations. The negative
configuration adds a `True` premise to the composite endpoint and must be
rejected by a supported Comparator replay.

The Plectis Signal is 95: summit-band editorial reading priority,
not proof authority, novelty certification, Comparator acceptance, Palomar
acceptance, or submission authorization. The score remains provisional until
the comparison set or theorem strength changes. The focused
source/Challenge/Solution/negative/axiom validation is green and the paper and
portfolio routes are synchronized. This package is an intended Palomar
candidate; public immutable identity and terminal Comparator/NanoDa receipts
remain before submission readiness. The supported macOS replay entrypoint
returns typed exit 75 because `systemd-run` is unavailable; that host boundary
is not a positive or negative Comparator verdict.
