<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Related Erdős problems

This is a map of relationships, not a second status register. For the eight
programmes in this repository, read [results and limits](../RESULTS.md), then
follow [the source map](SOURCE_MAP.md#complete-eight-problem-return-matrix).
[Claim records](../claims.json) own local public status and exact boundaries.
The external catalogue status and the local release status are separate facts.

## Neighbouring questions

| Relationship | What connects the questions | Evidence route |
|---|---|---|
| #69 and #257 | Expanding `ω(n)` by prime divisors connects its binary generating series to the prime-support Mersenne sum. The formalised identity bridge and the cited irrationality theorem are separate evidence. | [Prior art](../PRIOR_ART.md) · `python3 scripts/query_corpus.py --claim prime_support_irrationality` · [#257 results](../RESULTS.md#result-257) |
| #250 and #249 | The Lambert transform of the identity function gives the divisor-sum series; the totient transform is the neighbouring representation. A theorem for one coefficient function does not transfer to the other. | [Prior art](../PRIOR_ART.md) · `python3 scripts/query_corpus.py --claim sigma_transcendence` · [#249 results](../RESULTS.md#result-249) |
| #258 and the divisor-sum programmes | The denominator `a₁···aₙ` gives a related divisor-count series. This is an untouched analogy; this repository does not address #258. | [External problem #258](https://www.erdosproblems.com/258) |
| #68 and the binary-series programmes | Factorial and binary denominators provide different carry coordinates. Shared carry terminology does not identify the endpoint questions or their proof obligations. | [#68 results](../RESULTS.md#result-68) · [source map](SOURCE_MAP.md) |
| #1049 and #257 | Full-support Lambert sums connect the integer-base case with the support-series programme. Rational noninteger bases retain their separate question and hypotheses. | [#1049 results](../RESULTS.md#result-1049) · [#257 results](../RESULTS.md#result-257) |

A solved neighbour, shared transform or formalised special case is not an
advance on another target by analogy alone. Check whether `claims.json::machine_readable_paper.argument_graph`
records an `advances_open_target` edge, then inspect its exact source statement.

## Return to local evidence

Run `python3 scripts/query_corpus.py --route erdos_<n>` for `n` in
`68, 243, 249, 251, 257, 269, 1041, 1049`. The
[complete eight-problem return matrix](SOURCE_MAP.md#complete-eight-problem-return-matrix)
links those routes to papers and Lean modules without repeating their results.
For a recorded obligation, use
`python3 scripts/query_corpus.py --open <remaining_open.id>`. Named lookups include
`python3 scripts/query_corpus.py --open remaining_open.erdos_249_irrationality` and
`python3 scripts/query_corpus.py --open remaining_open.universal_257_all_infinite_supports`.

In particular, [#1041's current result](../RESULTS.md#result-1041) records the
refutation of the exact Formal Conjectures statement; old open geometric
routes do not override that status or settle correspondence with the historical
wording. For [#269](../RESULTS.md#result-269), consult the current claim boundary:
the actual rationality-to-reduced-carry bridge is established separately, while
the source-specific cofinal escape producer remains open.

## July 2026 catalogue snapshot

The earlier version of this page recorded the following external statuses in
July 2026. This is preserved historical evidence, not a fresh observation of
the catalogue today, and does not determine local formal status.

| External page | Status recorded in July 2026 |
|---|---|
| [#68](https://www.erdosproblems.com/68) | open |
| [#249](https://www.erdosproblems.com/249) | open |
| [#257](https://www.erdosproblems.com/257) | open |
| [#1041](https://www.erdosproblems.com/1041) | open |
| [#1049](https://www.erdosproblems.com/1049) | open for rational noninteger bases |
| [#69](https://www.erdosproblems.com/69) | solved, attributed to Tao–Teräväinen |
| [#250](https://www.erdosproblems.com/250) | solved, attributed to Nesterenko 1996 |
| [#258](https://www.erdosproblems.com/258) | solved |
