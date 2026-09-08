# A finite denominator exclusion

For the literal series sum over n>=2 of 1/(n!-1), every representation a/q with integer a and positive natural q satisfies q >= 2^39990 and q > 10^12040. Reducedness is unnecessary. The Challenge imports only Mathlib and assumes only that representation; no interval validity predicate or numerical certificate is a hypothesis. The Solution projects the two transparent numerical bounds from the audited concrete certificate.

This is one finite exclusion, not irrationality, transcendence, or the separate factorial-divisibility exclusion. The source compiled with a bounded 64 MiB Lean thread stack and its endpoint axiom audit is clean. Wrapper elaboration, wrapper audit, and supported-runner Comparator replay remain pending. No submission has occurred; novelty is unassessed.
