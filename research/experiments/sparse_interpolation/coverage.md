<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# When added congruences leave gaps

Suppose a step permits the even digits from 0 through 8, each with weight
1/2, and requires the new remainder to lie in [1,3]. Every old remainder in
[1,7] is then possible: the five permitted digits give overlapping intervals.
Require the digit also to be divisible by 3. Only 0 and 6 remain, so the possible
old remainders become [1,3] ∪ [4,6]. The target 7/2 lies in the gap. Both
congruences are compatible; compatibility alone does not preserve coverage.

This observation gives an exact one-step test for adding congruences to the
feedback construction. It is an elementary consequence of the Chinese
remainder theorem and interval overlap, not a claim of a new mathematical
technique. Its use here is to identify precisely what an added constraint costs.

## Exact calculation

Fix a cumulative digit sum C, an allowance A, a positive weight w and a
continuation interval [l,h], where 0 ≤ l ≤ h. Impose the existing prefix
congruence C+d ≡ 0 (mod M) and any additional digit congruences. Generalised
CRT either finds them inconsistent or writes their simultaneous solutions as
one residue class modulo L, the least common multiple of the moduli. After
intersecting with 0 ≤ d ≤ A, the permitted digits form a finite progression

    d₀, d₀+L, …, d₀+(k−1)L.

If k=0, no remainder is admissible. Otherwise the complete set of admissible
old remainders is

    ⋃_{j=0}^{k−1} [ (d₀+jL)w+l, (d₀+jL)w+h ].

For k≥2, this set fills its convex hull **if and only if**

    Lw ≤ h−l.

If the inequality fails, there are exactly k−1 open gaps, each of length
Lw−(h−l). When k=1 the set is a single interval with no spacing condition,
including the case of an interval consisting of one point.

**Proof.** A digit d is permitted at remainder r exactly when l ≤ r−dw ≤ h,
which is equivalent to dw+l ≤ r ≤ dw+h. This proves the union formula.
Adjacent intervals overlap or touch exactly when
(d+L)w+l ≤ dw+h. If they fail to touch, their open gap cannot be covered by
an earlier or later interval, since all left endpoints and all right endpoints
increase with d. This proves necessity, sufficiency and the gap lengths.

For an arbitrary finite digit set the same proof uses each consecutive digit
gap separately. In particular the Boolean divisor-support relation permits
at most the two digits b and b+1, where b is the contribution from previously
selected proper divisors. Intersect those with the congruences first. A digit
sequence cannot be called a support sequence without this Boolean witness.

## Implementation and independent checks

`feedback.py::remainder_cover` implements this union in compressed form without
enumerating a large allowance. It returns the first interval, translation,
number of intervals, hull and exact gap length. `Step.check` remains the
independent direct predicate used in the tests. The regression suite checks
interval endpoints and a point in every intervening elementary interval; it
also tests an empty set, singleton, touching intervals and incompatible CRT.

The API accepts a state, so it can diagnose a contributed constraint at the
actual cumulative sum and Boolean history. The CLI's `--cover --request`
inspects the initial state only. The proof above is an ordinary mathematical
argument; the implementation has exact rational tests. Neither is presented
as a Lean formalization of the general covering assertion.

## What is still needed for an infinite construction

A one-step cover does not supply an infinite schedule. To use
`admissible_digits_hasSum` in
[FeedbackContinuation.lean](../../../lean/ErdosProblems/Synthesis/FeedbackContinuation.lean),
one must supply actual choices satisfying every step contract and continuation
upper bounds tending to zero. Eventual congruences additionally use the nested
moduli and divisibility-cofinal schedule hypotheses of
`admissible_digits_hasSum_eventual_congruences`.

Covering every permitted continuation state at every stage would justify
recursive selection. A calculation at one state or finitely many stages does
not establish that premise. This is where a new mathematical constraint may
require a new proof, even when its finite certificates all pass.

## Contribute and replay a policy

Keep the contract, admissibility implementation and choice policy distinct.
A policy can be restricted JSON data with a `policy` list whose entries are
`min`, `max`, `middle` or `previous`; it chooses among admissible digits and
cannot change the declared request. Use `--runner policy --policy-result`
to apply it to another request. A new arbitrary Python policy is software to
review, not a data-only input.

The recipient saves the intended request independently, then runs:

```sh
python3 research/experiments/sparse_interpolation/feedback.py \
  --request request.json --verify-result returned-result.json \
  --output replay.json --lean checked-candidate.lean
```

The replay checks the candidate against that request and rejects a different
request or invalid digits, even if the submitted result claims success. It
reconstructs the Lean candidate from the recipient's request. Run the existing
[proof workbench](../../../docs/agents/AGENT_WORKBENCH.md) to probe and replay
that source if kernel evidence is wanted. Merely emitting it is not kernel
acceptance. Replay establishes neither optimality nor infinite continuation.

Return the policy, request, result, replay and a human explanation through the
[shared contribution path](../../../CONTRIBUTING.md#return-what-you-learned).
Explain what the policy changes and report a distinct reuse input, including
failures. Credit the idea, implementation and checking separately. The included
regressions are internal journey tests, not an accepted outside contribution.
