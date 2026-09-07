# ExternalVerification243ProtectedEpochEnergy

## The theorem

Let `p` be an odd prime, `l ≥ 1` and `Q = p ^ l` with `16 ≤ Q`. Take a
dynamically reduced primitive orbit with arbitrary cancellation factors `hc n`
satisfying, from an index `s`, the division-free cocycle `w n + v n = a n * u n`
together with `w n = hc n * u (n + 1)` and `a n * v n = hc n * v (n + 1)`,
coprimality of `u n` and `v n`, positivity, and the centring bound
`2 * w n ≤ 3 * u n`. Suppose `Q` divides `v s`, that `4 * runningMax u s < p * Q`,
and that `p * Q ≤ 2 * u τ` for some `τ > s`.

Then there is a finite set `J` of indices in `[s, τ)` such that every `n ∈ J` is
a global record step, is cancellation-free (`hc n = 1`) and jumps by at least
three, and such that

`p * Q ≤ (8 * p + 8) * |J| + 4 * ∑_{n ∈ J} (u (n + 1) - u n - 2) + 8 * p`.

## Why it is not routine

The single divisibility `Q ∣ v s` is reused across the whole family of odd
multiples of `p` inside the window from `p * Q / 4` to `p * Q / 2`, of which
there are at least `(Q - 8) / 8`. No product of moduli appears anywhere, so the
bound is uniform in the cancellation factors. The earlier route charged one
protected prime power against one barrier height, which forced a fresh modulus
per barrier and a Chinese-remainder product whose size was never controlled.

Three ingredients carry the proof: a barrier count for the window; a per-step
capacity bound, because barriers first crossed at the same step lie between
consecutive numerators and are spaced `2 * p` apart; and a per-barrier
clean-record argument, in which persistence of the prime power through the
crossing kills the exact landing and adjacent coprimality kills a jump of at
most two.

## What it discharges

This closes the explicit `-- OPEN:` target recorded at the end of
`ErdosProblems/Erdos243/PrimitiveRecordBarrier.lean`. It also drops a
minimality hypothesis present in the source return: `τ` need not be the first
index at which the orbit reaches `p * Q / 2`, because each barrier supplies its
own first-crossing index.

## What is not established

The statement is a lower bound on record energy inside one protected epoch. The
matching upper bound — that a bounded-negative-part or summable orbit has finite
total energy, so infinitely many protected epochs are impossible — is not proved
here and is exactly the open parent. The centring bound and the protection
hypothesis are assumed rather than derived from the dynamics. Erdős #243 remains
open.

Lean elaboration of `Challenge.lean`, `Solution.lean`, `NegativeSolution.lean`
and `AxiomAudit.lean` has not been run for this packaging pass. It is pending
the next governed build. Comparator replay, Palomar mechanical verification and
Palomar editorial review are separate gates and none is recorded.
