# ExternalVerification243SaturatedSquareTransport

## The two theorems

Fix one primitive step of a reciprocal tail dynamic: `w + v = a * u`,
`w = hc * u'`, `a * v = hc * v'`, with centred errors `e = v - (a - 1) * u` and
`e' = v' - (a' - 1) * u'`.

**Saturated square transport.** `u' ∣ hc * e * e' - v ^ 2`, with no hypothesis
beyond those equations and definitions.

**The Legendre defect.** If `u' ∣ b * e * e' - (b * s) ^ 2` and some prime `p`
divides `u'` with `e * e'` a non-square in `ZMod p`, then `b ≠ 1`.

## Why the first is not routine

The transport is modulo the whole next numerator, with the full content
removed. The corpus lemma it replaces transports only modulo the largest
divisor of `u'` coprime to the removed content, which is what a coprimality
hypothesis buys. Here there is no such hypothesis. Two orientation identities
fall out of the cocycle with no sign or size side condition; multiplying them
and using the cocycle again to remove the spurious multiplier gives an exact
identity whose right-hand side is the raw numerator times an explicit integer.
Everything else is bookkeeping.

## Why the second is included

It is the honest reach, and its limit is the interesting half. The congruence
`b * e * e' ≡ (b * s) ^ 2 (mod u')` is blind to a pure square payment: if
`b = 1` it degenerates to `e * e' ≡ s ^ 2` and carries no quadratic-character
information at all. So the obstruction excludes exactly one thing, that the
removed content is a perfect square, and quadratic-character counting can never
detect square deletion. Packaging the positive identity without this boundary
would misrepresent what the method can do.

## What is not established

Neither statement bounds the cancellation factors, the numerators or the orbit.
Both are single-step facts. Erdős #243 remains open.

Lean elaboration of `Challenge.lean`, `Solution.lean`, `NegativeSolution.lean`
and `AxiomAudit.lean` has not been run for this packaging pass. It is pending
the next governed build. Comparator replay, Palomar mechanical verification and
Palomar editorial review are separate gates and none is recorded.
