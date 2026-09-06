# ExternalVerification243TwoModulusRecordCut

## The two theorems

**Finite cut.** Let `H % 6 = 5`, let `m > 1` divide `H` and `l > 1` divide
`H + 2`, and let both divide `v'`. If `u'` and `v'` are coprime, `u` and `u'`
are coprime, `u < H ≤ u'` and `u' ≤ u + 4`, then no such step exists.

**Orbit form.** If those two moduli persist in the reduced denominator from an
index `s`, `H` sits above `runningMax u s`, and every record-setting step from
`s` rises by at most four, then `u n < H` for every `n ≥ s`.

## Why it is not routine

With jumps up to four there are five candidate landings, so the single
forbidden landing of the odd protected cut is not enough. Two moduli kill the
landings at `H` and `H + 2` against coprimality of the next pair. The
congruence `H ≡ 5 (mod 6)` does all the remaining work: it makes `H + 1`
divisible by six, so `H + 1` collides in turn with `H - 3`, `H - 2` and `H - 1`,
and `H + 3` collides with `H - 1` by parity. The landing at `H + 4` would force
`u ≥ H`.

Compared with the odd protected cut, the jump budget doubles from two to four
and the prime-power protection machinery is replaced by bare persistence
hypotheses. That is a trade, not a free strengthening: persistence is assumed.

## Where it stops

The cut does not extend to jump five, and the obstruction is explicit rather
than a gap in the argument. The source module records a genuine primitive step,
`u = 33`, `v = 5 * 37 * 41`, `a = 231`, `u' = 38`, which crosses `H = 35` past
both forbidden landings `m = 5` and `l = 37` with coprime endpoints on both
sides, in one jump of size five. Extending the cut would need a third forbidden
landing, and this fixture shows no purely congruential strengthening of the
present hypotheses can supply one.

## What is not established

Persistence of the two moduli is a hypothesis. Discharging it for primes that
never disappear from the denominator is an open analytic input of the same
shape as the supply hypothesis of the odd protected cut. Erdős #243 remains
open.

Lean elaboration of `Challenge.lean`, `Solution.lean`, `NegativeSolution.lean`
and `AxiomAudit.lean` has not been run for this packaging pass. It is pending
the next governed build. Comparator replay, Palomar mechanical verification and
Palomar editorial review are separate gates and none is recorded.
