# Prime predecessor-gap threshold lab

## Exact target

Write the reduced strict-successor predecessor gap as
`Delta_m=u_m/v_m`.  `PrimeZeroBranch.lean` proves that

`((m+2)m!-2)v_m <= m^2(m!-1)u_m`

is a sufficient tail-free certificate: it forces either a non-unit carry or
the useful maximal-digit branch.  If this inequality held automatically at
every prime, Euclid's theorem would provide its cofinal index supply.

## Discriminating computation

`scripts/check_erdos68_prime_predecessor_threshold.py` uses exact `Fraction`
arithmetic for

`Delta_(m+1) = m Delta_m - 1/(m!-1) - b_m`

and compares the two cleared integers only at prime indices.  It stops at the
first failure, rather than extending a carry horizon.

The threshold holds at `m=3` and already fails at the next prime, `m=5`.
Here `Delta_5=18/115`, so the cleared right-minus-left margin is `-42820`.
The receipt stores `u_5`, `v_5`, and both cleared sides, making the
counterexample independently replayable without floating point.

This falsifies the universal every-prime assertion, but it does not falsify an
eventual-prime assertion that permits finitely many exceptions.  It does not
weaken the Lean consumer and does not say that the carry at 5 is a unit carry.
The viable prime routes are an eventual-threshold theorem, the strictly
sharper lower-endpoint cylinder escape condition, or a condition using actual
denominator/residue structure beyond primality.  The certified scalar spectrum
through 300000 makes the first route concrete: its only `D_m=-1` prime events
are 5 and 23, and every `D_m=0` event separately clears the thin threshold
margin.  Proving the combined odd-index threshold from 25 onward would finish
it.
