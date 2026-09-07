# ExternalVerification243SlowRiseBarrier

## The theorem

Let `a, u, v : ℕ → ℕ` and `N B : ℕ`. Suppose that from index `N`: every
multiplier satisfies `1 < a n`; `u n` and `v n` are coprime; and the two
cocycle equations `u (n + 1) + v n = a n * u n` and `v (n + 1) = a n * v n`
hold. Suppose also that `u` tends to infinity. Write `P` for the product
`∏ i : Fin B, a (N + i)`. Then it is impossible that `u (N + B) < P` and
`u (n + 1) ≤ u n + B` at every index `n ≥ N + B` with `u n < 2 * P`.

## Why it is not routine

The rise budget is charged only on the finite window `u n < 2 * P`, not
uniformly. The proof gets that by replacing gcd stabilisation, which needs
bounded negative magnitudes, with persistence: a common divisor of the
numerator and denominator states at one index divides every later state, and
therefore every later centred error. A Chinese-remainder block of the
pairwise-coprime multipliers `a N` through `a (N + B - 1)` is placed inside
the interval from `P` to `2P`, so a slowly rising numerator must land on one
block modulus while still inside the window. That modulus then divides every
later state, contradicting coprimality of the reduced tail.

## Relation to the bounded-rise entry

This statement dominates `no_boundedRise_reducedTail`, carried by
`ExternalVerification243BoundedRiseReducedTail`: a uniform rise bound `B` is
the special case in which the windowed hypothesis holds everywhere. The
dominance is recorded here. Whether the earlier entry is retired, merged or
kept is an editorial decision for the launch selection.

## What is not established

The block-start bound `hstart` and the windowed rise bound `hrise` are
hypotheses. Neither is derived from the underlying dynamics. The analytic
transfer that would supply them on the canonical Erdős #243 orbit, meaning
which moduli to choose and that a doubly-logarithmic rise budget is
admissible, is an ordinary proof in `SlowNegativePartRigidity.md` and is not
formalised. Erdős #243 remains open.

Lean elaboration of `Challenge.lean`, `Solution.lean` and `AxiomAudit.lean`
has not been run for this packaging pass. It is pending the next governed
build. Comparator replay, Palomar mechanical verification and Palomar
editorial review are separate gates and none is recorded.
