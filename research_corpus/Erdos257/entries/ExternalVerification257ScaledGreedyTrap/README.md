# Erdős #257: scaled greedy trap and the canonical 1/21 frontier

This package exposes the source-current dynamical normal form of the base-two
Mersenne achievement set. After scaling the greedy residual by `2^N`, the
achievement set is exactly the set of nonnegative initial states whose orbit
never reaches the universal barrier `2`. The complementary theorem is stronger
than unboundedness: every nonnegative initial state outside the achievement set
has `scaledGreedyRemainder x N → +∞`. Its proof finds a fatal rank and uses the
positive excess over the complete tail, which is doubled by each later scale.

Membership also has an exact recurrence criterion with a much weaker-looking
hypothesis: one bounded cofinal subsequence of scaled remainders is enough. In
symbols, for `0 ≤ x`, membership is equivalent to the existence of `B` such that
beyond every cutoff some `N` has `scaledGreedyRemainder x N ≤ B`. This does not
require a prescribed bound, convergence, a global orbit bound, or bounded return
gaps. The reverse implication uses the exponential-escape theorem.

For every nonnegative rational target, membership is equivalently cofinal
crossing of the moving lower separatrix. The displayed `1/21` theorem is its
canonical specialization: beyond every cutoff, some rank `N` satisfies
`2 * scaledGreedyRemainder (1/21) N < mersenneScale (N+1)`.
The package separately exposes the `1/21` bounded-cofinal-return specialization
because it is the weakest native recurrence criterion currently isolated for
that open target.

These are exact equivalences, not a proof that the `1/21` crossings occur.
Membership of `1/21`, the construction of an infinite rational support, and
Erdős #257 remain open. The older fatal/cofinite/aligned-branch classification
is a compatible alternate coordinate, not the sharpest current producer.

The Challenge is Mathlib-only. Both Comparator configs enable NanoDa and
permit exactly `propext`, `Quot.sound`, and `Classical.choice`. This is a
first-wave Palomar candidate, not a novelty, review, acceptance, publication,
or submission claim.

`lakefile.toml` registration remains for the integrating agent.

Focused Lean replay was attempted through the guarded build on 2026-08-31 and
was deferred before compilation at the low-disk firewall: 427,282,432 bytes
free versus the 17,179,869,184-byte minimum. Static contracts remain
checkable; theorem transport and the axiom audit remain pending until that
storage re-entry condition is met.
