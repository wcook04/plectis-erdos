# Final-middle endpoint bypass audit

## Status

This pass tested whether the final-middle/all-right contradiction could
bypass the remaining global producer after the positive-sign theorem.  It
does not close the endpoint.  The useful outcome is an exact map of the
first surviving cells and a proof that the sharp-gap shortcut has reached
its natural limit.

## Existing stronger sign

Under the final-middle followed-by-all-right hypotheses, the corpus already
proves the landing excess is at least two:

```text
middleThenAllRight_landingExcess_two_le
```

in `HalfCylinderMiddleCarryLowerBound.lean`.  Thus positivity alone does not
advance the final-cell boundary; it only rederives exclusion of landing
excess one, equivalently `producerCarry = -3`.

The mechanism is the existing chain from the all-right limit inequality to
the rational fatal gap, the floor-`Z` wall, and integer pulse absorption.

## First surviving cell

Landing excess two is `producerCarry = -2` and lazy centred charge one.  The
exact tail comparison eliminates all phases except the already certified
survivor set:

```text
finalMiddleCell_neg_two_forces_phase_refinement_through_twentySix
finalMiddleTwentySixPhaseSurvivors_card = 412
```

so 412 of 2730 joint phases remain.  The forced `{2,3,6}` plus cofinite
baseline has tail approximately

```text
115/63 = 1.825396...
```

in the surviving `D = 2 (mod 3)` phase, below the fatal threshold two.  This
confirms that the phase is a structural survivor rather than a reversed
inequality.

Landing excess three (`producerCarry = -1`) is not eliminated by the
current mod-four residual-pulse/high-boundary-divisor channel.  Landing
excess at least four is on the nonnegative side of the two-sided dyadic
invariant, but that invariant yields only a remainder-or-overshoot witness,
not a contradiction with an all-right tail.

## Source-row reachability for the first surviving cell

The first surviving cell now has an additional exact source-row constraint.
In the only surviving mod-three phase, `producerCarry = -2` forces

```text
wordPulse % 4 = 2,
seamResidualPulse236 % 4 = 3,
3 <= seamResidualPulse236.
```

The residual pulse cannot come only from odd-boundary incidences, whose
weights are even.  Hence the selected source support contains an even-boundary
divisor `d` satisfying

```text
7 <= d < s,
d | (2*s+2),
3*d <= 2*s+2.
```

The exact Lean declarations are

```text
wordPulse_mod_four_eq_two_of_producerCarry_eq_neg_two
seamResidualPulse236_mod_four_eq_three_of_producerCarry_eq_neg_two
three_le_seamResidualPulse236_of_producerCarry_eq_neg_two
exists_high_boundary_divisor_of_producerCarry_eq_neg_two
exists_high_even_boundary_divisor_of_producerCarry_eq_neg_two
exists_high_even_boundary_divisor_scale_of_producerCarry_eq_neg_two
```

This is a genuine reachability filter on the 412 phase survivors, not a
closure.  The corresponding future-tail increment is exactly
`1/(2^d-1)`, and `d >= 7` gives only

```text
1/(2^d-1) <= 1/127 < 11/63.
```

Thus the forced divisor alone cannot fill the surviving tail deficit.  A
closure still needs either several coupled source incidences, a smaller
forced rank, or a global argument converting the support condition into
additional tail mass.

The residual pulse actually forces a coupled alternative.  Let `E` be the
selected ranks outside `{2,3,6}` dividing `2*s+2`, and let `O` be those
dividing `2*s+1`.  Consecutivity of the two boundaries gives the exact count

```text
seamResidualPulse236 = |E| + 2*|O|.
```

For `producerCarry = -2` the left side is `3 (mod 4)`.  Hence

```text
|E| >= 3,
```

or

```text
|E| = 1 and |O| >= 1.
```

This improves the single-divisor statement to three even-boundary channels
or one even plus one odd channel.  It still does not close the cell: selected
divisor ancestry does not force selection of the complementary quotient.
Exact counterexamples to that inference occur at `s=89`, where selected
`20 | 180` has unselected quotient `9`; at `s=107`, where selected `27 | 216`
has unselected quotient `8`; and at `s=38`, where selected `7 | 77` has
unselected quotient `11`.  The forced ranks can therefore remain of order
`s`, leaving exponentially small tail mass.

The exact decomposition and dichotomy are Lean-checked as
`seamResidualPulse236_eq_evenCard_add_two_mul_oddCard` and
`residualBoundary_card_dichotomy_of_producerCarry_eq_neg_two` in
`HalfCylinderMiddleCarryLowerBound.lean` (commit
`aad4b86fbb9f01e9c75f67cb8c21992a7a3e5773`).

Exact replay through row 4800 found 1174 middle resets and no landing-excess
two event; the smallest mature middle excess was 1565 at row 14.  This is
bounded computational evidence only.

## Sharp-gap stop line

The Mersenne-gap bounds at `D >= 13` give

```text
2 / 4^(D+1) < mersenneGap D < 3 / 4^(D+1).
```

They can eliminate the carry `-3` cell but cannot eliminate carry `-2`.
Therefore no refinement that uses only this numerator-versus-gap comparison
can close the first surviving cell.

The exact surviving all-right window remains

```text
2 <= landing excess < 2 * sqrt(2*D+2) + 8,
```

from `middleProducer_allRight_landingExcess_window`.

## Consequence

The endpoint is not one sign flip away.  A successful bypass must add new
support-sensitive information inside the thin positive window: empty the
412 phase survivors for excess two, discharge excess three, and control the
nonnegative carry regime, or replace all three with a single stronger
tail/selection theorem.  No such theorem is claimed here.
