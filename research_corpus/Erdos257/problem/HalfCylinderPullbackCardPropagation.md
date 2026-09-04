# Half-cylinder pullback-card propagation

## Status

This note records Lean-checked propagation and alternating-reset packet
theorems together with exact finite falsification receipts.  Erdős #257
remains open.  The symmetric middle-reset return inequality is now proved;
the upper terminal packet inequality and the pullback-coordinate lower bound
isolated below are not yet proved at all depths.

## The invariant that survives both cylinder blocks

The late-upper audit attaches to an upper reset at source `s`, its largest
false rank `d`, and the following right length `k` the exact integer

\[
 Q_k=R_{d+1}-2^{d+1}-4
      +2^{(2d+1)-(s+k)}-2^{(2d+2)-s}.
\]

The raw values `Q_k` are not monotone along successive reset blocks; the
existing audit has many strict-growth failures.  The useful invariant is
instead the support-sensitive inequality

\[
 |A_{s+k+1}|+2\le Q_k. \tag{PC}
\]

Every seam pulse is at most twice the current support cardinality.  The
two-unit margin in (PC) therefore gives the sharper forward digit budget
`pulse+4 <= 2Q_k`; the backward fixed-support digits obey the same `2Q_k`
budget.  Lean now retains the quantitative content of those budgets instead
of collapsing them immediately to an order comparison.  If `G` is the
critical gap and `R` the terminal endpoint remainder, it proves

\[
 4^{s-d}Q_k+2Q_k\le 3G,
 \qquad
 4^kG+2G\le 3R,
\]

and hence the composed parent/child packet inequality

\[
 4^{s-d+k}Q_k+2\,4^kQ_k+6G\le 9R. \tag{QA}
\]

In particular `R>=G>=Q_k`, recovering the earlier cardinality propagation,
but (QA) keeps both base-four amplification factors for the recursive step.

Lean checks the generic estimates and the complete two-block specialization
in
`Erdos257PeriodNoncollapse/HalfCylinderPullbackCardPropagation.lean`:

- `affineRightRunCharge_le_coordinate_geometric`;
- `exactCylinder_amplification_of_twoBudget`;
- `scaled_coordinate_add_two_coordinate_le_three_remainder`;
- `fixedSupportPulseCharge_le_coordinate_geometric`;
- `three_mul_fixedSupportPulseCharge_add_two_mul_le`;
- `scaled_pullbackCoordinate_add_two_le_three_criticalGap`;
- `twoStage_amplification`;
- `coordinate_le_criticalGap_of_fixedSupportPullback`;
- `seamUpperThenRightRun_scaledCriticalGap_add_two_le_three_remainder`;
- `seamUpperThenRightRun_remainder_ge_supportCard_add_two`;
- `lateUpperReset_scaledPullback_add_two_le_three_criticalGap`;
- `lateUpperReset_criticalGap_ge_endpointCard_add_two_of_pullbackCoordinate`;
- `lateUpperReset_twoBlock_amplification_of_pullbackCoordinate`;
- `lateUpperReset_endpointRemainder_ge_card_add_two_of_pullbackCoordinate`.

Thus (PC) propagates first through the exact backward pullback to the forward
critical gap and then through the observed upper/right cylinder to

\[
 |A_{s+k+1}|+2\le R_{s+k+1}. \tag{CG}
\]

This is precisely the seam support-cardinality gap needed to exclude the
mature quotient-take/real-skip midpoint cell.  It uses neither false
monotonicity of `Q_k` nor a support-free congruence.

This is also the correct coordinate response to the denominator-cancellation
audit in
`formal_math/erdos257_hole_geometry/notes/DenominatorCancellationAudit.md`.
That audit proves that the reduced remainder denominator retains forced
top-block cyclotomic factors, so a finer estimate in the raw remainder
coordinate cannot recover the death-window argument.  Inequality (QA) lives
instead in the renormalized integer quotient/defect coordinates and therefore
does not pay that structural `2^{Theta(n^2)}` denominator cost.

## The pulse register is exactly a frozen multiplicity window

The quotient-coordinate connection to the hole/excess-multiplicity lane is
now exact.  For an arbitrary finite support `A`, Lean proves

\[
 \sum_{e\in A}\operatorname{rowPulse}(b,e)
 =c_A(2b+2)+2c_A(2b+1),
\]

and therefore identifies the full base-four pullback register with the
division-free binary coefficient window on the paired interval:

\[
 C^{\rm fixed}_{b,A}(k)
 =F_A(2b,2k).
 \tag{MW}
\]

If `e_A` is the centered Möbius carry, all interior divisor incidences in
that window telescope:

\[
 F_A(n,J)-(2^J-1)
 =2^J e_A(n-1)-e_A(n+J-1).                 \tag{CT}
\]

The affine `+4` digit of the actual cylinder is only an explicit geometric
baseline.  After clearing the denominator three,

\[
 3C^{\rm affine}_{b,A}(k)
 =3F_A(2b,2k)+4(4^k-1).                    \tag{AR}
\]

The checked declarations are:

- `sum_rowPulse_eq_pairedSupportCoeff`;
- `fixedSupportPulseCharge_eq_finiteCoeffWindowNumerator`;
- `finiteCoeffWindowNumerator_sub_baseline_eq_centeredCarry`;
- `fixedSupportPulseCharge_sub_geometric_eq_centeredCarry`;
- `three_mul_affineRightRunCharge_eq_fixedSupport_add_geometric`;
- `three_mul_affineRightRunCharge_eq_multiplicityWindow_add_geometric`.

This is the precise bridge suggested by the multiple-set cockpit: the pulse
register measures weighted holes versus excess multiplicity, rather than a
raw rational remainder.  It also records the limit of that bridge.  The
pullback freezes the *finite terminal seam support*, whereas Theorem G and
the rational `X(P)` lattice concern the completed infinite rational support.
There is no sign-monotone transfer between them.

The exact forced-seam audit through row 2,500 checks (MW) and (CT) on all 605
completed upper pullbacks.  The centered window has 523 positive, 37 zero,
and 45 negative values; 234 windows have no holes at all.  Its minimum is
`-488` at `(s,d,k_back)=(19,14,5)` (weighted holes `520`, positive excess
`32`), while its maximum is `774773` at `(511,502,9)` (weighted holes
`34856`, positive excess `809629`).  Thus the exact identity is useful
coordinate unification, but a bare hole bound or positivity claim cannot
prove (PC), (MS), or the upper endpoint packet inequality.  Any use of the
Möbius endpoint carries must retain their coupled difference in (CT); the
individual carries can be enormous while the pulse packet stays small.

## The symmetric middle return is now unconditional

Write the exact right-run charge after source row `d` and length `k` as

\[
 C_k=\sum_{q<k}4^{k-1-q}(p_{d+q+1}+4).
\]

Lean proves the signed cylinder identity

\[
 R_{d+k+1}-2^{d+k+1}+C_k=4^k\operatorname{dev}_d. \tag{SP}
\]

Thus the desired middle-origin lower return inequality is equivalent to the
terminal packet crossing the three-halves boundary:

\[
 2^{d+k}<4^k\operatorname{dev}_d
 \quad\Longleftrightarrow\quad
 3\cdot2^{d+k}<R_{d+k+1}+C_k. \tag{MR}
\]

The right side of (MR) is now proved whenever the observed run terminates in
an actual carry and `d>=12`.  The new ingredient is only one unit but it is
forced at every depth.  A carry identifies the next greedy word with the
false-extension of the adjacent cut's upper word.  Rank `2` is selected in
every greedy seam word from row `13` onward, remains selected under false
extension, and has row pulse exactly one.  Hence the upper pulse is positive.
Separation and carry then give

\[
 2^{s+1}\le R_s+O_s,
 \qquad 4O_s+p_s^{\rm upper}\le2^{s+1},
 \qquad p_s^{\rm upper}>0,
\]

so `4O_s<2^(s+1)` and therefore

\[
 R_s>3\cdot2^{s-1}. \tag{TC}
\]

At the terminal row `s=d+k+1`, (TC) alone clears the right side of (MR), even
before adding the nonnegative charge `C_k`.  The checked declarations are:

- `seamAdjacentCut_abovePulse_pos_of_successorCarries`;
- `seamSuccessorCarries_remainder_gt_threeHalf`;
- `rightRun_signedPacket_exact`;
- `rightRun_scaledDeviation_gt_iff_endpointPacket_gt_threeHalf`;
- `rightRun_endpointPacket_gt_threeHalf_of_terminalCarry`;
- `rightRun_scaledDeviation_gt_of_terminalCarry`.

This closes the roadmap's symmetric middle-reset return step.  It also makes
the remaining asymmetry exact: for an upper-origin block one still needs the
opposite terminal packet inequality

\[
 R_{d+k+1}+C_k<2^{d+k}. \tag{UP}
\]

The corpus already identifies (UP) with the upper critical-index identity.
The next proof must therefore establish this one-sided upper packet bound (or
its equivalent pullback-card/middle-staircase form); no separate middle
return estimate remains.

## Exact previous-middle form

For every late upper reset with `s>=13`, the existing corpus proves that the
largest false predecessor `d` is a middle producer.  Substituting its exact
landing recurrence rewrites the pullback coordinate as

\[
 Q_k=4R_d-p_d-4
      +2^{(2d+1)-(s+k)}-2^{(2d+2)-s},
\]

where `p_d` is the actual paired divisor-incidence pulse.  Consequently the
remaining producer can be stated without signed subtraction:

\[
 2^{(2d+2)-s}+p_d+4+|A_{s+k+1}|+2
 \le 4R_d+2^{(2d+1)-(s+k)}. \tag{MS}
\]

Lean defines (MS) as `LateUpperPreviousMiddleStaircaseEscape`, proves that it
implies (PC), and then proves that it implies (CG) at every late upper/right
endpoint in the exact factor range.  This is the source-current analytic
frontier: rule out a narrow middle-coordinate window immediately above one
explicit dyadic staircase while retaining the actual paired pulse.

The older row bound `d<=R_d` is not strong enough for (MS), and pure residue
classes are already known to give false danger alarms.  A successful proof
must therefore descend through the alternating upper/middle reset packets
with their ordered divisor-incidence digits, or establish a stronger coupled
barrier that directly implies (MS).

## Support-free rank reduction

There is a cleaner sufficient producer which removes the moving support set
from the hypothesis.  At the endpoint row `s+k+1`, the seam word has only
`s+k-1` selectable ranks.  Therefore

\[
 s+k+1\le Q_k \tag{QR}
\]

implies `|A_(s+k+1)|+2 <= Q_k`, hence (PC) and the complete two-block
endpoint conclusion.  Lean checks this implication as
`pullbackCard_of_lateUpperPullbackRankEscape`, with (QR) packaged as
`LateUpperPullbackRankEscape`.

This is a reduction, not an all-depth proof of (QR).  Exact canonical replay
through row 2,500 found no failure of (QR); the minimum margin was four at
`(s,d,k)=(19,14,1)`, where `Q_k=25` and the endpoint row is `21`.  The exact
eight-generation noncanonical countermodel in
`UpperToMiddleLandingSupportAudit.md` shows why a proof of (QR), (PC), or
(MS) cannot come from a bounded recent affine ancestry window alone: it must
retain the distinguished canonical origin or an equivalent global invariant.

## Exact finite discriminator

The forced-seam mode of
`ErdosProblems/Erdos257/scripts/half_midpoint_tail_bridge_lab.py` now reports
the late-card premise separately from the two nonlate base failures.  A
targeted exact run through rank 5,000 produced:

```text
late upper critical pullbacks completed: 1226
late pullback-card failures:             0
minimum late pullback-card slack:        17
minimum source / largest false / k:      19 / 14 / 1
minimum endpoint / Q / endpoint card:    21 / 25 / 6
```

The computation used exact integer seam recurrence and support sets.  It is
only a falsification test for (PC)/(MS); it does not prove their all-depth
quantifiers or settle one-half membership.

The audit now also computes the left side of (QA) directly.  Through rank
2,000, all 483 late pullbacks satisfying the factor range and (PC) obeyed
(QA), with zero failures.  The minimum slack was 649,269 at
`s=19, d=14, k=1, Q=25, G=25065, R=100251`.  This is an independent exact
check of the Lean theorem's coordinate specialization, not extra evidence
for the still-open premise (PC).

The same exact run records all completed upper/right blocks through rank
2,000.  All 485 terminate in the middle branch, all 485 satisfy (UP), and the
minimum strict endpoint packet slack is 55 (source row 5, endpoint row 7).
The next-landing identity is checked exactly as

\[
 P_{\rm next}=4P_{\rm endpoint}+2^{\rm endpoint+1}+4,
\]

so its strict slack is `4 * endpoint_slack + 3`; the observed minimum is 223.
This is finite evidence for the still-open upper inequality, not an all-depth
proof.  The symmetric lower return (MR), by contrast, is Lean-checked at all
mature terminal carries.

## Direct parent-child monotonicity is false

A targeted exact probe of the proposed alternating-reset descent compared
each late upper block with the preceding upper block whose endpoint is its
largest-false middle source.  Through row 1,000 there are 240 such parent-child
pairs.  Three natural induction quantities all fail to be monotone:

```text
quantity                                             strict-decrease events
Q - (endpoint_card + 2)                              45
Q / (endpoint_card + 2)                              45
4^(backward_length) * Q / (endpoint_card + 2)         7
```

The first failure of all three is the child source 43 over parent source 41:

```text
child:  Q = 12,829,399,059, endpoint_card + 2 = 25
parent: Q = 137,102,541,922, endpoint_card + 2 = 17
backward_length = 1
```

This is not a failure of (PC): both margins are enormous.  It is a decisive
counterexample to proving (PC) by direct monotonic descent of its slack or
ratio, including the obvious one-block base-four normalization.  The surviving
route must exploit the coupled two-block inequality (QA), the exact staircase
identity (MS), or an ordered pulse constraint that is lost by these scalar
normalizations.  The durable authority capture is
`cap_quick_erdos_257_normalized_parent_child_pullba_dcb7f7894c0e`.

## Validation

The focused command

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py \
  --jobs 2 Erdos257PeriodNoncollapse.HalfCylinderPullbackCardPropagation
```

completed successfully after 3,345 jobs.  The printed axiom audits for all
new declarations contain only the standard `propext`, `Classical.choice`,
and `Quot.sound` ceiling.

The quantitative two-block source and audit landed in commit
`2347beb358efa425f4cac2d3eecbaa51ccbcdf3a`; the exact packet identities,
terminal-carry theorem, and extended audit landed in
`83190aa256ad9561f73c4ec92894f687c97cff4a`.
