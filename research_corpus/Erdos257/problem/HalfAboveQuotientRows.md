# Target-zero quotient rows for Erdős 257

Status: the compactness consumer is Lean-checked; the all-depth producer is
open.  Finite computation is used only to discriminate the producer and is
not promoted to a proof of Erdős problem 257.

## Why this is a distinct row target

Put

\[
 q_N(d)=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor.
\]

The existing `ExactLocalMersenneHalfRow` interface uses the truncated
nonterminating-binary target (2^{N-1}-1).  The audit supplied by the
operator instead uses the adjacent target

\[
 T_N^+=2^{N-1}.
\]

These targets must not be mixed in a transition formula, but both have the
same compactness endpoint.  If a Boolean row (D_N\subseteq\{2,\ldots,N\})
satisfies

\[
 \sum_{d\in D_N}q_N(d)=2^{N-1},
\]

then the exact quotient/fraction decomposition gives

\[
 \sum_{d\in D_N}\frac1{2^d-1}-\frac12
 =\frac{\Phi_N(D_N)}{2^N},
 \qquad
 \Phi_N(D_N)=\sum_{d\in D_N}
 \frac{2^{N\bmod d}}{2^d-1}.
\]

Every summand of (Phi_N) lies in ((0,1)), so

\[
 0<\sum_{d\in D_N}\frac1{2^d-1}-\frac12
 <\frac{|D_N|}{2^N}\leq\frac{N+1}{2^N}.
\]

Thus any cofinal supply of target-zero rows gives finite achievement-set
points converging to (1/2) from above.  Closedness supplies an exact
representation, and the odd-denominator obstruction forces its support to
be infinite.

This chain is now checked in
`ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean`:

- `ExactAboveLocalMersenneHalfRow`;
- `CofinalExactAboveLocalMersenneHalfRows`;
- `abs_exactAboveLocalMersenneRowValue_sub_half_le`;
- `localMersennePrefixValue_le_half_of_aboveResidual_card`;
- `localFractionMass_cast_eq_binaryCoeffTail`;
- `localFractionMass_cast_le_two_sqrt_add_four`;
- `aboveResidual_lt_fractionMass_of_half_lt_localMersennePrefixValue`;
- `aboveResidual_cast_lt_two_sqrt_add_four`;
- `aboveResidual_lt_card_of_half_lt_localMersennePrefixValue`;
- `aboveMidpointResidual_lt_rank_of_real_crossing`;
- `aboveMidpointResidual_cast_lt_two_sqrt_add_four_of_real_crossing`;
- `half_mem_mersenneAchievementSet_of_cofinalExactAboveLocalRows`;
- `exists_rational_half_counterexample_of_cofinalExactAboveLocalRows`;
- `not_universal_of_cofinalExactAboveLocalRows`.

The last theorem is conditional.  It does not assert the cofinal producer.

## The discriminating computation

The exact script

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/half_above_quotient_rows_audit.py --max-n 5000
```

runs two independent calculations.

1. It computes target-zero quotient greedy only through the half cutoff.
   The remaining coins are a complete binary bank, so closure is equivalent
   to the lower residual being below its bank capacity.
2. It certifies the real half-greedy word with scaled-integer interval
   arithmetic and compares every quotient lower-core bit with the
   corresponding real-greedy bit.  No floating-point value decides a bit.

The probe has three direct falsifiers: a bank-capacity failure, a lower-core
bit mismatch, or negative adjacent-endpoint financing.  A literal odd
midpoint hole is recorded separately because the two-horizon bypass handles
that value conditionally.

At horizon 5000 the receipt is:

```text
target: 2^(N-1)
horizons checked: 4..5000 (4997 rows)
exact rows: 4997
closure failures: 0
real-feasible lower cores: 4997
lower-core mismatches: 0
negative-financing events: 0
midpoint holes: 0
minimum financing: 3 at N=14
midpoint takes: 1246
midpoint residual below rank: only (d,R)=(3,2),(7,2)
minimum R-d for midpoint takes with d>=8: 377 at d=14
real half word certified through rank 2500
real half word sha256: 114baa84dc181d11c7d4a39d84725430aa16d9a3fa237ef9867f0cd07828ba01
```

## What the computation selects

The meaningful structural conjecture is stronger than row closure and more
specific than a generic carry bound:

> For every (N\geq4), target-zero quotient greedy through
> (lfloor N/2\rfloor) agrees with the real greedy orbit for (1/2).

If true, the lower core is automatically real-feasible.  At the next
endpoint, every selected divisor contributes more than one half to the
quotient fractional mass.  That fractional ancestry finances the endpoint
divisor pulse, ruling out negative adjacent demand.  This is the exact
mechanism seen by the computation; bounded carries and literal horizon-word
stability are unnecessary and, respectively, impossible and false.

The remaining proof obligation is therefore not the compactness step.  It is
the all-depth real-prefix/quotient-prefix comparison, equivalently the
exclusion of the first strict quotient-take/real-skip mismatch.  Finite scans
do not exclude that first mismatch.

The new Lean mismatch certificate narrows that event further.  Suppose an
even row at endpoint `2d` takes its midpoint coin and leaves integer residual
`R`.  If the resulting prefix crosses above the real target `1/2`, then

\[
 R<|D\cup\{d\}|\le d.
\]

Indeed, the exact quotient/fraction decomposition shows that `R` finances
the real prefix whenever it finances the support-cardinality bound on the
fractional mass.  Thus a first mismatch must occur inside the small integer
window `R<d`.  Through `d=2500`, the quotient computation enters that window
only at `d=3` and `d=7`; the independent real-greedy certificate verifies
that both midpoint takes are still below `1/2`.  For every audited midpoint
take with `d>=8`, the much stronger `R-d>=377` holds.  This finite separation
does not prove that a later small-slack event cannot occur, but it replaces
an unrestricted fractional comparison by an exact, arithmetic falsifier.

## The fractional phase is the future divisor tail

There is a stronger exact identification.  For a finite support `D` on
ranks at least two,

\[
 \Phi_M(D)
 =\operatorname{binaryCoeffTail}
   \bigl(\operatorname{supportCoeff}(D),M\bigr).
\]

The equality is best seen dynamically.  Both sides start at the same finite
Mersenne support value when `M=0`, and both obey

\[
 X_{M+1}=2X_M-\#\{d\in D:d\mid M+1\}.
\]

Thus the quotient fractional phase is not a separate error term: it is the
future binary divisor-incidence tail already bounded by the divisor-pair
estimate.  Consequently any target-zero row with remaining integer slack
`R` which crosses above the real half target satisfies

\[
 R<\Phi_M(D)\le 2\sqrt M+4.
\]

At the midpoint endpoint `M=2d`, a first quotient-take/real-skip mismatch is
therefore confined to

\[
 \boxed{R<2\sqrt{2d}+4}.                                  \tag{9}
\]

This deletes every linear-size residual from the mismatch frontier.  It
does not by itself exclude the remaining square-root band.

## Two-step experiment on the surviving band

The companion exact probe

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/half_midpoint_tail_bridge_lab.py --max-rank 20000 --direct-check-through 100
```

avoids the old quadratic row scan.  If `W_d` is the endpoint-`2d` residual
after the certified real half prefix through `d`, and `g_n` counts selected
divisors of `n`, two quotient transitions give

\[
 W_{d+1}=4W_d-2g_{2d+1}-g_{2d+2}
          -b_{d+1}(2^{d+1}+1).                         \tag{10}
\]

The script certifies the real bits by dyadic interval arithmetic, checks
(10) against direct quotient evaluation through rank 100, and then uses only
exact integers.  Through rank 20,000 it reports:

```text
quotient/real midpoint mismatches: 0
direct recurrence failures: 0
takes in the square-root crossing window: (d,R)=(2,3),(3,2),(7,2)
minimum square-clearance from rank 8: 149657 at (d,R)=(14,391)
real takes / skips: 10028 / 9971
```

Here square-clearance is `(R-4)^2-8d`; nonnegative means the take lies
outside (9), without using floating point.  The persistence of the same
minimum at rank 14 is evidence for a backward critical-band argument, not a
finite proof.  The exact remaining producer is to show that a source-reachable
two-step orbit can never enter the square-root band after the sealed base
cases.

## The mismatch coordinate is exact

The real/quotient comparison can be stated without a one-sided estimate.  If
a target-zero prefix has integer residual `R`, then

\[
 \frac12<\sum_{a\in D}\frac1{2^a-1}
 \quad\Longleftrightarrow\quad
 R<\Phi_M(D).                                      \tag{11}
\]

This is now Lean-checked as
`half_lt_localMersennePrefixValue_iff_residual_lt_fractionMass`.  The sharper
integer tail envelope gives

\[
 \Phi_M(D)<2\lfloor\sqrt M\rfloor+3,
\]

so an even midpoint mismatch at rank `d` has the exact natural-number
signature

\[
 0\le R<2\lfloor\sqrt{2d}\rfloor+3.                \tag{12}
\]

The corresponding Lean declaration is
`aboveMidpointResidual_lt_two_natSqrt_add_three_of_real_crossing`.

The experiment now replays an independent dyadic enclosure for the real
residual alongside the integer recurrence.  At each midpoint it encloses the
candidate phase `Phi_m` and compares it with the integer quotient margin
`J_m`.  Thus it checks the exact dichotomy `J_m >= Phi_m` (real take) versus
`J_m < Phi_m` (real skip), not a floating approximation to either side.
Through rank 20,000 the maximum rigorous phase ceiling is 15, while the
mature take margin `J_m-ceil(Phi_m)` is minimized by 390 at rank 14 and the
closest mature skip still has `J_m=-252` at rank 8.  This is strong finite
separation, but not an all-depth gap theorem.

Two tempting shortcuts were also killed.  Reducing `J_m` modulo the least
power of four larger than (12) produces false central-band alarms already at
rank 9, so a bounded backward congruence window does not encode the sign of
the full margin.  Shifting the quotient target down by `2d+1` and repairing
from five adjacent targets also fails as a universal fringe argument: at
`d=9` the strict-core remainder is `2*2^d+9`, outside that repair block.  A
target shift may remove a single equality after a core bound is known; it
does not supply the missing core bound.

## Forced seam word and the support-cardinality collapse

The first-shell calculation can be made deterministic.  If a midpoint row
takes rank `d` with residual `R` while real greedy skips it, the actual stem
below `d` is forced to equal the integer-greedy seam word for

\[
2^{2d-1}-2^d,
\]

and its seam remainder is exactly

\[
E_d=R+1.
\]

This is Lean-checked by
`midpointRealSkip_forces_seamAlignment_and_remainder`.  The exact floor-error
coordinate supplies a sharper obstruction than the earlier square-root
band.  If `c_d` is the cardinality of the forced seam support, then

\[
E_d\ge c_d+2
\]

already forces the real decision at rank `d` to be a take.  Consequently a
quotient-take/real-skip mismatch must satisfy

\[
R\le c_d,
\qquad E_d\le c_d+1,
\qquad E_d<d.                                           \tag{13}
\]

The first two inequalities are checked in
`midpointRealSkip_forces_residual_le_seamSupportCard`; the last is checked in
`midpointRealSkip_forces_seamRemainder_lt_rank`.  Thus the midpoint route now
lands inside the existing last-non-right-ancestor analysis of row-small seam
states, but in the much thinner support-cardinality cell.

The exact disposable producer selected by this reduction is

```text
SeamRemainderCardGapFromEight:
  for every d >= 8, card(seamGreedyWord d) + 2 <=
                    seamIntegerGreedyRemainder d.
```

Lean theorem
`midpointRow_realTake_of_seamRemainderCardGapFromEight` proves that this
producer excludes every mature midpoint mismatch.  The producer itself is
not asserted.

The forced-word mode of `half_midpoint_tail_bridge_lab.py` independently
rebuilds the integer-greedy seam word at every rank.  Through rank 2000 its
exact receipt is:

```text
positive seam remainders: 1998 / 1998
card-gap failures: only d=7, with E=3 and c=3
minimum E-c-2 for d>=8: 260 at d=8
minimum by incoming branch:
  middle: 260 at d=8
  right:  535 at d=9
  upper:  386 at d=14
incoming upper / middle / right branches: 486 / 486 / 1025
positive second-shell certificates: 0
maximum second-shell surplus: -1 at d=7
```

Rank `7` is not a counterexample: it is the known small base cell, and the
real decision there is a take.  The scan is only a discriminator for (13),
not an induction over all ranks.

One further tempting shortcut was falsified on the same forced words.  After
an upper reset followed by `k` right branches, the exact cylinder implies a
congruence modulo `4^k`.  That congruence alone does not exclude the thin
cell: through rank 2000 it already has ten false danger alarms, first at
rank 58 (`k=3`, residue `11`, support cardinality `28`).  Any proof must use
the ordered reset/pulse geometry, not merely the terminal residue class.

The surviving route is therefore exact and narrower than the old row-scale
upper-reset band: prove that the base-four reset-and-pulse cylinder never
enters its top window of width `c_d+1`.  Middle successors already have a
row-scale lower bound; the unresolved work is to retain support cardinality
through an upper reset and its following right run, instead of replacing the
exact affine pulse packet by the former coarse width `2(d+k)`.  Establishing
that support-sensitive cylinder escape would prove
`SeamRemainderCardGapFromEight`, eliminate every mature midpoint mismatch,
and leave only the finite base rows in the quotient-prefix comparison.

## The upper obstruction pulls back to a middle ancestor

The upper-reset window is now known not to be an independent local event.
Let `s` be a late upper-reset source, let `d` be the largest false rank of
its seam word, and let `k` be a following right length for which
`s+k <= 2d+1`.  Put

\[
 a=2d+1-s,
 \qquad
 Q_k=R_{d+1}-2^{d+1}-4+2^{a-k}-2^{a+1}.
\]

The fixed-support transport identity gives the exact division-free
pullback

\[
 \bigl(2^{s-k+1}-E_s\bigr)+C_{d,s}
   =4^{s-d}Q_k,                                      \tag{14}
\]

where `E_s` is the upper reset charge and `C_{d,s}` is the complete ordered
fixed-support pulse charge between the earlier row and `s`.  No pulse term
has been bounded or discarded.  Lean checks (14) in
`exists_backwardCriticalDistance_pullback_of_lateLargestFalse`.

The future right length is now completely separated from the earlier
coordinate:

\[
 Q_k=Q_0-2^a+2^{a-k}.                                \tag{15}
\]

This is Lean-checked by
`pullbackCoordinate_eq_base_sub_dyadicStaircase`.  Thus the remaining danger
is a linear-width interval above one explicit dyadic staircase, at the
strictly earlier middle scale.

Taking `k=0` in (14), positivity of the current upper cylinder forces

\[
 2^{d+1}+4+2^a\le R_{d+1}.                           \tag{16}
\]

The predecessor at rank `d` cannot be upper, because an upper predecessor
would give `R_{d+1} <= 2^{d+1}`.  It is therefore middle.  Moreover, for
`s>=13`, lateness gives `a>=6` and `d<=2a`; hence
`4d <= 8a <= 2^a`.  Combining (16) with the exact middle recurrence proves

\[
 d\le R_d.                                           \tag{17}
\]

The full suffix between `d` and `s` consists of actual right branches, not
merely a support pattern visible at the endpoint.  Transporting (17)
through that middle/right block gives the all-depth source barrier

\[
 2^s+s\le R_s.                                       \tag{18}
\]

The proof-bearing declarations are
`lateUpperReset_previousRemainder_ge_dyadicBarrier`,
`lateUpperReset_previousProducer_isMiddle`,
`lateUpperReset_previousMiddleRemainder_ge_row`,
`seamRightBranch_of_fullSuffix`, and
`lateUpperReset_sourceRemainder_ge_expBarrier`.

The exact audit through rank 2000 completes 485 upper/right blocks.  Its two
small pullback coordinates occur at sources 5 and 13; neither source is in
the late-largest-false regime.  Every audited late block has a preceding
upper block ending at its middle source, every late predecessor is middle,
every late `Q_k` clears the endpoint support cardinality plus two, and no
upper/right run reaches the two-thirds crossing.  These are mechanism
selectors, not finite proofs.

One natural induction was decisively falsified: `Q_k` is not monotone along
the chain of upper blocks (there are 86 strict-growth failures through rank
2000).  The surviving proof target is therefore quantitative rather than
monotone: preserve a lower barrier for the coupled upper-deficit and
middle-excess coordinates strong enough either to keep `Q_k` above the
support-cardinality window or to prove `LargestSkipLateStepSocket`.  The
latter socket already has a Lean-checked fan-in directly to
`(1/2) in mersenneAchievementSet`; proving it would close the half endpoint
without a finite-computation argument.
