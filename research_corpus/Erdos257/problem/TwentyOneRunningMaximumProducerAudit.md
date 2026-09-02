# Denominator-21 running-maximum producer audit

Status: exact downstream reduction, finite seed, record-only equivalence, and
nested-height service bridge formalized and Lean-checked.  The sharper causal
endpoint is also Lean-checked after removing one duplicate upstream theorem.
The all-depth arithmetic producers remain open.

## Why this coordinate is now mandatory

[`DenominatorCancellationAudit.md`](../../../erdos257_hole_geometry/notes/DenominatorCancellationAudit.md)
proves that large reduced denominators in the raw greedy remainder are
structural, not a loose-LCM artifact: every selected rank `d` in the top
dyadic block contributes a cyclotomic factor `Phi_d(2)` which occurs in no
other prefix summand and therefore cannot cancel.  The measured reduced
denominators lose at most a negligible number of bits relative to the LCM
scale.  Consequently a finer estimate in the same remainder/death-window
coordinate cannot recover a denominator-separation proof.  The running
maximum, record increment, and nested-height variables are a genuine
renormalisation, not merely a new notation for the discarded route.

The independent [`MultipleSetGapBound.md`](../../../erdos257_hole_geometry/notes/MultipleSetGapBound.md)
audit supplies the matching combinatorial redirect.  Its proved covering
bound is far from active on the pinned targets, so holes in the multiple set
are not the scarce resource; excess divisor multiplicity is.  The midpoint
quantity used below,

\[
  g_d=f(2d)-f(d),
\]

is exactly such an excess-multiplicity coordinate: it counts the selected
divisors in the new top 2-adic layer of `2d`.  Thus the service route consumes
the cockpit redirect directly, without returning to the structurally
over-resolved raw remainder.

### What transfers from the period/excess lane, and what does not

The new period-position work makes the coordinate selection sharper, but it
does not supply the missing inequality for free.  For a *completed infinite*
rational support, the shift invariant has the positive lattice floor
`Lambda_P >= 1` at multiples of the denominator-21 period, and
`DefectFloorBridge.md` identifies `Lambda_P = Q_P` there.  That implication
cannot be used to prove survival of the greedy support: infinitude of the
support is one of its hypotheses, and for `1/21` it is already equivalent to
the desired conclusion.  Importing the floor into the producer would be
circular.

There is also an unconditional finite-support bridge.  The half-cylinder
pulse register is exactly a dyadically weighted selected-divisor
multiplicity window, and after subtracting the all-ones baseline it
telescopes to a difference of centered Mobius carries.  This is the right
renormalized coordinate, but the exact seam audit finds both signs (523
positive, 37 zero, 45 negative through row 2,500).  Consequently neither
multiple-set hole scarcity nor positivity of a frozen excess window implies
the causal midpoint service.  The completed-support `X(P)` lattice and the
finite frozen seam window must not be conflated.

The surviving noncircular period input is the already-banked exact finite
six-step defect law

\[
 Q_{n+6}=64Q_n+W_{n\bmod 6}
   -\sum_{j=1}^{6}2^{6-j}f(n+j),
\]

where `W` is the fixed cyclic denominator-21 target word.  This is not a new
frontier: `BooleanMobiusCarry.lean` already iterates it into the exact
six-step repair load, restricts the all-rank obligation to slope-danger
ranks, and exposes cofinal safe-or-repaired supply as an open membership
producer.  The translation-invariant contraction already fails at rank 73,
and source-clock/digit-sum reductions lose the old-divisor incidence data.

Accordingly the running-maximum route may use this identity only if it gains
something from the *strict-record midpoint*.  It must extract the endpoint
load `f(d)` while retaining the other five selected-divisor loads and the
live defect.  A bound obtained by first replacing those loads with holes,
ordinary divisor counts, a fixed six-bit suffix, or the completed-support
lattice would repeat an already falsified or circular split.  The genuinely
new admissible statement would be a source-specific six-step load/defect
comparison at strict-record midpoints, not another proof of the recurrence.

The exact identity was already Lean-banked upstream as
`Erdos257PeriodNoncollapse.twentyOneGreedyDefect_add_six`, together with the
weighted load `twentyOneSixStepRepairLoad`, the contraction equivalence
`twentyOneGreedyDefect_add_six_le_iff_repairLoad`, and several checked
membership consumers.  No duplicate local theorem is needed.  The prose
formula above is that existing iterated recurrence, not an additional
empirical claim.

## Coordinate

For the canonical denominator-21 greedy defect `Q_N`, define

\[
H(N)=1+\max_{0\leq k<N}Q_k.
\]

The new Lean module uses the equivalent recursive definition

\[
H(0)=1,\qquad H(N+1)=\max(H(N),Q_N+1).
\]

## Open producer

The sole unproved assumption is

\[
\tag{DRMH} H(2d)\leq 2H(d)\qquad(d\geq0).
\]

This is the inequality that passed every tested doubling pair through rank
2,000,002 in the exact census recorded by
`TwentyOneRecordAncestorInheritance.md`.

## Exact record-only reduction

Define the record-midpoint producer

\[
\tag{RMB}
H(N)<Q_N+1\Longrightarrow
Q_N+1\leq2H\left(\left\lfloor\frac{N+2}{2}\right\rfloor\right).
\]

The antecedent says precisely that `Q_N` starts a new height plateau.  Lean
now proves

```
TwentyOneDefectDoublingHeightBound ↔
  TwentyOneDefectRecordMidpointBound
```

as `twentyOneDefectDoublingHeightBound_iff_recordMidpointBound`.  The forward
direction moves a new plateau to the next doubled midpoint.  The reverse
direction inducts over all horizons and spends `(RMB)` only when a new record
appears.  Consequently DRMH is not an all-pairs proof obligation: it is one
sharp inequality at each strict defect record.

The record-only final endpoint is
`not_universal_of_twentyOneDefectRecordMidpointBound`.

## Exact nested-height service bridge

The phase-neutral doubled-service identity is now Lean-formalized as
`twentyOneEulerMidpointService_identity`.  For every positive `d`, with
`f(n)` the selected-divisor load, it proves

\[
 (f(2d)-f(d))+Q_{2d}
 =2(Q_{2d-1}-Q_{d-1})+Q_d+t_{2d}-t_d
\]

in `Int`, before any record, phase, or asymptotic hypothesis is introduced.
The nested-height producer is packaged in its cancellation form

\[
\tag{NH'}
2(Q_{2d-1}-Q_{d-1})+Q_d\le H(d)+H(d/2)
\]

at even strict-record midpoints.  Lean proves that one such coupled row
implies its required record-midpoint inequality as
`twentyOneRecordMidpointBound_of_nestedHeight_at`.  The proof uses
monotonicity only after the two compensation terms have already been kept
together; it does not assert either of the false additive splits.

The complete source-specific bridge is
`twentyOneDefectRecordMidpointBound_of_nestedHeightService`.  Its inputs are
kept disjoint:

1. `twentyOneDefectInitialRecordMidpointBound`, the proved finite rows through
   rank `19`;
2. `TwentyOneDefectQuarterPhaseRecordLock`, divisibility of every later
   strict-record successor by `4`;
3. `TwentyOneDefectNestedHeightService`, `(NH')` at the resulting even
   midpoint.

The seed is discharged from the exact rational greedy prefix through rank
`20`, certified by `native_decide`; the prefix is
`{5,7,8,9,10,11,13,16,18,20}`.  It proves `Q_N<=1` through rank `18`,
`Q_6=1`, and `Q_19=2`, which closes every initial midpoint row without an
unproved finite assumption.  Consequently the exact finite seed theorem
uses Lean's standard native-decision axiom; the symbolic midpoint identity
and service bridge remain independent of that finite certificate.

The two remaining inputs imply `(RMB)`, hence `(DRMH)`, the `1/21` membership
theorem, infinite support, and the final negation of universal irrationality.
The composed endpoint is `not_universal_of_twentyOneNestedHeightService`.

## Twenty-million-rank named discriminator

The reproducible script
`../../scripts/twenty_one_running_max_deep_audit.py` reuses the rigorously
bracketed block orbit from the independent primorial-producer falsifier.  Its
canonical receipt is
`../../../../state/formal_math/erdos257_period_noncollapse/twenty_one_running_max_deep_receipt.json`.

Through rank `20,000,002` it records:

* `10,000,002` doubling pairs, zero DRMH violations, and only the three finite
  equality seeds `d=4,5,6`;
* maximum observed defect `128` and `56` strict records;
* all `54` strict records after rank `19` have successor divisible by `20`;
* zero violations of the Euler midpoint service inequality and of its sharper
  nested-height form, each with minimum exact margin `1`.

A new named discriminator strips the right side further.  On the actual
record rows the source-specific estimate

\[
  g_d+Q_{2d}\le H(d)+2
\]

has no violation.  More sharply, the three successors `140`, `420`, and
`780` are the only rows where `g_d+Q_{2d}>H(d)`; every one of the `49` later
record rows satisfies the single-height bound `g_d+Q_{2d}<=H(d)`.  This is
strictly stronger than `(NH)` after the finite exceptions and is now emitted
by the canonical deep receipt as a falsifier for a possible source-specific
proof.  It is not asserted all-depth, and the rational control cohort already
warns that comparable one-height laws are not carry-generic.

At a strict record `n=2d-1`, the successor recurrence removes the apparent
future dependence entirely:

\[
 g_d+Q_{2d}=2Q_n+t_{2d}-f(d).
\]

Hence the no-exception `H(d)+2` discriminator is equivalently the causal
midpoint-load inequality

\[
 f(d)\ge 2Q_n+t_{2d}-H(d)-2.
\]

Every term on its left is selected by rank `d`.  This is the current named
analytic clue: a late record must already have paid for itself in the
midpoint's divisor ancestry.  It is strictly a quotient/excess-multiplicity
statement and is not approachable by the cyclotomic denominator estimate.

The Lean module now packages this sharper statement as
`TwentyOneDefectCausalMidpointService` and proves the intended direct bridge:
after the exact finite seed and quarter-phase lock, the `H(d)+2` service gives
`(RMB)` without passing through a separate density estimate.  The named final
consumer is `not_universal_of_twentyOneCausalMidpointService`.  This addition
does not assert the service law; it makes its consequence exact and prevents
future work from re-expanding the same algebraic route.

The receipt also tests the most natural attempt to decouple that ancestry.
Let `tau(d)` be the full divisor count and write `tau(d)-f(d)` for omitted
midpoint divisors.  The exact H-plus-two margin splits as

\[
\begin{aligned}
 H(d)+2-(2Q_n+t_{2d}-f(d))
 ={}& (\tau(d)-2Q_n)\\
    &+\bigl(H(d)+2-t_{2d}-(\tau(d)-f(d))\bigr).
\end{aligned}
\]

The first term has no violation on the `55` even record rows and minimum
zero.  The two tempting support-side substitutes are decisively false:
`2f(d)>=tau(d)` fails on `18` rows with minimum margin `-16`, while the
omitted-divisor budget in the second line fails on `51` rows with minimum
margin `-111`.  Thus even the full divisor envelope cannot be proved first
and combined with an independent density or omission estimate.  The negative
and positive pieces must remain coupled through the actual selected ancestry.

The engine made zero undecided decisions.  Its minimum decision margin was
`3,139,869,089` integer units against a rigorous error bracket of `10,760`,
and it independently reproduces the pinned selected count `249,858` at rank
`500,002`.  The receipt also rechecks the old two-million horizon: zero DRMH
violations and the same three equality seeds.

This computation is a named falsifier for DRMH, the record phase lock, and the
two midpoint-service lemmas.  Their finite survival is evidence and
falsification coverage, not proof.

## Validation receipt

The focused build of `TwentyOneRunningMaximumProducer` succeeded after the
finite-seed proof repair, including the exact seed, doubled-service identity,
record-only equivalence, nested-height bridge, membership consumer, and final
counterexample consumer.  The subsequent build after adding the sharper
causal-midpoint endpoint eventually ran.  Lean elaborated the causal bridge
and both final consumers without `sorryAx`.  The build failed only on a
locally duplicated six-step recurrence: the stronger theorem and its
repair-load consumers already existed upstream in `BooleanMobiusCarry`.
That duplicate has been removed and the audit now cites the upstream theorem.
The final focused build and its serialized Lake authority recheck both pass:

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py \
  --jobs 2 ErdosProblems.Erdos257.TwentyOneRunningMaximumProducer
Build completed successfully (3047 jobs).
```

The axiom audit reports no `sorryAx`.  The symbolic causal and nested-height
bridges use only `propext`, `Classical.choice`, and `Quot.sound`; the finite
seed consumers additionally carry the explicitly documented native-decision
axiom for the rank-20 rational prefix certificate.

## Lean-checked consequence chain

Assuming DRMH, the module proves:

1. `H(2^k) <= 2^k H(1)` by dyadic iteration.
2. `H(N) <= 2(N+1)H(1)` by rounding `N` to the next power of two.
3. `Q_N+1 <= 4H(1)(N+1)`.
4. `(Q_N+1)/2^N -> 0`, hence
   `TwentyOneGreedyDefectSubexponential`.
5. `1/21` belongs to `mersenneAchievementSet` by the existing exact
   subexponential criterion.
6. The representing support is infinite: rank 1 is impossible because its
   term is 1, while `finiteErdosSum_ne_one_div_twenty_one` excludes every
   finite support on ranks at least 2.
7. Therefore `UniversalMersenneSubseriesIrrationality` is false.

The original endpoint theorem is
`not_universal_of_twentyOneDefectDoublingHeightBound`; the record-only endpoint
above is equivalent.

## Claim ceiling

No proof of DRMH/RMB, the quarter-phase lock, or nested-height service is
asserted.  The finite seed, doubled-service identity, and every implication
after the two explicitly named all-depth inputs are exact.  Erdős #257
remains open until those two producers (or another sufficient producer) are
proved.  The sharp analytic frontier is `(NH')` together with the
quarter-phase lock; further indiscriminate horizon sweeps do not change the
claim status.
