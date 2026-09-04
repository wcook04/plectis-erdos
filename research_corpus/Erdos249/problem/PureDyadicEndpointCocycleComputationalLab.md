# Pure-dyadic endpoint-cocycle lab

## Exact analytic coordinate

For the pure-dyadic denominator `2^c`, put

`Q_H = totientBlock(H,c)` and `M_H = 2^H-1`.

When `k` is the nearest integer quotient of `Q_H/M_H`, define the signed
endpoint error

`E_H = Q_H-kM_H`.

The canonical residue `(-Q_H) mod M_H` lies near one endpoint exactly when
`|E_H|` is small.  The block and modulus recurrences give

`E_(H+1) = 2E_H + phi(c+H+1)-k`.

`PeriodMultipleEscape.lean::pureDyadicEndpointError_succ` kernel-checks this
identity.  It changes the structural question: a long Mersenne residue trap is
a totient-letter word whose affine orbit shadows the moving interval
`[-(c+H+1), c+H+1]` while one quotient `k` remains fixed.

## Discriminating computation

`scripts/check_pure_dyadic_endpoint_cocycle.py` uses a single totient sieve and
the exact recurrences for `Q_H` and `M_H`.  It scans `0 <= c <= 1000000`, records
only new delay champions, and checks the affine error recurrence on every
champion word.  Its canonical stop condition is the first bounded scan that
contains a delay strictly above the previous record seventeen and binds the whole
signed word.

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/check_pure_dyadic_endpoint_cocycle.py \
  --max-c 1000000 --max-height 100 --delay-threshold 17 \
  --output state/formal_math/erdos257_period_noncollapse/erdos249_pure_dyadic_endpoint_cocycle_receipt.json
```

## One-way result and new frontier

The exact champion `c=490794` has geometry-clear height `20`.  Its nearest
quotient is fixed at `k=327611`; the signed endpoint error remains within the
moving radius through height `38` and first leaves it at height `39`.  The
post-clearance delay is therefore `19`, decisively eliminating the candidate
universal cap seventeen.  The earlier `c=50490`, delay-seventeen word remains
an explicit regression fixture, so extensions can add champions without
silently changing the established cocycle checks.

The important output is the recurrence, not a new guessed cap.  A successful
proof route must now show that no totient-letter word can shadow this affine
window forever, or classify a nested family that does.  This is strictly more
structured than treating the residues as random modulo growing Mersenne
numbers.  The finite scan does not prove unbounded delay, universal escape, or
irrationality.

## Prime positions force linear excursions

The actual consecutive-totient word has more structure than the pointwise
legal-letter relaxation.  If `p=c+H+1` is prime, then
`phi(p)=p-1=c+H`, so the fixed-quotient cocycle gives

`c+H-k = E_(H+1)-2E_H`.

Consequently

`c+H-k <= |E_(H+1)|+2|E_H|`.

`PeriodMultipleEscape.lean::prime_forces_pureDyadicEndpointError_excursion`
kernel-checks this inequality, and
`exists_late_pureDyadicEndpointError_excursion` supplies such a prime position
beyond every requested height.  Thus bounded, periodic, and more generally
sublinear-error fixed-quotient modes are impossible for the actual word.  A
surviving permanent trap must use linear-size excursions inside the full
moving envelope; it cannot be a bounded perturbation of the constant-two
countermodel.

The checker now records every prime row occurring in a record champion word
and verifies the same adjacent-error inequality exactly.  In the final
`c=490794` champion, the prime argument `490829` occurs at height `35`; its
lower bound and adjacent error budget are both `163217`.  This equality is a
structural certificate from the recurrence, not evidence that finite scanning
settles the all-depth escape question.  The remaining route is narrower:
classify whether linear-envelope prime excursions must eventually cross the
endpoint radius, or whether actual totient correlations can keep alternating
them inside it forever.

## A trapped prime successor forces a directional bottom lock

The next totient letter removes that apparent freedom.  Put
`p=c+H+1` and suppose `p` is prime.  Applying the cocycle at `H` and `H+1`
gives

`E_(H+1)=2E_H+p-1-k`,

`E_(H+2)=2E_(H+1)+phi(p+1)-k`.

If the successor remains below the upper endpoint boundary,
`E_(H+2)<=p+2`, elimination of `E_(H+1)` yields the exact directional
constraint

`4E_H+p+phi(p+1) <= 4+3k`.

`PeriodMultipleEscape.lean::prime_successor_upper_trap_forces_bottom_lock`
kernel-checks this implication.
`exists_late_prime_predecessor_bottom_lock_of_upper_trap` combines it with
unbounded primes: an orbit trapped below the upper boundary at every height
has such bottom-locked prime predecessors beyond every cutoff.  Since
`phi(p+1)>=1`, these predecessors are forced linearly negative as `p` grows
with fixed `k`.  This eliminates every permanent fixed-quotient mechanism
that is not cofinally bottom-locked immediately before large primes.

The checker binds the same inequality to every eligible prime triple in the
record champion trajectories.  Nine prime rows have a still-trapped
successor, and every one has negative pre-prime error; none has a
nonnegative predecessor.  For the final champion (`c=490794`, `p=490829`),
the errors are `E_H=-15877`, `E_(H+1)=131463`, and `E_(H+2)=66195`, with
bottom-lock slack `424636`.  These finite observations are regression
certificates for the theorem-facing mechanism, not the cofinal proof.

The surviving computation is now specific: expand the bottom lock backward
through preceding composite letters and test whether the resulting precursor
cones overlap across prime gaps strongly enough to force an endpoint escape.

## Exact backward cone: one local lock is insufficient

`scripts/check_prime_successor_precursor_cone.py` performs that first
discriminating test without extending the scan horizon.  It starts from the
complete integer interval allowed by the prime-successor bottom-lock inequality
at `p=490829`, inverts

`E_(h+1)=2E_h+phi(c+h+1)-k`

through the fourteen exact preceding totient letters, enforces integrality and
the moving endpoint bound at every layer, and then independently replays every
surviving seed forward.

The cone does not collapse.  It contains exactly 35 errors at the
geometry-clear height `H=20`, ranging from `53685` through `53719`.  Every one
replays inside all fourteen endpoint windows and reaches the terminal
bottom-lock interval; the actual record error `53713` is one of them.  This is
an exact counterexample to the proposed local implication that a single
prime-successor bottom lock, even combined with all exact intervening totient
letters and endpoint constraints, forces a backward lower-boundary crossing.

This eliminates the one-block propagation mechanism rather than merely
reporting a longer finite delay.  A surviving proof must correlate at least
two prime locks, or introduce a cross-gap arithmetic invariant not present in
the current cone.  The finite cone is not an infinite trap and proves neither
universal escape nor irrationality.

## Two locks can determine the seed without forcing escape

`scripts/check_two_prime_lock_precursor_cone.py` tests the next stronger local
mechanism on the `c=349`, `k=167` record word.  Its trajectory has two distinct
prime arguments whose successors remain endpoint-trapped: `359` at `H=10`
and `367` at `H=18`.  The checker starts from the complete geometry-boundary
interval `E_10 in [-360,360]`, replays every integer seed through the actual
totient letters, and intersects the moving endpoint window only through the
successor of each lock.

The first successor leaves 362 seeds, the consecutive range `[-145,216]`.
The second successor collapses that set to the unique seed `E_10=-15`, which
is exactly the record orbit.  Uniqueness does not cause escape: the orbit is
still strictly trapped at `H=19`, where `E_19=-109`, and its minimum endpoint
margin over `H=10,...,19` is 238.

Thus two distinct prime-successor locks, every intervening actual totient
letter, and every endpoint constraint can determine the orbit uniquely
without forcing a crossing.  This is an exact mechanism elimination, not a
longer-horizon audit.  A viable local route now needs at least a third lock;
alternatively it must introduce a genuinely global invariant transported
across prime gaps.  The finite witness is not an infinite trap and proves
neither universal escape nor irrationality.

Replay and freshness check:

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/check_two_prime_lock_precursor_cone.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/check_two_prime_lock_precursor_cone.py --check
```

## Three local locks still leave a complete precursor cone

`scripts/check_three_prime_lock_precursor_cone.py` replaces seed-by-seed
enumeration with the exact affine preimage of every moving endpoint interval.
If `E_H = 2^(H-H0) e + A_H`, the constraint `|E_H| <= c+H+1` is one integer
interval for the geometry-boundary seed `e`; intersecting the intervals is
therefore complete and does not lose non-consecutive seeds.

The first three-lock word occurs already at `c=1858`. Geometry clears at
`H=12`, the fixed quotient is `k=1251`, and the successors of the three
distinct prime arguments `1871`, `1873`, and `1877` all remain trapped. The
complete seed cone contracts as

```text
3743 -> 937 -> 234 -> 15.
```

After the third successor it is the full interval `[-193,-179]`, not an
approximation or a sample. The actual seed `E_12=-189` remains inside it and
reaches `E_20=-741`, still `1138` units from the endpoint boundary.

The shared affine-cylinder checker now certifies the exact finite-prefix
identity behind this survival statement. For any positive-scale affine bands,
an integer seed belongs to their complete pulled-back intersection if and only
if its affine value satisfies every original band. Thus an already observed
endpoint-trapped finite trajectory necessarily supplies a survivor of its own
complete prefix cone. Extending such an observed prefix and then intersecting
only its endpoint bands cannot, by itself, yield an empty-cone contradiction.

This decisively eliminates the proposed local implication that three trapped
prime successors force crossing. It also shows that the earlier two-lock
uniqueness at `c=349` was exceptional rather than a monotone lock-count
phenomenon: adding another local lock need not even determine the seed. The
surviving producer must now use an unbounded/cofinal family of locks with a
genuinely global cross-gap invariant. This does not say that every fixed lock
count admits a trapped word; refuting a new universal fixed-count implication
still requires a witness with that many locks or a separate structural proof.

Canonical generation and replay stop at the first witness:

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/check_three_prime_lock_precursor_cone.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/check_three_prime_lock_precursor_cone.py --check
```
