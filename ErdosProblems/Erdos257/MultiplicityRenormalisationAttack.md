# Multiplicity renormalisation of Lambert coefficients

This audit asks whether the rational Lambert coefficient rungs can be pushed
to Boolean coefficients by an exact local rewrite. It records what the
near-carry does, where its defect goes, and why the first nontrivial defect
already contains the live `1/21` problem. No Lean theorem is added here.

## 1. Exact local identities

Put `w_d = 1/(2^d-1)`. For every `d >= 2`, elementary rational arithmetic gives

```
delta_d = 1 / ((2^(d-1)-1)(2^d-1)),
2 w_d = w_(d-1) - delta_d,                                  (A)
w_(d-1) = 2 w_d + delta_d.                                  (B)
```

Thus the apparent carry `2 w_d -> w_(d-1)` is not value preserving: reduction
of a multiplicity two creates a *negative* defect. The positive orientation
(B) preserves nonnegativity but increases the coefficient at `d` from one to
two and appends a new positive defect. It is an expansion, not Booleanisation.

The defect is indeed concentrated at about double scale. With
`x=2^(d-1)`, comparison of denominators gives, for `d >= 3`,

```
w_(2d-1) < delta_d < w_(2d-2).                              (C)
```

So the ordinary greedy expansion of `delta_d`, if it survives, first takes
the index `2d-1`. This is only a *location* statement. It does not provide a
Boolean expansion of the remaining defect.

There is a second exact multiplicity identity for every `a,k >= 1`:

```
w_a = (1 + 2^a + ... + 2^((k-1)a)) w_(ka).                  (D)
```

It follows from divisibility of `2^a-1` into `2^(ka)-1`. It can collapse a
very specially divisible coefficient at `ka`, but the forward direction
explodes a Boolean coefficient into many copies. It supplies no general
coefficient reduction.

## 2. The immediate `1/21` barrier

The first nontrivial defect is not merely similar to the prescribed rational:

```
delta_2 = 1/3 = w_2,
delta_3 = 1/21.
```

Consequently any positive Boolean completion of the rewrite at `d=3` would
already be an infinite Boolean Mersenne support of rational value `1/21` (a
finite completion is separately excluded in the current corpus). A generic
rewrite rule that claims to materialize every `delta_d` into stabilizing
Boolean bits therefore solves the live rational Boolean-subsums problem at
its first nontrivial instance. It is not an auxiliary bookkeeping step.

More precisely, if `B_3` has value `delta_3`, then (B) is the exact identity

```
w_2 = 2 w_3 + value(B_3).
```

The reverse coefficient-reducing use requires an already-present copy of
`B_3` to consume. Without that copy it creates a signed deficit; with it, the
rewrite has assumed the desired Boolean representation.

## 3. Exact computational audit

[`multiplicity_renormalisation_audit.py`](../../scripts/multiplicity_renormalisation_audit.py)
verifies (A) using `Fraction`, then runs the exact unrestricted greedy
algorithm on `delta_d`. A residual is declared fatal only when it is at least
the rational upper bound `2 w_(n+1)` for the full tail after `n`, justified by
`mersenneTail_le_two_mul_weight`
([`GreedyAchievementSet.lean:154-176`](../../Erdos257PeriodNoncollapse/GreedyAchievementSet.lean#L154)). No decimal arithmetic is used.

Command and receipt:

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/multiplicity_renormalisation_audit.py --max-d 24 --depth 512
```

The script verifies (A) for every `2 <= d <= 24`. It finds no certified fatal
gap through depth 512 for `d=3,...,24`; this is explicitly **not** evidence
of membership. At `d=3` it records `delta_3=1/21`, first greedy index `5`,
and 268 selected indices through depth 512. The output uses exact
fraction/bit-length/SHA-256 receipts for large residuals. `d=2` terminates
exactly at the singleton `{2}`.

This computation kills neither `delta_3` nor the rewrite proposal by itself.
Its value is diagnostic: it makes clear that a positive repair does not stay
finite or local, and it encounters the already-live rational target.

## 4. Interaction with the Lambert rungs

The formal source proves the signed Möbius rung
`sum mu(d) w_d = 1/2`
([`MersenneLambertLadder.lean:586-595`](../../Erdos257PeriodNoncollapse/MersenneLambertLadder.lean#L586)) and the positive totient rung
`sum phi(d) w_d = 2` ([`572-585`](../../Erdos257PeriodNoncollapse/MersenneLambertLadder.lean#L572)). Applying (B) coefficientwise to either is not a convergent Booleanisation:

* It moves mass one step *down* while doubling multiplicities one step up.
  The total defect has positive boundary mass; it cannot simply be discarded.
* Applying the coefficient-reducing orientation (A) makes a signed defect at
  each rewritten location. A positive Boolean limit exists only after every
  such defect has itself been resolved.
* Repeated defects begin near the doubled locations by (C), but their later
  Boolean digits are globally determined. Coordinatewise stabilization would
  require a proof that all these globally coupled defect expansions exist and
  are compatible. The `d=3` instance already shows that this is at least as
  strong as constructing `1/21`.

The primitive conductor rung does not supply the most natural prime-wise
divisibility mechanism. Its coefficient at an odd prime is `p-2`, and the
source proves it is not divisible by `p` (`primWeight_prime_dold_defect`,
[`MersenneLambertLadder.lean:327-351`](../../Erdos257PeriodNoncollapse/MersenneLambertLadder.lean#L327)). Thus a naive prime-fold divisor-coordinate compression is unavailable at the basic prime coordinates. This does not rule out every possible nonlocal integer relation.

### An actual infinite multiplicity-two rational input

[`MultiplicityTwoRationalConstruction.md`](MultiplicityTwoRationalConstruction.md)
now supplies what the signed and high-multiplicity rungs did not: for every
rational `s` in `(26/21,2)`, there are continuum-many pairs of infinite
Boolean supports `B,C` with

```text
sum_d (1_B(d)+1_C(d)) w_d = s,
```

so the combined coefficient sequence is nonnegative and lies in `{0,1,2}`.
In particular this holds at `s=3/2`, with a proved convolution-mass lower
bound `11/42`.  The result follows from the measure-one achievement set and
its complement symmetry, not from a bounded feasibility horizon.

This strengthens the input side of the present attack but leaves its verdict
intact.  Applying the local rule to each double coordinate still creates the
positive defects above, and the first nontrivial defect is still `1/21`.
Thus the remaining question is sharper: can the *correlation between the two
Boolean codings in the positive-measure overlap* globally absorb those
defects?  Atomwise independent rewriting cannot see that correlation and
remains blocked exactly as before.

## Verdict

No value-preserving, positivity-preserving local rewrite has been found that
drives arbitrary Lambert multiplicities to `{0,1}` while pushing only harmless
defects to doubled indices. The two exact orientations have complementary
failures:

| Rewrite | What it preserves | Failure |
|---|---|---|
| `2w_d -> w_(d-1)-delta_d` | low-index multiplicity reduction | creates a negative defect |
| `w_(d-1) -> 2w_d+delta_d` | positivity and value | increases multiplicity and leaves a positive defect |
| `w_a -> (sum 2^(ja))w_(ka)` | exact value | multiplicity explosion; inverse requires exceptional divisibility |

The route remains live only in the substantive sense: an explicit globally
compatible Boolean resolution of the `delta_d` defects would yield a rational
Boolean support. It has not produced one. The local renormalisation mechanism
does not bypass the boundary problem; at `d=3` it is exactly that problem.

## 5. New exact boundary-integer calculation for the `delta_3=1/21` orbit

This is a calculation in the *actual greedy correction prefix* for `1/21`,
not in an arbitrary quotient row.  Let `a_d` be its greedy Boolean digit,
let

```
B_K = sum_(d<=K) a_d 2^(K-d),
P_K = B_K/2^K,
r_K = A_K/Q_K  (in lowest terms),
```

and put `U_K = 4^K(P_K+r_K)`.  Each denominator used to form `r_K` is odd:
it is `21` or one of the `2^d-1`.  Hence `Q_K` is odd (indeed it divides the
corresponding finite LCM).  This is precisely the finite-prefix data behind
`targetGreedyDyadicPrefix` and `greedyMersenneRemainder`
([`BooleanMobiusCarry.lean:3542-3550`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L3542),
[`GreedyAchievementSet.lean:1015-1029`](../../Erdos257PeriodNoncollapse/GreedyAchievementSet.lean#L1015)).

The correction window in the formal development is

```
I_K = [P_K+r_K-eta_K, P_K+r_K],
```

where `eta_K=mersenneCorrectionTail K`
([`BooleanMobiusCarry.lean:3941-3947`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L3941)).
The proved strict bound `eta_K < 2^(-(2K+1))`
([`HalfCutLocator.lean:52-76`](../../Erdos257PeriodNoncollapse/HalfCutLocator.lean#L52))
implies `4^K eta_K<1/2`.  Therefore, if this scaled interval contains an
integer at all, it contains exactly one and it has the closed form

```
q_K = floor(U_K)
    = 2^K B_K + (4^K A_K-rho_K)/Q_K,                         (E)
rho_K = least nonnegative residue of 4^K A_K modulo Q_K.     (F)
```

This is an exact Euclidean-division identity, not an approximation to the
tail.  The tail decides only the crossing predicate
`U_K-q_K <= 4^K eta_K`; it does not alter `q_K`.

For every `j>=1`, (E) gives the promised exact residue law

```
q_K = 2^K B_K + Q_K^(-1)(4^K A_K-rho_K)       (mod 2^j).     (G)
```

The inverse exists because `Q_K` is odd.  When `j<=K`, the prefix term drops
out.  Thus the denominator `21` does not by itself control the two-adic
valuation: the residue also contains the accumulated selected-divisor
denominator `Q_K` and the Euclidean remainder `rho_K`.  Any proposed bound
on `v2(q_K)` must constrain that full Boolean/divisor prefix, not merely the
period of `4^K mod 21`.

### Exact computation (evidence, not theorem)

[`correction_window_boundary_audit.py`](../../scripts/correction_window_boundary_audit.py)
implements (E)--(G) with `Fraction`, and certifies the crossing decision by
summing the next `L` corrections exactly.  Its remaining tail enclosure is

```
4^K(eta_K - sum_(K<n<=K+L)(w_n-2^-n)) < 2/(3*4^L).
```

This follows termwise from `w_n-2^-n < 2*4^-n`; it is deliberately an
enclosure, not a floating-point test.  The script asserts both (E) and (G)
at every reported crossing.

Command:

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/correction_window_boundary_audit.py --depth 768 --lookahead 128 --modulus-bits 32
```

The exact run classifies all 768 stages: 258 certified crossings, 510
certified noncrossings, and no enclosure-undecided stage.  On *certified
actual crossings*, it finds

```
K=51:  v2(q_K)=9,
K=349: v2(q_K)=10,
K=373: v2(q_K)=8,
K=383: v2(q_K)=8.
```

So the correction-prefix orbit already falsifies any small universal claim
such as `v2(q_K)<=7` at a crossed window.  The largest valuation among every
upper-endpoint candidate in this finite range is `11` at `K=52`, but that
candidate is not a certified crossing and must not be conflated with the
previous list.

This is **not** a proof that `v2(q_K)` is unbounded, and a finite scan cannot
refute some unspecified larger bound.  What it does rigorously kill is the
idea that the bare denominator `21` makes the boundary integer uniformly
odd, low-valuation, or periodic in the target's period-six residue.  The
exact remaining question is a global restriction on `(B_K,A_K,Q_K,rho_K)`
along the live greedy path; no current theorem supplies one.

## 6. The `delta_3` signed floor law, and three count-based no-gos

The exact relation `delta_3=w_2-2w_3=1/21` has a second consequence that is
independent of the six-step repair recurrence.  Write

```
F_a(N) = floor(2^N/(2^a-1)),
epsilon(N) = 1 if N mod 6 is 2, 4, or 5; otherwise 0.
```

Then elementary division in the six classes modulo `6` gives the exact
integer identity

```
floor(2^N/21) = F_2(N) - 2 F_3(N) - epsilon(N).             (H)
```

It is the floor-level form of `1/21=1/3-2/7`, so the apparently harmless
defect `delta_3` has a forced *signed* quotient ancestry.  It is not the
existing recurrence for the defect.

Let `A` be the actual greedy support for `1/21`.  Swapping the finite divisor
sum in the binary prefix gives

```
binaryCoeffPrefixNumerator(supportCoeff A,N)
  = sum_(a in A, a<=N) F_a(N).
```

The source identifies `supportCoeff A(n)` as the count of selected divisors
([`BooleanMobiusCarry.lean:55-92`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L55))
and gives the recursive prefix numerator
([`1182-1191`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L1182)).
Together with the formal definition of the natural defect
([`1717-1757`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L1717)),
(H) yields the exact alternate formula

```
Q_N = F_2(N) - 2 F_3(N) - sum_(a in A, a<=N) F_a(N) - epsilon(N).  (I)
```

Formula (I) is the strongest direct transport supplied by `delta_3`: it
exposes the two negative charges, `-2F_3` and the live selected-divisor load.
Thus it does **not** make `Q_N` a nonnegative skipped-ancestor energy.  The
following exact counterexamples delimit several tempting repairs of that
idea.

* No representation `Q_N=E_N+c_(N mod 6)` with `E_N` a cumulative
  nondecreasing nonnegative count can hold: `Q_19=2` but `Q_25=1`, while
  `19=25 (mod 6)`.
* The three counts of selected indices in the residue classes modulo `3`,
  even together with `N mod 6`, do not determine `Q_N`: no greedy index is
  selected from 94 through 99, so the entire selected prefix and all three
  counts agree at 93 and 99, yet `Q_93=1` and `Q_99=2`.
* The natural six-bit suffix state is insufficient: stages 40 and 94 have
  the same `N mod 6` and the same final six greedy bits, but `Q_40=0` and
  `Q_94=1`.

These are targeted no-gos, not a claim that no richer potential exists.  In
particular, they do not rule out a state retaining divisor labels or a growing
boundary history.  They do show that the `delta_3` floor identity alone cannot
replace the repair load by a monotone skipped-count, a mod-3 imbalance, or the
six-step suffix state.  Such a replacement loses exactly the old-divisor
incidences that still change the prefix numerator.

### Exact audit receipt

[`delta_three_defect_audit.py`](../../scripts/delta_three_defect_audit.py)
checks (H) with integer arithmetic and generates the actual greedy orbit with
`Fraction`; it asserts all three counterexamples above.  No floats and no
membership inference are used.

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/delta_three_defect_audit.py
```

This does not improve the conditional `Q_N <= floor(N/6)` endpoint and does
not restate the six-step recurrence.  Its new content is the exact signed
floor transport (H)--(I), plus the demonstrated failure of the three simplest
nonnegative/count compressions of it.
