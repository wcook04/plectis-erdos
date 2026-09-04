# Twenty-one saturation arithmetic attack

This note attacks the single transition from exact saturation to permanent
escape in the denominator-21 quotient row. It keeps the exact quotient and
divisor arithmetic separate from finite computation. No Lean edit or kernel
invocation was used.

## 1. Exact quotient identities

At even depth M = 2R, the local rank-d quotient is

    Q_R(d) = floor(2^(2R) / (2^d - 1)).

The geometric identity is exact:

    Q_R(d) = sum_{k >= 1, k*d <= 2R} 2^(2R-k*d).

Indeed, divide the finite geometric expansion of 2^(2R)/(2^d-1) into
integral terms (k*d <= 2R) and a remainder strictly below one. The quotient
word is therefore a finite Lambert/geometric word, not an opaque floor.

The target is T_R = floor(4^R/21). Since 2^6 = 1 modulo 21,

    4^R mod 21 = 1, 4, 16 according as R mod 3 = 0, 1, 2.

Consequently the exact two-step target pulse is

    floor(4*(4^R mod 21)/21) = 0, 0, 3

in those three residue classes. This is precisely
`twentyOneTargetTwoStepPulse_even_eq_three_iff`; the period-six statement is
`two_pow_six_mul_mod_twentyOne`.

For a finite quotient support D, the two-step lift is

    localPrefixQuotient(D, 2R+2)
      = 4*localPrefixQuotient(D,2R)
        + 2*#(d in D : d divides 2R+1)
        + #(d in D : d divides 2R+2).

The exact source names are `localPrefixQuotient_add_two` and
`localPrefixTwoStepPulse`. Thus a saturated row s_R = 2^R can cross the next
binary capacity only if the target pulse is 3 and the support pulse is at most
1. The theorem `twentyOneSaturatedBoundary_crosses_iff_sparsePulse` already
formalizes this reduction.

## 2. What crossing forces, and why it is an ancestor statement

If R = 3a+2, then

    2R+2 = 6(a+1).

Both a+1 and 2(a+1) divide this endpoint. Therefore a crossing row with
support pulse at most one omits at least one of these two ancestors. This is
exactly `twentyOneSaturatedBoundary_crossing_forces_ancestor_hole`.

The obstruction is not a mysterious residue condition: it is a two-point
ancestor closure condition at scale R/3. Any proof that saturation cannot cross
must establish, for every sufficiently large R congruent to 2 modulo 3, that
both ranks a+1 and 2(a+1) occur in the canonical quotient word (or in the
aligned real greedy word).

The geometric quotient formula explains the shape of this requirement. The
rank a+1 quotient contains all geometric terms 2^(2R-k(a+1)); its first
omitted term is already on the same one-third scale as the endpoint pulse.
Möbius inversion does not remove the issue: if c(n) is the divisor coefficient,
then the Boolean support is recovered by

    1_A(n) = sum_{d|n} mu(d) * c(n/d).

It translates the ancestor hole into a Boolean condition, but supplies no sign
or valuation inequality forcing the condition.

## 3. Exact adversarial computation

I ran the descending integer-greedy quotient with exact integers for
2 <= R <= 800. The remainder defect was recorded as

    Delta_R = s_R - 2^R.

There were no exact saturations and no crossings at this range. The first
values are:

| R | R mod 3 | Delta_R | target pulse | support pulse |
|---:|---:|---:|---:|---:|
| 2 | 2 | -4 | 3 | 0 |
| 3 | 0 | -5 | 0 | 0 |
| 4 | 1 | -4 | 0 | 0 |
| 5 | 2 | -17 | 3 | 0 |
| 6 | 0 | 66 | 0 | 0 |
| 7 | 1 | 263 | 0 | 0 |
| 8 | 2 | 1051 | 3 | 1 |
| 9 | 0 | 4205 | 0 | 2 |
| 10 | 1 | 16819 | 0 | 1 |
| 11 | 2 | 67273 | 3 | 2 |
| 14 | 2 | 4305464 | 3 | 2 |
| 17 | 2 | 275549685 | 3 | 5 |

The only rows where the ancestor closure test fails after R=2 are R=5, 8,
11, and 14; from R=17 through the tested range, the canonical quotient word
contains both a+1 and 2(a+1) whenever R=3a+2. This is a discovery signal,
not a proof. It is also exactly the kind of finite pattern that must not be
promoted to a theorem without a quotient-floor argument.

The small exceptions matter: a finite modulus cannot simply assert that the
ancestor pair is always present. The pair is absent at R=8, 11, and 14 even
though all have the same target-pulse residue R mod 3 = 2.

## 4. Modular and 2-adic candidates killed

### Candidate A: a modulus rules out saturation

False in the strongest possible sense. The saturation equation is an equality
between a floor-generated greedy remainder and 2^R. Reducing modulo any fixed
m sees only finitely many residues of the target and quotient terms, while the
number of geometric terms and their carries grows with R. The period-six target
pulse class survives every modulus compatible with 2^6 = 1 mod 21.

### Candidate B: R mod 3 = 2 itself rules out crossing

False. It is exactly the *necessary* residue for crossing, because it creates
the target pulse 3. The first possible crossing rows R=2,5,8,11,14 all lie in
this class; what changes is the ancestor pulse, not the target residue.

### Candidate C: the 2-adic valuation of Delta_R is bounded or periodic

False on the exact scan. For R = 3a+2 the valuations of |Delta_R| at
R = 14, 26, 56, 62, 68 include 3, 2, 3, 7, 5, while many neighboring rows
have valuation zero. There is no stable valuation class tied to R mod 3 or
mod 6. The valuation is controlled by the accumulated quotient word, not by
the target period alone.

### Candidate D: Möbius inversion forces the missing ancestor

False without an independent positivity/selection input. Möbius inversion is
exact and recovers Boolean support from divisor coefficients, but its terms
have alternating signs. It can certify that a candidate coefficient vector is
Boolean; it cannot force c(a+1) or c(2(a+1)) to be nonzero from the target
floor identity alone.

## 5. Best surviving invariant

The strongest surviving arithmetic invariant is the following conditional
ancestor-closure statement:

> For all sufficiently large R = 3a+2, the canonical quotient-greedy word
> contains both ranks a+1 and 2(a+1). Then exact saturation cannot cross, by
> `twentyOneSaturatedBoundary_crossing_forces_ancestor_hole`.

This is materially sharper than “a finite check finds no saturation”: it names
the two exact geometric quotient inequalities that must be proved. A route to
it would compare the quotient at rank a+1 with the sum of all selected ranks
above it, using

    floor(4^R/(2^(a+1)-1))
      = sum_{k(a+1)<=2R} 2^(2R-k(a+1)),

and then descend once to rank 2(a+1). The needed strict margins are integer
floor inequalities, so a proof could plausibly be obtained by a finite residue
analysis plus a monotone geometric tail bound. The current corpus has the
generic strong-gap theorem `localMersenneWeights_two_mul_strong_gapDominates`,
but not this specific ancestor-inclusion theorem.

## 6. Boundary of the attack

Established here:

* exact geometric quotient and two-step pulse identities;
* exact period-six target residues;
* crossing implies R=3a+2 and an ancestor hole;
* modular, valuation, and bare Möbius obstructions are insufficient;
* exact computation identifies R>=17 ancestor closure as the best finite pattern.

Still open:

* proving canonical inclusion of both ancestor ranks for all large R;
* transferring that inclusion across full rational alignment;
* excluding saturation itself, rather than only excluding a saturated crossing.

The arithmetic wall has therefore narrowed to one concrete statement: prove
eventual one-third/two-thirds ancestor closure for the quotient-greedy word.

## 7. Cross-coordinate audit: ancestor closure versus 2-adic boundary forcing

The proposed ancestor predicate is a quotient-row property. Write

    AC(R) := R = 3a+2 and (a+1 in D_R and 2(a+1) in D_R),

where D_R is the canonical quotient-greedy support at depth 2R. It is exactly
the negation of the ancestor-hole conclusion needed to rule out a saturated
crossing.

The correction-window predicates are different objects. In
`GreedyAchievementSet.lean`, `dyadicBoundary_cancel_powTwo` reduces a boundary
numerator 2^v*q over the 4^K grid to dyadic depth 2K-v. The theorem
`crossedBoundary_forceDepth_gt_iff` says that strict amplification beyond K is
equivalent to v < K-1. In `BooleanMobiusCarry.lean`,
`correctionBoundary_large_valuation_forces_empty_doublingBlock` and
`correctionBoundary_valuation_lt_of_mem_doublingBlock` turn that valuation
bound into an empty-block statement. The left/right orientation theorems then
add the exact endpoint alternatives:

* `correctionBoundary_left_valuation_lt_or_singleton_doublingBlock`: either
  v < K-1 or the block is the singleton `10...0` fringe;
* `correctionBoundary_right_amplifies_or_longSelectedRun`: either v < K-1 or
  the whole terminal block is selected.

These statements concern a support prefix numerator at depth 2K. AC(R)
concerns two quotient bits at ranks approximately R/3. There is no definition
identifying their K, boundary numerator, or orientation.

### One genuine implication

AC can feed the valuation theorem only after an additional boundary equation is
provided. If R=3a+2 and AC(R), choose K=a+1. Then 2K=2a+2 is one of the
selected ancestors, so any *actual* shifted-boundary equation whose
doubling block is `(K,2K]` has a support hit. Under the hypotheses of
`correctionBoundary_valuation_lt_of_mem_doublingBlock`, this yields

    v < K-1,

and hence strict forcing-depth amplification by
`correctionBoundary_forceDepth_gt_of_mem_doublingBlock`.

This is only a conditional implication: AC supplies the hit, while the
boundary numerator equation supplies the valuation context. It does not turn
the quotient saturation predicate into a correction-window predicate.

### Why the converse fails

A valuation bound v<K-1 needs only one selected rank in (K,2K]. It does not
force either specific ranks a+1 or 2(a+1), and it says nothing about quotient
greedy selection. For example, the Boolean word with support `{2K}` has
prefix numerator 1 at depth 2K, hence v=0 and strict amplification whenever
K>1, but it has no prescribed ancestor pair. This is an exact counterexample
to valuation-implies-AC, even before imposing a target equation.

The right-boundary predicate is even further from AC: its non-amplifying
alternative is a *long selected run*, whereas AC is only two selected points.
Thus neither left nor right correction classification implies the quotient
ancestor closure.

### Exact adversarial scan

For the canonical quotient rows, I computed AC(R), the valuation of the
depth-2K prefix numerator at K=a+1, and the selected block for
2 <= R <= 80 with R congruent to 2 modulo 3. The first rows were:

| R | K=a+1 | AC(R) | v2(prefix at 2K) | selected ranks in (K,2K] |
|---:|---:|---|---:|---|
| 5 | 2 | false | undefined (zero prefix) | none |
| 8 | 3 | false | 0 | {6} |
| 11 | 4 | false | 0 | {6,7,8} |
| 14 | 5 | false | 0 | {6,7,8,9,10} |
| 17 | 6 | true | 0 | {7,8,9,10,11,12} |
| 20 | 7 | true | 0 | {8,...,14} |

The valuation remains zero in the AC rows because the selected terminal block
produces a prefix numerator congruent to 2^K-1, not a highly divisible
boundary numerator. Therefore eventual AC does not empirically imply a large
valuation, nor does a large valuation appear as the mechanism behind AC.

### Surviving cross-coordinate statement

The exact implication worth retaining is:

> Ancestor closure is a sufficient *hit certificate* for strict correction
> amplification only after an independently verified left/right boundary
> equation. The correction valuation then controls amplification, while the
> quotient ancestor pair controls whether the saturated target pulse can cross.

This is a compositional bridge, not an equivalence. It points toward
membership only if the boundary equation is supplied cofinally; otherwise it
merely juxtaposes two consumers. The existing
`twentyOneAlignedSaturatedCrossing_forces_scaled_greedy_skip` theorem makes the
same separation explicit: alignment plus crossing gives a real greedy skip,
but the missing input is still the alignment/ancestor producer.
