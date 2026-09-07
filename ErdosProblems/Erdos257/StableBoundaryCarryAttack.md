# Stable boundary data for the carry recurrences

This is an adversarial audit of the stable-manifold idea. It records exact
algebra, current Lean consequences, and counterexamples to overstrong boundary
claims. It does not add a Lean theorem or propose a new invariant.

## 1. The exact two-sided law

Write a binary carry recurrence as

```
u_(n+1) = 2 u_n + b_(n+1),    b_(n+1) = a_(n+1) - c_(n+1).
```

For every `N`, direct iteration gives

```
u_N / 2^N = u_0 + sum_(j=1..N) b_j / 2^j.                  (1)
```

If the weighted forcing series converges, then the boundary number

```
theta = lim_N u_N / 2^N
      = u_0 + sum_(j>=1) b_j / 2^j                         (2)
```

exists. Conversely, *future forcing plus `theta`* gives the inverse-tail
formula

```
u_n = 2^n theta - sum_(r>=1) b_(n+r) / 2^r.                (3)
```

Thus the forward recurrence has a one-real-parameter family of solutions;
the datum at infinity is exactly `theta`. The tempered/stable solution is
unique and is the `theta = 0` member. Equation (3), not positivity of a
forward orbit, is the required two-sided boundary condition.

The base-four fatal recurrence has the same form. If

```
s_(R+1) = 4 s_R + g_R,
```

then, whenever its weighted forcing converges,

```
Theta = lim_R s_R/4^R,
s_R = 4^R Theta - sum_(j>=R) g_j / 4^(j-R+1).              (4)
```

For the fatal aligned `1/21` branch, the exact recurrence is

```
s_(R+1) = 4s_R + targetPulse(2R) - prefixPulse(D_R,2R)
          - (2^(R+1)+1),                                   (5)
```

with the accompanying append of `R+1`; this is a Lean theorem under
`TwentyOneFatalAlignedBranch`
(`twentyOneFatalAlignedBranch_eventually_affine_supercapacity`,
[`TwentyOneQuotientGreedy.lean:5653-5668`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L5653)).

The finite version of (1) is already formalized in base `q` as
`affine_cocycle_telescope` ([`AffineCocycleObstruction.lean:82-93`](AffineCocycleObstruction.lean#L82)). The existing source formalizes the
special case `theta=0`, not the general inverse-tail presentation: a tempered
orbit forces the weighted sum to be minus its anchor
(`affine_cocycle_tsum_eq_neg_anchor`, [`95-109`](AffineCocycleObstruction.lean#L95)).

## 2. What could kill the homogeneous coefficient?

### Positivity: killed

Positivity alone does not select `theta=0`. If `u` solves the recurrence and
`C` is an integer, then

```
u^C_n = u_n + C 2^n
```

has the same forcing and has boundary coefficient `theta+C`. For `C>0`, it
is positive once `u` is bounded below. This is elementary algebra, not a new
Lean result. It has a certified concrete forcing source: the `{2,3}` carry
has exact recurrence and a positive six-cycle
([`BooleanMobiusCarry.lean:1082-1122`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L1082)). Applying the displayed homogeneous shift preserves its recurrence.

This counterexample changes the initial anchor `u_0`; it therefore does not
contradict uniqueness after both future forcing and an initial anchor are
fixed. It shows precisely that **forward positivity supplies no boundary at
infinity**.

### Boolean quotient/Möbius ancestry: killed

The same shift satisfies

```
2u^C_n-u^C_(n+1) = 2u_n-u_(n+1).
```

Hence it has exactly the same carry quotient and exactly the same Boolean
Möbius transform. In particular, quotient Booleanity cannot see the
homogeneous coefficient. The `{2,3}` quotient is formally recovered as its
support coefficient and its Möbius transform as `support23`
([`BooleanMobiusCarry.lean:1133-1147`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L1133)). This is an algebraic counterexample to using quotient ancestry *alone* to force stable boundary data.

There is an important naming caveat. The Lean structure
`BooleanMobiusCarryCertificate` is called “quotient-only” because it does not
start with a support set, but it additionally includes `initial`, positivity,
the square-root bound, divisibility, and Boolean Möbius quotient
([`BooleanMobiusCarry.lean:763-784`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L763)). It is not merely a Boolean-quotient condition.

### Square-root/subexponential control: survives

For a nonnegative orbit, any upper bound `u_n = o(2^n)` forces `theta=0`
directly from (2); a square-root strip is a sufficient instance. This is not
a prospective theorem: the certificate reconstruction derives tempering from
positivity plus its square-root bound
([`BooleanMobiusCarry.lean:856-891`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L856)), and the canonical `1/21` theorem makes the same implication explicit
([`2943-2954`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L2943)).

So the square-root candidate is mathematically sound but strategically does
not close the problem: present Boolean ancestry does not imply the strip, and
the fatal branch formally has strict supercapacity instead
([`TwentyOneQuotientGreedy.lean:5617-5651`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L5617)).

### A rational or integral arithmetic class for `theta`: killed

Integrality of all finite states gives no contradiction: normalized limits of
integer sequences can be arbitrary real numbers. Even periodic integer
forcing may yield a nonzero rational `theta` after the anchor is chosen. More
importantly, the endpoint-pulse cocycle supplies an irrational weighted
forcing class. The current formal theorem says a *tempered, rationally
anchored* base-four orbit would force its correction stream to have an
irrational weighted value
(`irrational_tsum_correction_of_tempered_branch`,
[`AffineCocycleObstruction.lean:216-255`](AffineCocycleObstruction.lean#L216)).
This obstructs tempering with an eventually periodic/rational correction; it
does not place the nonzero `Theta` of an escaping orbit in a forbidden class.

## 3. Exact status of the fatal branch

The fatal aligned branch already has the forward data needed to state (4):
the finite support and scalar undergo an exact eventual transition
([`TwentyOneQuotientGreedy.lean:5282-5315`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L5282)), and nonmembership forces `s_R > 2^R` eventually
([`5617-5651`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L5617)). It therefore supplies a legal forward escaping orbit, conditional on nonmembership. The existing results do **not** prove convergence of `s_R/4^R`; formula (4) is conditional on weighted summability of its actual forcing. They also do not prove `Theta=0`, nor an arithmetic restriction on `Theta` that contradicts `s_R>2^R`.

This destroys two tempting claims:

1. “Exact Boolean/Möbius reconstruction must eliminate the homogeneous mode.”
   False: quotient data are invariant under homogeneous shifts.
2. “The irrational endpoint cocycle makes the escaping mode impossible.”
   False as currently formalized: it rules out a **tempered** rational-anchor
   integration of the specified forcing, and explicitly leaves escaping
   non-tempered behavior untouched.

## 4. Best surviving cross-representation lemma

Full stable convergence is stronger than the current `1/21` consumer needs.
The sharpest surviving cross-representation statement is instead the following
**open closed-return lemma**:

> Every exact aligned Boolean--Möbius `1/21` trajectory has arbitrarily large
> horizons `R` with `s_R <= 2^R`.

This is genuinely a boundary assertion: it excludes the only forward survivor
of the fatal branch, permanent strict supercapacity, without pretending that
the local recurrence determines its homogeneous coefficient. It is already
decisive: any unbounded sequence of such closed rows yields the cofinal
normalized decay condition
(`twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows`,
[`TwentyOneQuotientGreedy.lean:5551-5570`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L5551)), hence membership by
`one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay`
([`5456-5530`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L5456)).

The two-sided stable condition `s_R/4^R -> 0` remains a sufficient stronger
version. Once tempering and a reconstructed support orbit are available,
`support_fraction_of_temperedCarry` identifies its rational value
([`BooleanMobiusCarry.lean:451-457`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L451)). But the audit found no route from positivity, Boolean ancestry,
or cocycle arithmetic to even the weaker closed-return lemma. The cocycle
argument rejects stable periodic correction rather than the legal escaping
mode.
