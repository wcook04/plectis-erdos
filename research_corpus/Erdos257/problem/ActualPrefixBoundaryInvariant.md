# The actual-prefix boundary invariant at `1/21`

Status: exact theorem-discovery note, 2026-08-20.  The deductions below have
not yet been added to Lean.  They use the actual rational-greedy prefix, not
the horizon-dependent quotient-greedy word.  This distinction removes one
alignment hypothesis but does not by itself exclude the fatal branch.

## 1. A quotient state which is aligned by definition

Let

```text
A   = greedyMersenneSupport(1/21),
D_R = A intersect {2,...,R},
S_R = floor(4^R/21) - sum_(d in D_R) floor(4^R/(2^d-1)).
```

Every finite actual greedy prefix is at most `1/21`.  Therefore `S_R` is a
natural number by
`localPrefixQuotient_le_twentyOneTarget_of_prefix_le`
([`TwentyOneQuotientGreedy.lean:778-800`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L778)).
Unlike `twentyOneEvenQuotientGreedyRemainder R`, this state does not require a
full quotient/rational alignment theorem: its support is the actual prefix by
definition.

Put

```text
p_R = 2 #{d in D_R : d divides 2R+1}
        + #{d in D_R : d divides 2R+2},
t_R = 4(4^R mod 21)/21,
b_(R+1) = 1_A(R+1).
```

The exact quotient recurrences
`localPrefixQuotient_add_two` and `twentyOneQuotientTarget_add_two`
([`TwentyOneQuotientGreedy.lean:729-768`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L729))
give, without any alignment assumption,

```text
S_(R+1) = 4 S_R + t_R - p_R - b_(R+1)(2^(R+1)+1).       (1)
```

The final term uses the exact endpoint quotient
`floor(4^(R+1)/(2^(R+1)-1)) = 2^(R+1)+1`.  Thus the same
affine law found on the eventual aligned branch actually exists at every
rank in an actual-prefix coordinate.  What is lost is the assertion that a
rational skip is also a quotient skip.

## 2. A last skip must already be at quotient supercapacity

Define the signed closed margin

```text
m_R = 2^R - S_R.
```

At every actual selected step, (1) becomes

```text
m_(R+1) = 4m_R + p_R + 1 - t_R.                           (2)
```

The target pulse satisfies `t_R in {0,3}` by
`twentyOneTargetTwoStepPulse_even_cases`
([`TwentyOneQuotientGreedy.lean:2323-2362`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L2323)).
Consequently `m_(R+1) >= 4m_R-2` on a selected step.

**Deduction.** If `L` is a final actual greedy skip, then

```text
S_L >= 2^L.                                                (3)
```

Indeed every step after `L` is selected.  If `m_L >= 1`, set
`V_R=3m_R-2`.  Then (2) gives `V_(R+1) >= 4V_R`, while nonnegativity of
`S_R` gives `m_R <= 2^R`.  The resulting lower growth like `4^(R-L)` is
incompatible with the upper growth like `2^R`.  Hence `m_L <= 0`, which is
(3).

This removes the alignment mismatch in the earlier conditional last-skip
potential.  It does **not** prove membership: a rational greedy skip can be
a quotient-only take after floors are applied.  The remaining local event is
now exact:

> a final real skip must be the first skipped rank whose actual-prefix
> quotient state is saturated or strictly supercapacity.

Ruling out that event would force cofinally many skips and hence membership
by the existing cofinal-skip endpoint.

## 3. Exact identification with the Lambert defect plus the upper word

Let `Q_N=twentyOneGreedyDefect N` and let

```text
H_R = sum_(R<a<=2R, a in A) 2^(2R-a)
```

be the literal binary numeral of the actual support in the upper half of the
row.  Expanding each quotient as a finite geometric series and interchanging
the finite divisor sums gives

```text
S_R = H_R + Q_(2R).                                        (4)
```

This is the missing direct dictionary between the quotient state and the
denominator-21 Lambert defect.  It is also visible from the definitions of
`twentyOneGreedyDefect`
([`BooleanMobiusCarry.lean:1718-1730`](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L1718))
and `localMersenneQuotient`
([`BooleanMobiusLocalRepair.lean:20-22`](../../Erdos257PeriodNoncollapse/BooleanMobiusLocalRepair.lean#L20)).

If `L` is a final skip, then every rank `L+1,...,2L` is selected, so

```text
H_L = 2^L-1,
S_L = 2^L-1+Q_(2L).                                        (5)
```

Combining (3) and (5) yields the necessary condition

```text
Q_(2L) >= 1.                                               (6)
```

Moreover `Q_(2L)=1` is exactly saturation and `Q_(2L)>=2` is strict
supercapacity.  Thus the one-third suffix/defect phenomenon and the first
quotient escape are not merely analogous: at a hypothetical final skip they
are the same integer.

## 4. What this changes, and what it does not

The exact common mechanism can now be stated without an eventual-alignment
qualification:

```text
actual Boolean upper word H_R
        + Lambert defect Q_(2R)
        = actual-prefix quotient reservoir S_R.
```

The Boolean suffix consumes the first `2^R-1` units.  Any remaining Lambert
defect is precisely the supercapacity charge.  On an all-selected tail that
charge follows the expanding affine direction; the period-six target pulse
cannot recover it after escape.

This is stronger than another equivalence of membership predicates, but it
is not a solution.  The decisive arithmetic statement is now one of the
following genuinely local exclusions:

* no actual skipped rank `L` can have `S_L >= 2^L`; or
* every skipped `L` with `Q_(2L)>=1` forces a later skip; or
* the saturation case `Q_(2L)=1` and the strict case `Q_(2L)>=2` are both
  incompatible with the exact reduced-residual window at a final skip.

The existing adjacent-gcd and numerator-product theorems at a final skip
([`TwentyOneQuotientGreedy.lean:3865-4334`](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L3865))
are the natural arithmetic inputs for the last alternative.  No implication
from those theorems to the exclusion above is presently proved.

## 5. A separate construction lesson: the Witt collision

For the rational defect

```text
delta_d = 1/((2^(d-1)-1)(2^d-1))
```

put `B=2^d`.  Writing an exponent as `n=kd-j` gives the exact atom

```text
1/(2^(kd-j)-1) = sum_(ell>=1) 2^(j ell) B^(-k ell).         (7)
```

Meanwhile

```text
delta_d = sum_(k>=2) (2^k-2) B^(-k).                       (8)
```

Equations (7)-(8) turn positive Booleanisation into a big-Witt ghost-coordinate
problem.  Before exponent labels wrap modulo `d`, the degree-`k` residual is
obtained by subtracting all proper-divisor power sums from `2^k-2` and taking
its binary mask.  This exactly predicts the initial blocks seen in the
`delta_d` greedy computations.

It does not give a construction for fixed `d`: the masks have unbounded bit
length (at prime `k` every bit `1,...,k-1` occurs), so labels `j>=d`
eventually represent exponents already represented by earlier pairs.  The
resulting diagonal collisions create multiplicity greater than one.  This is
an exact structural reason the attractive formal defect expansion ceases to
be Boolean, not a numerical failure of depth.

## 6. Adversarial verification of the prefix bridge

The previous attempted correction was itself incorrect: it treated the upper
word as a Boolean support numerator.  The definition of
`binaryCoeffPrefixNumerator` uses `supportCoeff A`, so a rank can contribute
with multiplicity equal to the number of its divisors in (A).

Let

\[
 C_{2R}=\operatorname{binaryCoeffPrefixNumerator}(\operatorname{supportCoeff}A,2R).
\]

Expanding the divisor count and swapping the finite sums gives

\[
 C_{2R}=\sum_{d\in A,\,d\le R}
       \sum_{kd\le2R}2^{2R-kd}
       +\sum_{d\in A,\,R<d\le2R}2^{2R-d}
     =\operatorname{localPrefixQuotient}(D_R,2R)+H_R.
\]

The repeated geometric terms occur in both (C_{2R}) and the local quotient
and cancel.  Therefore the original identity

\[
 S_R=H_R+Q_{2R}
\]

is exact.  At (R=5), the actual greedy prefix is
\(A\cap[2,10]=\{5,7,8,9,10\}\).  In particular,
\(\operatorname{supportCoeff}A(10)=2\), from (5\mid10) and (10\mid10).
Thus

\[
 C_{10}=2^5+2^3+2^2+2+2=48,
 \qquad Q_{10}=48-C_{10}=0,
\]
\[
 H_5=2^3+2^2+2+1=15,
 \qquad S_5=48-33=15=Q_{10}+H_5.
\]

This explicitly falsifies the proposed counterexample and confirms that the
coefficient-versus-membership distinction is load-bearing.

At a hypothetical final skip (L), the all-selected interval gives
\(H_L=2^L-1\), so \(S_L\ge2^L\) implies exactly

\[
 Q_{2L}\ge1.
\]

The existing carry-growth estimate has the form

\[
 Q_{2L}+1<2^L(2\sqrt L+7).
\]

This is compatible with (Q_{2L}=1) and therefore supplies no contradiction,
congruence, or denominator obstruction by itself.  The repeated-term sum may
be used only inside the coefficient numerator/local-quotient identity above;
after cancellation it cannot distinguish saturation from strict escape.
