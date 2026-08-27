# Erdős #1041 for translated quartic quotient fibres

Status: proved analytic case theorem, 2026-08-24.  The new chord-lift metric
kernel and strict endpoint budget are formalized in
`QuarticQuotientFiberCase.lean`.  The four-point radial lemma is attributed to
Venkata Siddharth Pendyala, *A Degree-Four Lemniscate Path Theorem*,
arXiv:2606.24875 (2026), whose local extracted source is consumed below.  This
settles an exact all-scale family in every degree `4q`, `q>=2`; it does not
settle unrestricted Erdős #1041 and makes no novelty or priority claim.

## Source and attribution boundary

The downloaded primary source is Venkata Siddharth Pendyala, *A Degree-Four
Lemniscate Path Theorem*, arXiv:2606.24875v1 (23 June 2026), retained at
`annexes/arxiv-2606-24875-pendyala-degree-four-lemniscate-path/source.pdf`.
The local extraction is `extracted.md`: the abstract and Theorem 1 (printed
p. 1; extracted lines 6--9 and 26--32) state the monic degree-four theorem with
zeros counted with multiplicity and a polygonal path of length less than two.
Lemma 1 (printed pp. 1--2; extracted lines 34--45) gives the four-point radial
arms, with its angular-gap proof at extracted lines 47--108. The theorem proof,
including the close-pair segment and the normalized radial-arm branch, is at
printed p. 3, extracted lines 111--148.

Pendyala's source supports only that degree-four theorem and radial lemma. The
power-map chord-lift inequality, the translated cyclic-fibre theorem, and the
all-degree `4q` consequence are repository-authored extensions. The Lean
consumer formalizes the antitone-power kernel, its exact primitive, and the
strict endpoint-budget fan-in; it does not postulate or formalize the
covering-space lift construction or Pendyala's geometric lemma.

## The theorem

Let `q>=2`, let `h` be complex, and let `P` be a monic quartic.  Define

```text
f(z)=P((z-h)^q).
```

If all listed zeros of `f` lie in the open unit disk, then two listed zeros are
joined inside `{|f|<1}` by a possibly degenerate rectifiable path of length
strictly below `2`.

Equivalently, Erdős #1041 holds for every polynomial

```text
(z-h)^(4q) + A (z-h)^(3q) + B (z-h)^(2q)
  + C (z-h)^q + D
```

of degree `4q>=8` satisfying the root-location hypothesis.

The proof combines Pendyala's exact quartic dichotomy with a new metric fact:
the lift of a straight chord through a power map never costs more than the two
radial endpoint budgets.

## 1. Every quotient root is strictly inside the unit disk

Write the four listed roots of `P` as `w_1,...,w_4`.  Fix `w_j`, choose
`y_j^q=w_j`, and let `zeta` be a primitive `q`-th root of unity.  The complete
fibre

```text
h+y_j, h+y_j zeta, ..., h+y_j zeta^(q-1)
```

consists of listed zeros of `f`, hence lies in the open unit disk.  Since
`q>=2` and `sum_k zeta^k=0`,

```text
(1/q) sum_k |h+y_j zeta^k|^2 = |h|^2+|y_j|^2 < 1.       (1)
```

Thus `|y_j|<1` and

```text
|w_j|=|y_j|^q<1.                                       (2)
```

So the quartic quotient itself has all four roots strictly inside the unit
disk.

## 2. The power-map chord-lift lemma

Let `a,b` be complex and let `q>=1`; put `alpha=1/q`.  The segment

```text
gamma(t)=(1-t)a+t b
```

has a continuous lift through `pi(y)=y^q`, splitting at zero if the segment
passes through zero.  Away from zero, a chosen lift `eta` satisfies

```text
|eta'(t)| = alpha |b-a| |gamma(t)|^(alpha-1).            (3)
```

Parameterize the supporting line by arclength `x`, with perpendicular distance
`d` from the origin and `x=0` at the perpendicular foot.  Then

```text
|gamma|=sqrt(d^2+x^2).
```

Because `alpha-1<=0`, for `x!=0`,

```text
(sqrt(d^2+x^2))^(alpha-1) <= |x|^(alpha-1).              (4)
```

On a half-segment of coordinate length `A`, (3)--(4) give

```text
length <= alpha integral_0^A x^(alpha-1) dx = A^alpha.  (5)
```

If the perpendicular foot lies inside the chord, apply (5) to both halves and
use `A<=|a|`, `B<=|b|`.  If it lies outside, apply the same primitive on the
single coordinate interval; the resulting difference is smaller still.  Thus

> **Power-map chord-lift lemma.** Some lift of `[a,b]` under `y -> y^q` joins a
> `q`-th root of `a` to a `q`-th root of `b` and has length at most
>
> ```text
> |a|^(1/q)+|b|^(1/q).                                  (6)
> ```

The improper integral at a zero crossing is finite because `alpha>0`, and the
two lifts meet at zero.  Equality in (6) can occur for a diameter through zero;
this is exactly the extremal geometry, not a defect in the estimate.

The Lean module checks the antitone-power kernel (4), the exact primitive in
(5), and the strict endpoint consumer of (6).  The elementary covering-space
construction of the lifted path remains in this analytic note rather than
being postulated as an axiom.

## 3. Close quotient roots: lift their safe chord

Suppose `|w_i-w_j|<1` for some pair.  Every point `w` of their chord lies in the
open unit disk, and

```text
|w-w_i| |w-w_j| <= |w_i-w_j|^2/4.
```

Each of the other two root factors is strictly below `2`.  Therefore

```text
|P(w)| < |w_i-w_j|^2 < 1                               (7)
```

on the entire quotient chord.  Lift this chord under `y -> y^q` and translate
by `h`.  Containment follows from

```text
f(h+y)=P(y^q),
```

while (2) and (6) give

```text
length <= |w_i|^(1/q)+|w_j|^(1/q) < 2.                 (8)
```

This is the new branch that makes a quotient chord usable upstairs; no radial
spoke needs to exist in the close-pair regime.

## 4. Separated quotient roots: Pendyala's radial lemma

It remains to assume

```text
|w_i-w_j|>=1   for every i!=j.                          (9)
```

Let `R=max_j |w_j|<1` and normalize `v_j=w_j/R`.  Then `|v_j|<=1`, while

```text
|v_i-v_j| >= 1/R > 1.
```

Pendyala's four-point radial lemma supplies two distinct indices `i,j` such
that

```text
product_k |t v_i-v_k| <= 1,
product_k |t v_j-v_k| <= 1        (0<=t<=1).            (10)
```

Scaling back gives, on both quotient spokes,

```text
|P(tw_i)| <= R^4 < 1,
|P(tw_j)| <= R^4 < 1.                                  (11)
```

Choose one `q`-th root `y_i` of `w_i` and one `y_j` of `w_j`.  The two radial
segments from `h` to `h+y_i` and `h+y_j` map to the spokes in (11).  Their
combined length is

```text
|w_i|^(1/q)+|w_j|^(1/q) <= 2 R^(1/q) < 2.              (12)
```

This closes the separated case and hence the theorem.

## 5. What has actually been added

Pendyala proved the degree-four theorem itself.  The new mathematical object
here is the power-map chord-lift inequality (6) and its use in the close-pair
branch.  It allows the quartic chord-or-radial dichotomy to survive composition
with an arbitrary cyclic power and arbitrary translation.  Combined with
`EvenSymmetricTrinomialCase.md` and `CubicQuotientFiberCase.md`, Erdős #1041 is
therefore settled for every translated cyclic lift of a monic quotient of
degree two, three, or four.

This does not extend automatically to quotient degree five.  The local corpus
contains an exact five-root configuration with no safe root chord and at most
one safe radial arm through the minimum-enclosing-disc centre, so the two-arm
radial branch and the chord branch can fail simultaneously.  The next quotient
degree requires a genuinely new hub, curved path, or global component
mechanism—the same boundary faced by unrestricted Erdős #1041.
