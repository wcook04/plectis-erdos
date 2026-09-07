# Erdős #1041: the quartic-core radius theorem

Status: analytic theorem proved on 2026-08-24. The multiplicative factor
consumer, uniform radius identity, and an exact separated quintic certificate
are formalized in `QuarticCoreRadiusCase.lean`; focused canonical Lean
validation is pending. The degree-four input is explicitly attributed to
Venkata Siddharth Pendyala, *A Degree-Four Lemniscate Path Theorem*,
arXiv:2606.24875 (2026). This theorem solves a new all-degree radius class; it
does not solve unrestricted Erdős #1041 and makes no literature-priority claim.

## Source and attribution boundary

The downloaded primary source is Venkata Siddharth Pendyala, *A Degree-Four
Lemniscate Path Theorem*, arXiv:2606.24875v1 (23 June 2026), retained at
`annexes/arxiv-2606-24875-pendyala-degree-four-lemniscate-path/source.pdf`.
The local text extraction is `extracted.md`: its abstract and Theorem 1
(printed p. 1; extracted lines 6--9 and 26--32) state the monic degree-four
short-path theorem, including multiplicities, the open-unit-disk hypothesis,
and the strict length bound. Lemma 1 (printed pp. 1--2; extracted lines 34--45)
is the four-point radial lemma, and its angular-gap proof is at extracted lines
47--108. The theorem proof's close-pair branch and normalized minimal-enclosing
disk branch are at printed p. 3, extracted lines 111--148.

Those locators support only Pendyala's degree-four theorem and its
four-point-radial mechanism. The off-centre factor-budget theorem (QC), its
uniform-radius corollary, the arbitrary-extra-factor extension, and the exact
separated quintic witness are repository-authored consequences. The Lean
consumer formalizes the scalar factor-budget implications and exact witness
arithmetic; it does not postulate or formalize Pendyala's geometric lemma or
path construction, and focused canonical validation remains pending.

## Headline theorem

Let

```text
f(z)=product_(j=1)^n (z-z_j),              n>=4.
```

Select four roots `z_1,...,z_4`. Suppose they lie in the open disk
`D(h,R)`, where `0<R<1`, and put

```text
Q(z)=product_(j=1)^4 (z-z_j).
```

If

```text
R^4 product_(k=5)^n (R+|z_k-h|) <= 1,                 (QC)
```

then two of the selected four roots are joined inside `{|f|<1}` by a
polygonal path of length strictly below `2R`, hence strictly below `2`.

This is a genuine quartic-core theorem: the unselected roots can be anywhere,
provided their explicit multiplicative cost in (QC) fits the budget. No unit
disk hypothesis on those roots is needed for the analytic implication itself.

## Proof

Normalize the four selected roots by

```text
u=(z-h)/R,             u_j=(z_j-h)/R,
q(u)=product_(j=1)^4 (u-u_j)=R^(-4)Q(h+Ru).
```

All four `u_j` lie in the open unit disk. Pendyala's degree-four proof gives
two of them and a polygonal path `gamma` joining them such that

```text
gamma is contained in the open unit disk,
length(gamma)<2,
|q(u)|<1 on gamma.                                      (1)
```

The containment assertion in (1) is part of the construction, not an added
hypothesis. In the close-pair branch the path is the root chord. In the
separated branch it is the union of two radial arms through the centre of the
four points' minimum enclosing disk. That centre lies in the convex hull of
the points, so both arms lie in their convex hull and hence in the unit disk.
The local extracted copy of arXiv:2606.24875 proves exactly this
chord-or-two-radii dichotomy.

Scale and translate the path:

```text
Gamma=h+R gamma.
```

Then `Gamma` lies in `D(h,R)`, joins two selected roots, has length below
`2R`, and by (1)

```text
|Q(z)|<R^4.                                             (2)
```

For every unselected root and every `z` on `Gamma`,

```text
|z-z_k| <= |z-h|+|z_k-h| < R+|z_k-h|.                  (3)
```

Multiplying (2) and (3), then using (QC), gives

```text
|f(z)|
 < R^4 product_(k=5)^n (R+|z_k-h|)
 <= 1.                                                  (4)
```

Thus the entire path is in the strict unit lemniscate, and its length is
below `2R<2`. This proves the theorem.

The Lean module checks the strict scalar fan-in behind (4), including its
complex-norm form. The finite four-point construction is Pendyala's attributed
analytic input and is not hidden behind a Lean axiom.

## Uniform-radius corollary

Suppose all `n` roots lie in one disk `D(h,R)`, with `n=m+4`. Select any four
as the core. Each remaining factor in (3) is strictly below `2R`, and the
factor budget becomes

```text
R^4(2R)^m = 2^m R^(m+4) = 2^(n-4)R^n.                 (5)
```

Consequently Erdős #1041 holds whenever

```text
2^(n-4) R^n <= 1.                                      (UR)
```

Equivalently, if the roots have circumradius `rho`, the strict condition

```text
rho < 2^(-(n-4)/n) = 2^(4/n-1)                        (6)
```

suffices: choose `R` strictly between `rho` and the right side of (6). For
degree five this is

```text
rho < 2^(-1/5) = 0.8705505632... .                     (7)
```

At degree four, (6) is the full unit-radius theorem of Pendyala. For higher
degrees it is a new exact all-configuration radius class, not a reformulation
of the unrestricted problem. The threshold is the output of this black-box
quartic-core factor budget; no global optimality is claimed.

## Exact strict-extension quintic

The general theorem covers configurations missed by the existing close-pair
branch. Take

```text
h=-3/10,       R=3/5,
```

and four Gaussian-rational core roots obtained from the offsets

```text
( 9/25, 12/25),  (-12/25,  9/25),
(-9/25,-12/25),  ( 12/25, -9/25)
```

about `h`. Take the fifth root to be `9/10`. Explicitly the five roots are

```text
 3/50 + (12/25)i,
-39/50 + (9/25)i,
-33/50 - (12/25)i,
 9/50 - (9/25)i,
 9/10.
```

Every root lies strictly inside the unit disk. The core roots have exact
distance `3/5` from `h`, while the fifth root has distance `6/5`. Therefore

```text
R^4(R+|z_5-h|)
 = (3/5)^4(9/5)
 = 729/3125
 < 1.                                                   (8)
```

The theorem supplies a path of length below `2R=6/5`, with the much stronger
pointwise bound `|f|<729/3125` before the final comparison to one.

This witness is deliberately separated. Exact rational arithmetic gives

```text
|z_i-z_j|^2 > 5/9                 for every i!=j.       (9)
```

Hence the strengthened quintic close-pair theorem cannot certify it. Its
polynomial is a generic dense quintic, so none of the sparse trinomial or
tetranomial coefficient selectors applies. The Lean certificate checks the
root radii, all ten inequalities in (9), the core/fifth distances, and (8) by
native exact rational evaluation.

## Relation to the forum comments and claim boundary

The forum chronology is used selectively. Pendyala's valid degree-four
theorem is the core input. The earlier unrestricted gradient-flow/tree claim
is not used: its cheap-tree proposition is false, exactly as the forum
correction records. This result therefore extends a verified local mechanism
rather than reviving the invalid global stitching argument.

What is proved is the quartic-core theorem (QC), its uniform-radius corollary
(6), and the exact separated witness. What remains open is the complement,
especially quintics of circumradius at least `2^(-1/5)` with no favourable
off-centre quartet budget. The Refinery should place this immediately after
Pendyala's quartic theorem and before the close-pair cyclic-quotient theorem,
because it promotes the whole quartic path—not merely its chord branch—through
arbitrary extra factors.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quartic_core_radius_case.py
```
