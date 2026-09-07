# Erdős 1041: exact AP on an all-even two-level wall, and a scalar no-go

Date: 2026-08-30. Status: ordinary exact all-even-degree family theorem with
exact rational replay and a quartic Lean source pending focused validation.
This note also gives an actual polynomial no-go for the total-three-arm
threshold proposed in `SaddleWallPairCompression.md`. The parent path theorem
for this centred trinomial family was already proved, more generally, by
`CyclicTrinomialFiberCase.md`; the new positive content here is the exact
critical-arc product on its saddle-wall geometry. This note does **not** prove
the unrestricted admissible-product inequality or Erdős 1041.

## 1. The family and its exact wall geometry

Let `m>=2` and `0<b<a<1`, and put

```text
f(z)=(z^m-a^m)(z^m+b^m)
    =z^(2m)+(b^m-a^m)z^m-a^m b^m.                       (F)
```

Its roots are the two interlaced regular `m`-gons

```text
a zeta_k,                    b exp(pi i/m) zeta_k,
zeta_k^m=1.
```

Writing

```text
beta  = a^m b^m,
gamma = ((a^m+b^m)/2)^2,
c^m   = (a^m-b^m)/2,
```

direct differentiation gives

```text
f'(z)=m z^(m-1)(2z^m+b^m-a^m).
```

Thus `0` is a critical point of multiplicity `m-1` with value `-beta`, while
the `m` points `c zeta_k` are simple critical points with the common value
`-gamma`. Moreover

```text
gamma-beta=((a^m-b^m)/2)^2>0,                           (L)
```

so every critical value lies on one descending ray and the configuration is
an exact two-level saddle wall. Since `a,b<1`, both levels are strictly below
one.

The inverse-ray arcs are elementary. At an outer saddle `c zeta_k`, one arm
runs radially to `a zeta_k`, with length `a-c`. The other runs radially to
zero and then out along the adjacent inner ray to
`b exp(pi i/m) zeta_k`, with length `c+b`. Hence every outer two-arm path has
length

```text
L_out=a+b.                                                (A1)
```

At the central multiplicity, the `m` descending arms are the inner radii,
each of length `b`. After separating the multiplicity and taking the
coalescing limit, its `m-1` binary merge edges therefore all have length

```text
L_in=2b.                                                  (A2)
```

This limiting interpretation is independent of the resolving tree: every
edge joins two inner arms through zero and hence has the same length `2b`.

## 2. Exact admissible-product theorem

Put `n=2m` and `r=b/a`. The normalized factor of every central edge and every
outer edge is respectively

```text
q_in  = L_in /(2 beta^(1/(2m)))
      = sqrt(r),

q_out = L_out/(2 gamma^(1/(2m)))
      = (1+r) / (2 ((1+r^m)/2)^(1/m)).                  (Q1)
```

> **Theorem (two-level wall AP).** For every `m>=2` and `0<r<=1`,
>
> ```text
> q_out<=1,
> Q_m(r):=q_in^(m-1) q_out^m
>       =r^((m-1)/2)(1+r)^m/[2^(m-1)(1+r^m)]<=1.       (Q2)
> ```
>
> The inequalities are strict for `0<r<1`, and equality occurs at `r=1`,
> the coalesced regular `2m`-gon `z^(2m)-a^(2m)`.

### Proof

Convexity of `x |-> x^m` on the nonnegative real axis gives the midpoint
power-mean inequality

```text
((1+r)/2)^m <= (1+r^m)/2,
```

or equivalently

```text
(1+r)^m <= 2^(m-1)(1+r^m).                              (PM)
```

Equation `(Q1)` says exactly that `q_out^m` is the left side of `(PM)` divided
by the right side, so `q_out<=1`. Also `q_in=sqrt(r)<=1`. Multiplying the
`m-1` central factors and the `m` outer factors proves `(Q2)`. Strictness and
the equality case follow from strict convexity and `r<1`. `[]`

In particular `(AP)` is proved on this entire all-even-degree terminal family,
with the explicit uniform gap

```text
Q_m(r) <= r^((m-1)/2) < 1                               (G)
```

away from the regular-polygon collision.

The original path conclusion has an even simpler occupied proof: this is the
centred trinomial

```text
z^(2m)+(b^m-a^m)z^m-a^m b^m,
```

so `CyclicTrinomialFiberCase.md` makes every origin spoke safe. Directly, any
two inner roots joined through zero have length `2b<2`, and along an inner
spoke the polynomial modulus is at most `beta<1`. Thus `(Q2)` is not a new
parent-family closure; its value is compatibility with the surviving global
admissible-product program and its exact wall equality structure.

## 3. The scalar total-length threshold is false

For `m=2`, the central saddle is simple. Choose one outer saddle and use the
notation of `SaddleWallPairCompression.md`. Then

```text
A=B=b,       X=a,       T=a+2b.
```

The formerly proposed scalar certificate becomes, after taking fourth powers,

```text
(a+2b)^4 <= 32ab(a^2+b^2).                              (T4)
```

At `a=1`, `b=9/10`, the left side minus the right side is exactly

```text
5836/625>0.                                              (N1)
```

Similarity-shrinking `a,b` puts every root strictly inside the unit disk and
preserves this failure. Thus the total-three-arm threshold is **false for an
actual polynomial saddle wall**.

The true lower/upper normalized pair nevertheless remains below one. Its
square is

```text
q_pair^2 = r(1+r)^2/[2(1+r^2)],
```

and the exact slack is

```text
1-q_pair^2
  =(1-r)(r^2+r+2)/[2(1+r^2)]>0.                         (N2)
```

At `r=9/10`, this is `371/3620`. The complete quartic AP square has the
sharper factorization

```text
4(1+r^2)^2-r(1+r)^4
  =(1-r)(r^4+r^3+7r^2+3r+4).                            (N3)
```

The diagnosis is exact: replacing the wall product by `T^2/2` discarded the
large stem slack `X^2/2`. The correct simple-wall condition retains all of
`SaddleWallPairCompression.md`'s equality:

```text
T^2-X^2-(A+B)|A-B| <= 8(beta gamma)^(1/n).               (SC*)
```

Unlike the false total-length bound, `(SC*)` is exactly equivalent to the
two-factor wall product being at most one.

## 4. Consequence for the frontier

The polynomial three-arm total `T` is retired as a universal target. A wall
proof must preserve stem/imbalance slack, or work directly with the complete
rooted merger block. This agrees with the independent computation in
`AdmissibleCriticalArcProductLab.md`: local node overspend is real, while
complete descendants repay it.

The new exact AP calculation is a subordinate mechanism theorem, not another
count of a family already solved by the centred-trinomial carrier. General
simple walls need not have equal lower arms, two rotational root orbits, or a
coalesced central block; longer spines and the root/admissibility/collision
strata remain open. The full admissible-product inequality, degree five, and
unrestricted Erdős 1041 remain open.

## Verification

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_symmetric_two_level_wall.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py --jobs 2 \
  ErdosProblems/Erdos1041/SymmetricTwoLevelWall.lean
```

The Python replay checks the exact power-mean inequality and critical-level
identity on `10,080` all-even-degree Fraction rows, plus `3,159` quartic
slack rows and the rational threshold counterexample. The Lean source states
`(N1)--(N3)` and their quartic inequality consumers, but its focused build was
terminated by the canonical build firewall before any theorem diagnostic and
therefore remains pending. No numerical continuation is used.
