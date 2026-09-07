# Erdős #1041 for translated even-symmetric trinomials

Status: proved analytic case theorem, 2026-08-24.  The decisive spoke estimate
is formalized in `EvenSymmetricTrinomialCase.lean`.  This settles an exact
all-scale family in every even degree at least four; it does not settle the
unrestricted problem and makes no literature-priority claim.

Later the same day, [CyclicTrinomialFiberCase.md](CyclicTrinomialFiberCase.md)
strictly subsumed this result by proving the spoke estimate for every exponent
pair `m>r>=1`.  This file is retained as the independently derived quadratic
quotient specialization and its exact factorization proof.

## The theorem

Let `q >= 2` and

```text
f(z) = (z-h)^(2q) + a (z-h)^q + c.
```

Assume that all zeros of `f` lie in the open unit disk and that `f` has at
least two distinct zeros.  Then two distinct zeros of `f` can be joined by a
rectifiable path of length strictly less than `2` on which `|f| < 1`.

Thus Erdős #1041 holds for every translated even-symmetric trinomial of degree
`2q >= 4` to which the problem applies.  In particular it holds for every
squarefree member of this family.  No smallness assumption on `h`, `a`, or `c`
is present beyond the actual root-location hypothesis.

## 1. The quadratic quotient

Put `y=z-h` and `w = y^q`.  The zero equation becomes

```text
w^2 + a w + c = 0.                                      (1)
```

Suppose first that `c != 0`, and write the two roots of (1) as `w_1,w_2`,
with multiplicity.  Since `w_1 w_2 = c`, one of them, say `w`, satisfies

```text
|w|^2 <= |c|.                                           (2)
```

Every point `h+y` with `y^q=w` is a zero of `f`.  Because `c != 0`, also
`w != 0`, so these are `q >= 2` distinct zeros.

## 2. The exact spoke factorization

Choose `y` with `y^q=w`, so `h+y` is a zero, and travel from the centre to it
as `h+t y`, `0 <= t <= 1`.  Set `u=t^q`.  Eliminating `a w` with (1) gives the
identity

```text
f(h+ty)
  = u^2 w^2 + a u w + c
  = c (1-u) (1-u delta),              delta = w^2/c.    (3)
```

By (2), `|delta| <= 1`.  Hence

```text
|f(h+ty)|
  <= |c| (1-u) (1+u |delta|)
  <= |c| (1-u) (1+u)
  =  |c| (1-u^2)
  <= |c|.                                                (4)
```

This is the whole containment mechanism.  It uses neither a critical point
nor a continuation argument: the two safe arcs are literal radial segments
from the symmetry centre `h`.
The Lean module proves (3), the disk inequality behind (4), and their fan-in
as a single spoke theorem.

It remains to justify strictness after translation.  Fix either quotient root
`w_i`, choose `y_i^q=w_i`, and let `zeta` be a primitive `q`-th root of unity.
The complete orbit

```text
h+y_i, h+y_i zeta, ..., h+y_i zeta^(q-1)
```

consists of zeros of `f`, hence lies in the open unit disk.  Since `q>=2` and
`sum_k zeta^k=0`, averaging squared moduli gives

```text
(1/q) sum_k |h+y_i zeta^k|^2 = |h|^2+|y_i|^2 < 1.       (5)
```

Thus `|y_i|<1` and `|w_i|=|y_i|^q<1` for both quotient roots.  Therefore
`|c|=|w_1w_2|<1`.  Formula (4) consequently places every selected spoke in the
strict sublevel set `{|f|<1}`.

## 3. Two distinct roots and the strict length budget

Take two distinct `q`-th roots `y_1,y_2` of the selected nonzero `w`.  Join the
corresponding zeros by the broken line

```text
h+y_1  -->  h  -->  h+y_2.
```

Both segments satisfy (4), and

```text
length = |y_1|+|y_2| = 2 |w|^(1/q) < 2,
```

where the strict inequality follows from (5).  This proves the theorem when
`c != 0`.

## 4. The degenerate constant term

If `c=0`, then

```text
f(z)=(z-h)^q((z-h)^q+a).
```

The hypothesis of at least two distinct zeros excludes `a=0`.  Choose two
distinct `q`-th roots `y` of `-a`.  Along either spoke `h+ty`, again with
`u=t^q`,

```text
f(h+ty)=a^2(u^2-u),
|f(h+ty)| <= |a|^2/4 < 1.
```

Here `|a|<1` and the common orbit radius is below one by the same mean-square
identity (5).  Their broken-line length through `h` is twice that radius and is
strictly below `2`.
So the constant-term degeneration is covered as well.  (In the usual
squarefree formulation this branch cannot arise, since zero then has
multiplicity `q>=2`.)

## 5. Why this is a genuine closure

The earlier higher-tangent computation suggested only a sufficiently small
perturbation theorem for `z^n+(n/j)epsilon z^j-r^n`.  At the middle tangent
`n=2j`, its first-order boundary slack and the spoke overshoot occur at the
same formal scale, so the perturbative estimate looked exceptional.  Passing
to the quotient `w=(z-h)^q` exposes the opposite fact: the middle tangent is the
one case with an exact quadratic factorization, and the product of the two
quotient roots selects the safe orbit automatically.

This result is stronger than a neighbourhood theorem:

* it works at every coefficient scale allowed by the root-location hypothesis;
* it settles infinitely many non-collinear, non-Chebyshev configurations, with
  arbitrary symmetry centre, in every even degree at least four;
* it supplies an explicit pair of roots and an explicit two-segment path;
* containment and the strict length bound are separate one-line estimates.

What remains open is unrestricted Erdős #1041: a general polynomial has no
cyclic quotient forcing an entire root orbit to share one safe spoke estimate.
The reusable mechanism to export is therefore not merely "try a fixed hub" but:

> compress a symmetric root orbit to a low-degree quotient, select a quotient
> root by a product inequality, and pull its full fibre back to a short safe
> hub.

## 6. Computational audit and its role

A fixed-seed (`1041`) audit sampled `200000` random pairs of quotient roots in
the unit disk, selected the smaller-modulus root, and sampled one `u` on each
spoke.  (Translation does not enter the normalized identity.)  The maximum
floating-point error in (3) was `4.579e-16`; the largest
observed `|delta|` was `0.999997156999`, and the largest observed normalized
spoke value was `0.999997500209`.  This calculation is only a transcription and
boundary audit.  The proof is the exact algebra (3), Vieta's product identity,
and the analytic inequalities above; no numerical premise enters the theorem.
