# Erdős #1041 for translated cubic quotient fibres

Status: proved analytic case theorem, 2026-08-24.  The selector, distance
envelope, and safe-spoke fan-in are formalized in
`CubicQuotientFiberCase.lean`.  This settles an exact all-scale family in every
degree `3q`, `q>=2`; it does not settle unrestricted Erdős #1041 and makes no
literature-priority claim.

## Source and authority boundary

This note has no external paper theorem as a proof premise. The cubic charge
selector, the AM--GM distance envelope, the exact identity
`(1-t)(1+t+t^2)=1-t^3`, the cyclic-fibre pullback, and the degree-sharpness
certificate are repository-authored mathematics. The Lean consumer
`CubicQuotientFiberCase.lean` checks the charge sum, real distance envelope,
complex product estimate, safe-spoke disjunction, and exact quartic falsifier;
the ordinary-mathematics companion supplies the finite fibre construction and
root-of-unity mean-square argument, neither of which is postulated as an axiom.

The elementary ingredients (AM--GM, polynomial factorisation, and the sum of a
finite root-of-unity orbit) are used directly rather than attributed to a
literature source. Accordingly, the degree-`3q` theorem is not presented as a
reported result, and no novelty or priority inference is made for it.

## The theorem

Let `q>=2`, let `h` be complex, and let `P` be a monic cubic.  Define

```text
f(z)=P((z-h)^q).
```

Assume all zeros of `f` lie in the open unit disk and `f` has at least two
distinct zeros.  Then two distinct zeros of `f` are joined by a two-segment
path of length strictly below `2` contained in `{|f|<1}`.

Equivalently, Erdős #1041 holds for every polynomial

```text
(z-h)^(3q) + A (z-h)^(2q) + B (z-h)^q + C,
```

of degree `3q>=6` satisfying the root-location hypothesis.

The proof has two independent parts.  First, every cubic with roots in the
open unit disk has at least one safe spoke from the origin to a root.  Second,
the map `z -> (z-h)^q` pulls that one spoke back to `q` safe spokes, and a
regular-orbit average supplies the strict metric budget.

## 1. A charge selects one cubic root

Write

```text
P(w)=(w-r_1)(w-r_2)(w-r_3),       |r_j|<1.
```

For `{j,k,l}={1,2,3}`, define the real charge

```text
A_j = Re(r_j conjugate(r_k+r_l)).                         (1)
```

The three charges satisfy the exact identity

```text
A_1+A_2+A_3
  = |r_1+r_2+r_3|^2-(|r_1|^2+|r_2|^2+|r_3|^2) > -3.     (2)
```

Consequently some charge is strictly greater than `-1`.  Relabel so
`A_1>=-1`, and put `r=r_1`, `s=r_2`, `v=r_3`.

This selector is global but elementary.  It is also sharp at the boundary:
for a centered equilateral triple every charge equals `-1`.

## 2. The selected spoke is safe

For `0<=t<=1`, arithmetic-geometric mean gives

```text
|tr-s| |tr-v| <= (|tr-s|^2+|tr-v|^2)/2.                 (3)
```

Expanding the numerator and using (1),

```text
(|tr-s|^2+|tr-v|^2)/2
  = t^2|r|^2 + (|s|^2+|v|^2)/2 - t A_1
  < t^2+1+t.                                             (4)
```

Because `P(tr)=r(t-1)(tr-s)(tr-v)`, (3)--(4) imply

```text
|P(tr)|
  < (1-t)(1+t+t^2)
  = 1-t^3
  <= 1.                                                  (5)
```

At `t=1` the value is zero.  Thus the entire radial segment `[0,r]` lies in
the strict cubic sublevel set `{|P|<1}`.  Notice what made degree three close:
after AM--GM there are exactly two residual distances, so their quadratic
envelope is the cyclotomic sum `1+t+t^2` and cancels `1-t` exactly.

The Lean module checks (2), the real envelope (3)--(4), the complex product
estimate (5), and the disjunction saying that one of the three spokes is safe.

## 3. Pulling one spoke back to a full fibre

Each cubic root `r_j` has a `q`-point fibre under `y -> y^q`.  Fix a `q`-th
root `y_j` and a primitive `q`-th root of unity `zeta`; the corresponding zeros
of `f` are

```text
h+y_j, h+y_j zeta, ..., h+y_j zeta^(q-1).                (6)
```

Every point in (6) lies in the open unit disk.  Averaging squared moduli and
using `sum zeta^k=0` gives

```text
(1/q) sum_k |h+y_j zeta^k|^2 = |h|^2+|y_j|^2 < 1.       (7)
```

Hence `|y_j|<1`, and therefore `|r_j|=|y_j|^q<1`; this verifies the root
hypothesis needed in §1 for all three cubic quotient roots.

Choose the safe cubic root `r` from §1.  If `r!=0`, choose two distinct
`q`-th roots `y_1,y_2` of `r`.  Along either spoke from `h`,

```text
f(h+t y_i)=P(t^q r),                                    (8)
```

which is strictly below one in modulus by (5), since `0<=t^q<=1`.  The broken
line

```text
h+y_1  -->  h  -->  h+y_2
```

has length `2|y_1|<2` by (7).

## 4. The zero quotient root

The charge selector could choose `r=0` when the cubic constant term vanishes.
This causes no gap.  Write

```text
P(w)=w(w-s)(w-v).
```

If `P` has a nonzero root, choose one, say `s`.  Its spoke obeys the direct
bound

```text
|P(ts)|
  = |ts| |s(t-1)| |ts-v|
  < 2 t(1-t) <= 1/2 < 1,                                (9)
```

because `|s|,|v|<1`.  Its nonzero fibre therefore supplies the same two-root
path.  If there is no nonzero quotient root, then `P(w)=w^3` and `f` has only
the one distinct zero `h`, contrary to the theorem's hypothesis.  Thus every
nontrivial degeneration is covered.  In the squarefree formulation the issue
cannot arise at all, because a zero quotient root gives multiplicity at least
`q>=2` at `h`.

## 5. Consequence and next boundary

Together with `EvenSymmetricTrinomialCase.md`, this proves Erdős #1041 for all
translated cyclic lifts of monic quotients of degree two or three.  These are
exact coefficient families, not perturbative neighbourhoods, and the centre
`h` is arbitrary.

The argument also explains its own current boundary.  For a quotient of
degree `m`, RMS bounds the `m-1` residual distances by an envelope of the form

```text
(1-t) (1+t^2+2t/(m-1))^((m-1)/2).
```

At `m=3` this is exactly `1-t^3`.  The loss at `m=4` is genuine, not merely a
weakness of how the envelope was written.

### Exact degree-sharpness certificate

Put `L=999/1000`, take three listed quartic roots equal to `L`, and take the
fourth root to be `L u`, where

```text
|u|=1,             Re u=-1/3
```

(for example `u=(-1+2 sqrt(2)i)/3`).  The charge of the isolated root `Lu`
against the other three is

```text
Re(Lu conjugate(3L)) = 3L^2 Re u = -L^2 = -998001/1000000 >= -1.   (10)
```

Nevertheless its spoke is unsafe.  At `t=2/5`,

```text
|t u-1|^2 = 1+t^2-2t Re u = 107/75,
```

and hence

```text
|P(tLu)|^2
  = L^8 (1-t)^2 |tu-1|^6
  = (999/1000)^8 (9/25) (107/75)^3
  = 405092296229092147294468293681
      / 390625000000000000000000000000
  > 1.                                                        (11)
```

The excess numerator is the positive integer
`14467296229092147294468293681`.  All four listed roots are strictly inside
the unit disk; multiplicity is allowed in the underlying listed-root problem.
The Lean module checks (10)--(11) as exact rational arithmetic.

Thus the implication

```text
root charge >= -1  ==>  its full radial spoke is safe
```

is true for cubics by the theorem above and false for quartics.  This does not
refute the stronger possibility that *some differently selected* quartic root
always has a safe origin spoke; the example's three clustered roots are safe.
It does prove that extending the fibre theorem requires a genuinely sharper
multi-distance selector, not repetition of the cubic charge-plus-AM--GM step.
The corpus's separate degree-five example with no safe origin spoke shows that
even that stronger statement cannot persist indefinitely.
