# Erdős #1041: the tail-resultant bonus

Status: analytic theorem proved on 2026-08-24; the finite product-bonus
principle and its signed-energy consumer are formalized in
`TetranomialTailProductSelector.lean`.  Its exact canonical shared-cache Lean
build passed on 2026-08-24.
This strictly enlarges the proved tetranomial class; it is not an unrestricted
solution of Erdős #1041.

## The new selector

Let

```text
g(w)=w^m+a w^r+b w^s+c,              m>r>s>=1,
t_i=c+b w_i^s,
```

where `w_1,...,w_m` are all roots of `g` in the open unit disk.  Retain the
explicit Newton moment `N=sum_i w_i^s` and put

```text
B = m|c|^2+(m-1+|c|^(2s))|b|^2+2 Re(conj(c)bN),
R = Res(g,bX^s+c).
```

The resultant is completely explicit.  With

```text
q = gcd(s,m-r),       S=s/q,       D=(m-r)/q,
```

its squared modulus is

```text
|R|^2 = |c|^(2r) |(-a)^S b^D-(-c)^D|^(2q).            (R)
```

If `|R|<=1` and

```text
B < m-1 + |R|^2,                                  (TR)
```

then two distinct roots have `|t_i|<1`.  Their complete origin spokes lie in
`{|g|<1}`, so the two roots are joined there by a broken line of length below
two.  The conclusion also survives every translated cyclic lift already
covered by the companion theorem.

## Proof

The exact energy identity and the root-product estimate give

```text
sum_i |t_i|^2 <= B.                                (1)
```

Since `g` is monic,

```text
product_i t_i = Res(g,bX^s+c)=R,
product_i |t_i|^2 = |R|^2.                         (2)
```

For completeness, (R) is not a hidden determinant computation.  When
`b!=0`, put `u=-c/b` and `d=m-r`.  At every root `zeta` of
`bX^s+c`,

```text
g(zeta)=zeta^r(zeta^d+a).
```

The map `zeta -> zeta^d` sends the `s` roots of `zeta^s=u` onto the
`S` roots of `eta^S=u^D`, each with multiplicity `q`.  Multiplying the
displayed values and cancelling the powers of `b` gives (R), up to an
irrelevant unit sign.  The identity for `b=0` follows directly (or by the
resulting polynomial identity).

Here is the new finite argument.  Suppose nonnegative `x_1,...,x_m` have
product `P<=1` and at most one is below one.  Select the exceptional entry `y`
if it exists, and otherwise select any entry.  Every other entry `z>=1` can be
multiplied into the running exceptional product without increasing the total
budget, because

```text
y z <= y+(z-1)              whenever 0<=y<=1<=z.
```

All intermediate running products remain at most the final product's upper
bound one.  Iterating gives the sharp inequality

```text
sum_i x_i >= m-1+P.                                 (3)
```

Apply (3) to `x_i=|t_i|^2` and `P=|R|^2`.  Equations (1), (2), and (TR)
contradict the assumption that at most one tail is safe.

The threshold is sharp for fixed `P<=1`: equality in (3) is attained by one
entry `P` and the other `m-1` entries equal to one.  Thus no larger uniform
bonus can follow from total energy and total product alone.

## Computational pressure

The deterministic replay uses the same 3,204 accepted open-disk
tetranomials as the preceding product-sensitive audit.  The old bound proves
3,187 cases.  The tail-resultant bonus proves 3,201, gaining 14 of the 17
old residuals; every one of the 3,201 certified samples has at least two
numerically safe tails.  Three samples remain outside this sufficient class;
the orthogonal reciprocal-moment selector closes two, and the existing
close-pair theorem closes the third.
These counts measure scope and falsification pressure; the analytic argument
and Lean kernel are proof authority.

## Boundary and handoff

The theorem is a genuinely stronger sufficient class, not a reformulation:
whenever `0<|R|<=1`, (TR) has a strictly larger right-hand side than the
previous selector.  Its remaining three sampled residuals should be split between
sharpening the radial moment bound in (1) and selectors using more than total
tail energy.  The Refinery should place this theorem after the Vieta
product-sensitive selector and retain the explicit no-priority boundary.
