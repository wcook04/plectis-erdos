# A tied Newton face can have no safe model spoke

## Status

This note gives an exact degree-five counterexample to the tempting extension
of the unique-Newton-face theorem: a tied low-mode face need not have even one
complete safe root ray.  The counterexample is an obstruction to the proof
mechanism only.  A truncated connector exists numerically with large margin,
the complete quintic near-Fekete neighbourhood is already proved elsewhere,
and Erdős #1041 remains open.

## Exact model

Let `omega=exp(2 pi i/5)` and

```text
H(z) = Re(z + 10 z^2 - z^5).
```

On the `j`-th fifth-root ray, `z=t omega^j`, one has

```text
H(t omega^j) = t cos(2 pi j/5)
             + 10 t^2 cos(4 pi j/5) - t^5.              (1)
```

Put `s=sqrt(5)`, `c=(s-1)/4=cos(2pi/5)` and
`d=(s+1)/4=-cos(4pi/5)`.  Conjugate symmetry leaves three ray types:

```text
j=0:      q_0(t) = t + 10t^2 - t^5,
j=1,4:    q_1(t) = c t - 10d t^2 - t^5,
j=2,3:    q_2(t) = -d t + 10c t^2 - t^5.
```

They all enter the positive set.  Explicitly,

```text
q_0(1/10)    > 0,
q_1(1/1000)  > 0,
q_2(3/10)    > 0.
```

For the last inequality,

```text
q_2(3/10) = 3(sqrt(5)-2)/20 - 243/100000 > 0,
```

using only `sqrt(5)>11/5`.  The middle inequality follows already from
`11/5<sqrt(5)<3`.  The radical bounds, the three evaluations, their five-ray
assembly, and the negation of a globally nonpositive model ray are checked in
`TiedNewtonFaceTwoSpokeNoGo.lean`.

Thus no choice of one root direction, let alone two, can close this tied face
by complete origin spokes.

## Why this is the right no-go

The unique-face theorem works because a single lowest active monomial is
negative on two phase directions and every competitor has a positive Newton
weight gap.  Here the linear term selects the directions `j=2,3` near the
origin, while the tied quadratic term creates a positive bump on precisely
those rays.  Conversely, the linear term already makes the other three rays
positive near the origin.  This is the smallest possible face switch in which
the selector moves with radius.

The obstruction does not touch Form A-cut.  In fact the adjacent pair `(1,2)`
is rescued exactly at common scaled radius `2`.  Both ray polynomials are
strictly negative for every `t>=2`.  On the connector

```text
z(u)=2((1-u)omega+u omega^2),       0<=u<=1,
```

the exact restriction is

```text
(-200+200s)u^4 +(400-400s)u^3 +(-400+260s)u^2
 +(200-41s)u -85/2-19s/2.
```

Splitting at `u=1/2`, its quartic Bernstein coefficients after adding `5`
are all nonpositive.  Hence the entire chord has `H<=-5`.  Lean checks the
Bernstein lemma, both interval certificates, and both outward ray inequalities.
Thus the same exact example proves both claims: complete spokes are false, and
a truncated connector is the correct replacement.

## Consequence for the programme

The all-degree near-Fekete programme now splits honestly:

1. unique outer Newton faces are already closed along analytic arcs;
2. the present exact counterexample retires complete spokes on tied faces but
   proves the first tied face is rescued by an exact truncated connector;
3. the surviving local target is the analogous connector theorem for every
   compact tied-face model, followed by the existing positive integer-gap transfer;
4. a full analytic-arc closure would then promote to an actual neighbourhood
   by semialgebraic curve selection.

The last two steps are not proved here.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_tied_newton_face_two_spoke_no_go.py --json
```
