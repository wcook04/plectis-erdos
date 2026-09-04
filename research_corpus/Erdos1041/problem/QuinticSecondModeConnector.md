# Erdős #1041: the all-phase quintic second-mode connector

Status: complete analytic theorem, exact symbolic replay, and Lean-checked
phase-envelope and Bernstein certificates, 2026-08-25. **This is a homogeneous
near-Fekete model theorem, not the unrestricted solution of Erdős #1041.**

## The theorem

Let `omega=exp(2 pi i/5)`, let `|A|=1`, and put

```text
H_A(z) = Re(A z^2-z^5).
```

There is an index `i mod 5` such that both outward radial tails from
`omega^i` and `omega^(i+1)`, together with the unit chord joining those two
points, lie strictly in `{H_A<0}`. On the entire chord there is in fact the
phase-independent rational margin

```text
H_A(z) <= -1/1000.                                      (1)
```

Thus **every phase** of the dangerous second Fourier mode in degree five has
a strict Form-A-cut model connector staying a positive distance from the
singular origin.

## Phase selection

Write `A=exp(i phi)`. Rotate the adjacent pair `(omega^i,omega^(i+1))` to the
base pair `(1,omega)`. Since `omega^(5i)=1`, the rotated model is

```text
Re(exp(i theta) w^2-w^5),       theta = phi+4 pi i/5  (mod 2 pi).
```

The five possible values of `theta` meet the interval

```text
2 pi/5 <= theta <= 4 pi/5.                              (2)
```

Indeed the five translates of this interval have length `2 pi/5` and tile a
full period. The Lean theorem `fivePhaseSector_cover` checks the corresponding
five-case real inequality without an appeal to a picture.

For either endpoint ray of the selected pair and `r>=1`,

```text
H_A(r omega^j)=r^2(cos(theta_j)-r^3).
```

Condition (2) puts both endpoint projections strictly below one, so both
outward arms are strictly negative. It remains to control the chord.

## Why only two boundary phases matter

Parameterize the base chord by

```text
w(t)=(1-t)+t omega = rho(t) exp(i alpha(t)),    0<=t<=1.
```

Its argument increases from `0` to `2 pi/5`, with
`alpha(t)<=pi/5` exactly on the first half. In polar coordinates,

```text
H_theta(w)=rho^2 cos(theta+2 alpha)-rho^5 cos(5 alpha).   (3)
```

For fixed `alpha` in the first half, `cos(theta+2 alpha)` is maximized over
(2) at `theta=2 pi/5`; in the second half it is maximized at
`theta=4 pi/5`. One exact proof subtracts the endpoint cosine and uses

```text
cos x-cos y=-2 sin((x+y)/2) sin((x-y)/2),
```

whose two sine factors have the required common sign on the stated ranges.
The Lean theorems `phaseModel_le_leftEndpoint` and
`phaseModel_le_rightEndpoint` kernel-check these two envelope inequalities.

The two boundary chords are reflections of one another:

```text
H_(omega)(w(t)) = H_(omega^2)(w(1-t)).                   (4)
```

Consequently it suffices to certify just the right boundary phase.

## Exact boundary certificate

For `theta=4 pi/5`, put `s=sqrt(5)`. Direct reduction using
`omega^4+omega^3+omega^2+omega+1=0` gives

```text
H_(omega^2)(w(t)) = (25/4)(s-1) Q(t),
Q(t)=t^4-2t^3+(11/10-9s/50)t^2+(s/5)t-3s/50-1/10.
```

Degree-elevate this quartic to its degree-13 Bernstein form. Its exact
coefficients are

```text
(-5-s)/4, (-9s-20)/26, (-53s-70)/156, (-157s-140)/572,
(-53s-35)/286, (-169s-95)/1716, 3(-6s-5)/572,
(-15+4s)/572, (-95+29s)/1716, (-35+2s)/286,
(-140-3s)/572, (-70+s)/156, (-10+s)/13, (-5+s)/4.
```

Every coefficient is at most `-1/1000`, using only `2<sqrt(5)<3`. The
Bernstein basis is nonnegative and sums to one, proving the uniform boundary
margin. Reflection (4) proves the same bound at the other endpoint phase, and
the cosine envelope proves (1) for every phase in (2). This completes the
all-phase theorem.

The exact true worst margin is about `0.132`, attained at the boundary chart;
the rational `1/1000` is deliberately weaker and proof-robust. The checker
replays (4), both polynomial identities, all fourteen coefficient bounds, and
as a non-authoritative calibration tests 20,001 coefficient phases on 4,001
chord points, selecting among all five adjacent pairs. The worst sampled best
chord is `-0.1320014746`.

## Why this changes the frontier

The first-mode argument does not cover the tangent stratum whose leading
Fourier frequency is two. The earlier first-nonzero-mode theorem supplies two
negative rays, but its margin vanishes at the origin and cannot by itself
absorb the anchored nonlinear remainder there. The theorem above solves that
problem for the first open degree and for **all coefficient phases**: truncate
at the balance radius and join two adjacent arms by a uniformly negative
chord.

After rescaling `z=rho w`, with `rho=|E_2|^(1/3)`, the chord margin has size
`rho^5=|E_2|^(5/3)`. The origin-anchored remainder from
[FormACutQuantitativeExpansion.md](FormACutQuantitativeExpansion.md) is
`O(eta^2 rho)`, hence smaller whenever the second mode is genuinely dominant
(`|E_2|` comparable to `eta`). The remaining degree-five issue is the compact
transition model in which the first and second modes are simultaneously
visible; across degrees, the analogous finite Newton-mode faces remain.

This checkpoint closes the pure second-mode phase circle. It does not assert
that the pure-mode chart alone covers mixed-mode perturbations or configurations
away from the near-Fekete regime.
