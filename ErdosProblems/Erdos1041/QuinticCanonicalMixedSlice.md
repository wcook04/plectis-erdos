# Erdős #1041: the canonical quintic mixed slice is completely closed

Status: complete analytic proof, exact symbolic replay, and Lean-checked
load-bearing inequalities, 2026-08-25. This closes an entire mixed family,
not merely its transition point. It does **not** yet prove the global
two-phase mixed selector or unrestricted Erdős #1041.

## The theorem

Put

```text
H_u(z) = Re(u z + i z^2 - z^5),             u >= 0.       (1)
```

For every `u >= 0`, there are two fifth-root rays, a common truncation radius
on them, and the chord joining the two truncation points, such that `H_u <= 0`
on both outward ray tails and on the complete chord.

The selector is explicit. Let

```text
u_*^3 = 27/320,       u_* = 0.4386026607319299... .        (2)
```

For `u <= u_*`, use rays `1, omega` and radius `r_L`; for `u >= u_*`, use
rays `omega^2, omega^3` and radius `r_R`, where

```text
r_L^3 = 0.6500753286943487...,
r_R^3 = 5 - 2 sqrt(5) = 0.5278640450004206... .           (3)
```

Here `omega=exp(2 pi i/5)`. Equality at the transition is a genuine interior
double contact on each selected chord.

## Exact cyclotomic reduction

Let

```text
w = sqrt(10+2 sqrt(5)),       w^4-20w^2+80=0,
190211/50000 < w < 380423/100000.                           (4)
```

Write `u_*=k_L r_L=k_R r_R`. Exact elimination gives

```text
k_L = -3(3w^3-40w-40)/160,
r_L^3 = -(13w^3-40w^2-200w+520)/160,

k_R = 3w^2/80,
r_R^3 = 15-w^2.                                             (5)
```

Reduction modulo (4) gives, for both choices,

```text
k_L^3 r_L^3 = k_R^3 r_R^3 = 27/320.                        (6)
```

Thus both connectors meet at exactly the same amplitude (2); no decimal
fitting enters the theorem.

## The two chord certificates

Parameterize either chord by `z=r((1-t)omega^j+t omega^k)`, `0<=t<=1`, and
divide (1) by `r^2`. At `u=u_*`, exact expansion in the field `Q(w)` factors
the result as

```text
(t-t_0)^2 (q_2 t^2+q_1 t+q_0).                            (7)
```

For the left connector `(j,k)=(0,1)`,

```text
t_0 = -(w-4)(w^2+10w+20)/40,
q_2 = 5(12w^3-25w^2-170w+380)/32,
q_1 = -5(8w^3-17w^2-114w+260)/16,
q_0 = (6w^3-15w^2-90w+220)/8.                             (8)
```

For the right connector `(j,k)=(2,3)`,

```text
t_0 = -(w^3-8w-40)/80,
q_2 = 25(7w^2-100)/8,
q_1 = 5(2w^3-35w^2-30w+500)/8,
q_0 = -5(w^3-7w^2-15w+104)/8.                             (9)
```

Exact rational interval arithmetic using (4) proves in both cases

```text
q_2 > 0,            q_0 < 0,            q_2+q_1+q_0 < 0. (10)
```

The residual quadratic is convex and negative at `t=0,1`, hence is
nonpositive throughout `[0,1]`. Multiplication by `(t-t_0)^2` proves the
complete chord inequality. The Lean theorems `convexQuadratic_nonpos` and
`doubleContactChord_nonpos` kernel-check precisely this step.

## The four ray tails

After the same scaling, every ray has the sparse form

```text
a x + b x^2 + c x^5,                  x>=1.               (11)
```

On three rays, `b,c<=0` and the value at `x=1` is already negative, so the
higher powers only improve the inequality. The remaining ray is `omega^2`:
its quadratic coefficient is positive, but after factoring out `x`, the
residual quartic has derivative sign controlled by

```text
b+4c < 0.                                                   (12)
```

It is therefore decreasing from an already negative value at `x=1`. These
are the two exact scalar arguments formalized as
`sparseRay_nonpos_of_endpoint` and
`sparseRay_nonpos_of_quartic_drop`.

## Why the transition certificate covers every amplitude

On the left chord and both of its rays, `Re z >= 0`. Lowering `u` from `u_*`
can only decrease (1), so the left connector works for every `u<=u_*`.
On the right chord and rays, `Re z < 0`. Raising `u` can only decrease (1),
so the right connector works for every `u>=u_*`.

This is the decisive simplification: the exact equality chart does not need a
uniform perturbative remainder estimate along this amplitude direction. Two
fixed tangent connectors plus monotonicity cover the entire half-line. Lean
checks the two transfer implications and their exhaustive disjunction in
`twoConnector_amplitude_cover`.

## Claim boundary and next handoff

Closed here: the complete canonical phase slice `A=u>=0, B=i`, including the
sharp transition and all amplitudes on either side.

Still open: allow both phases of `(A,B)` to vary, prove a finite connector
atlas covers that compact parameter space, and transfer it through the actual
near-Fekete expansion. The next analytic target is a neighbourhood theorem
around this slice: quantify how the strict parts of the two certificates and
the paired cubic sign cover phase perturbations away from the two double
contacts.
