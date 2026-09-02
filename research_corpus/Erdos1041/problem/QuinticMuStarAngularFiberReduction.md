# Erdős 1041: each `mu_*` phase fibre is controlled by its two endpoint rays

Date: 2026-08-30. Exact algebra checker:
`scripts/check_erdos1041_quintic_mustar_angular_fiber.py`.  Endpoint input:
`QuinticMuStarEndpointExcessCertificate.md`.

## 1. Result

Let

```text
mu_* = (-70+10 i sqrt(5))/27.                       (A1)
```

At this gap-zero parameter the allowed phase set is a half-circle.  This note
proves an angular maximum principle which reduces its entire curved-pair
excess inequality to the two endpoint rays.

> **Theorem A (short-sector angular maximum principle).**  Write
>
> ```text
> e^{i phi_c}=(-19+5 i sqrt(5))/(9sqrt(6)).          (A2)
> ```
>
> If the curved-pair excess at both endpoints
> `phi=phi_c+-pi/2` is at most `-a<0`, then
>
> ```text
> mathcal E(mu_*,phi)<=-a
> for every |phi-phi_c|<=pi/2.                       (A3)
> ```

The exact endpoint theorem now gives

```text
mathcal E(mu_*,phi_c+pi/2)<-47/125,
mathcal E(mu_*,phi_c-pi/2)<-2/5.
```

Taking `a=3/8` therefore closes the complete allowed `mu_*` fibre below
`-3/8`.  Conjugation closes the other root of
`27mu^2+140mu+200=0`.  The global phase theorem
`PhiConvexitySturmBound.md` gives the same endpoint domination independently;
the short-sector proof here is a self-contained exceptional-fibre route.

This is a proved analytic reduction.  It does not manufacture the endpoint
bounds; those are the sole remaining input.

## 2. Exact exceptional-fibre geometry

The polynomial factors as

```text
F_{mu_*}(x)
 =x^2(x+(5+i sqrt(5))/3)^2(x+(5-2i sqrt(5))/3).     (A4)
```

Its critical-gap cubic has roots zero and

```text
g_-=-[4(3-sqrt(3))/81](19+5i sqrt(5)),
g_+=-[4(3+sqrt(3))/81](19+5i sqrt(5)),              (A5)

g_+/g_-=2+sqrt(3).
```

Thus the two nonzero gaps have one common direction.  Formula (A2) has unit
modulus and rotates both to the positive real axis.  The chamber condition is
therefore exactly

```text
|phi-phi_c|<=pi/2.                                  (A6)
```

The extra critical point at `x=-(5+i sqrt(5))/3` has critical value zero and
is distinct from the active hub `x=0`.  It causes no obstruction to the two
hub branches at positive ray levels.

## 3. A subharmonic function on the fifth-root sector

For `alpha in C*`, define

```text
Q_alpha(y)=alpha^-5 F_{mu_*}(alpha y).               (A7)
```

The positive `Q_alpha` ray corresponds to the physical ray with direction
`alpha^5/|alpha|^5`.  Put `c=alpha^-1`.  Exact expansion gives

```text
Q_alpha(y)=y^5+5cy^4+10c^2y^3+(10+mu_*)c^3y^2,

Q_alpha(y)-(y+c)^5
 =mu_*c^3y^2-5c^4y-c^5.                             (A8)
```

Let `y_+(s;alpha),y_-(s;alpha)` be the two inverse branches born at the hub.
For positive `s` no critical value lies on the ray.  Hence the branches are
locally holomorphic in `alpha`, and

```text
partial_s y_j=1/partial_y Q_alpha(y_j).              (A9)
```

For finite `S`, the sum of the two integrals of
`|partial_s y_j|` is subharmonic in `alpha`.  Near the double hub the
singularity is `O(s^-1/2)`, locally uniformly, and is integrable.  The
quadratic terminal defect in (A8) gives the locally uniform monic-tract
limit after subtraction of the parameter-independent terminal normalizer.
Consequently

```text
U(alpha)=mathcal E(mu_*,phi(alpha))/|alpha|          (A10)
```

is subharmonic on the lifted sector.  Arm permutations under continuation
cancel in the pair sum.

## 4. Radial homogeneity

Choose a fifth-root sector mapping onto (A6).  Its opening is

```text
L=pi/5<pi.                                          (A11)
```

For `alpha=r e^{i theta}`, radial scaling gives

```text
U(r e^{i theta})=A(theta)/r.                        (A12)
```

In polar coordinates,

```text
Delta U=r^-3(A''+A).                                (A13)
```

Subharmonicity therefore means

```text
A''+A>=0                                            (A14)
```

in the distributional sense on the angular interval.

## 5. The short-interval maximum principle

Let `B` solve `B''+B=0` with the endpoint values of `A`; explicitly,

```text
B(t)=[A(0)sin(L-t)+A(L)sin(t)]/sin(L).              (A15)
```

Set `w=A-B`.  Then `w''+w>=0` and `w` has zero endpoint values.  If the
positive part `w_+` were nonzero, testing the distributional inequality
against `w_+` would give

```text
0<=-integral |w_+'|^2+integral |w_+|^2.             (A16)
```

But the Dirichlet Poincaré inequality on an interval of length `L<pi` gives

```text
integral |w_+'|^2 >= (pi/L)^2 integral |w_+|^2
                         > integral |w_+|^2,         (A17)
```

a contradiction.  Hence `A<=B`.

If both endpoint values are at most `-a`, then

```text
B(t)<=-a [sin(L-t)+sin(t)]/sin(L)<=-a,              (A18)
```

because

```text
[sin(L-t)+sin(t)]/sin(L)
 =cos(t-L/2)/cos(L/2)>=1                            (A19)
```

for `0<=t<=L`.  This proves Theorem A.

## 6. Closed exceptional fibre and claim boundary

The factorization, critical gaps, phase interval, fifth-root normalization,
terminal defect, radial Laplacian, and sine barrier are replayed exactly by
the checker.  The subharmonicity and weak maximum principle are proved in
Sections 3--5; they are analytic arguments rather than finite CAS identities.

Composed with `QuinticMuStarEndpointExcessCertificate.md`, the theorem closes
both `mu_*` punctures with the uniform strict bound `mathcal E<-3/8`.  This
removes the exceptional gap-zero fibres from the wall-sheet maximum principle.
The ordinary compact double-tight atlas still remains, so the composition does
not yet prove `EX-W`, `EX-U`, the model-to-real transfer, degree five, or
unrestricted Erdős 1041.
