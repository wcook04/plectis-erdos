# Erdős 1041: all `mu=-10` wall-limit resolutions are negative

Date: 2026-08-30. Exact checker:
`scripts/check_erdos1041_quintic_minus_ten_wall_limit_side_arm.py`.
Consumes `QuinticMinusTenEndpointExcessCertificate.md` and
`QuinticMinusTenFullArcExcessCertificate.md`.

## 1. Result

At `mu=-10`,

```text
F(x)=x^3(x^2+5x+10),
G_+=12+24 i sqrt(2),  G_-=12-24 i sqrt(2),
phi_0=arctan(1/(2sqrt(2))).
```

The full-arc theorem proves negativity for the canonical pair of inverse-ray
arms on every allowed phase.  A regular wall sheet can, however, converge to
the triple hub through three different approach lobes.  At the two phases
`+-phi_0` forced by a nonzero active gap, the limiting tract pairs are

```text
{T_0,T_1},  {T_1,T_4},  {T_0,T_4}.                  (S0)
```

The middle pair is the canonical pair already certified.  This note proves
the one missing shallow arm estimate

```text
e_0 < -13/15.                                        (S1)
```

Together with the exact endpoint-arm bounds

```text
e_- < 1/10,             e_+ < -9/80,                 (S2)
```

it gives the three exact pair ceilings

```text
e_-+e_+ < -1/80,
e_0+e_- < -23/30,
e_0+e_+ < -47/48.                                    (S3)
```

Conjugation gives the opposite phase.  Thus every direction-dependent
`mu=-10` puncture limit occurring in the wall-sheet maximum principle is
strictly negative.  This closes that puncture obligation; it does not by
itself certify the double-tight boundary or the two `mu_*` punctures.

## 2. Why there are three limiting pairs

Put `delta=mu+10`.  The critical point collapsing into the fixed hub has
the exact local expansions

```text
x_0=-delta/15-2delta^2/675+O(delta^3),
g(x_0)=-delta^3/675+O(delta^4).                      (S4)
```

The other critical gaps tend to `G_+` and `G_-`.  On a sheet whose active
gap tends to one of these nonzero values, tightness and the remaining chamber
inequality force the limiting phase to `+phi_0` or `-phi_0`.  The argument of
the cubic leading term in (S4) partitions the punctured `delta`-disc into
three approach lobes, centered at

```text
pi/3,  pi,  5pi/3,
```

with half-width `pi/6+phi_0/3`.  In cyclic order, the two square-root arms at
the ordinary double hub limit to the three unordered pairs in (S0).  This is
also visible directly by matching the three cubic start directions

```text
3 theta = -phi  (mod 2pi)
```

to the five monic terminal directions

```text
5 theta = -phi  (mod 2pi).
```

Only the shallow `T_0` arm is absent from the canonical resolution.  At
`+phi_0` it is the conjugate of the upper shallow arm for `q=-q_0`, where
`q_0=1/(2sqrt(2))`; it is therefore enough to certify that signed upper arm.

## 3. Exact algebraic curve for the shallow arm

Use the endpoint certificate's upper-half-plane coordinates

```text
x=b(t+i),
Q_q(t,b)=A_q(t)b^2+B_q(t)b+C_q(t)=0,
w=b(k-t).                                            (S5)
```

The shallow arm starts with `b=w=0`.  Its start direction
`r=cot(phi_0/3)` is the isolated large positive root of

```text
R(t)=t^6-78t^4+57t^2-8,                             (S6)

8.789971897990956 < r < 8.789971897990957,
q=-(3r^2-1)/(r^3-3r)=-q_0.
```

Its terminal direction `k=cot(phi_0/5)` is the isolated large positive root
of

```text
K(t)=8(5t^4-10t^2+1)^2-(t^5-10t^3+5t)^2,           (S7)

14.690277053249349 < k < 14.690277053249350,
q=-(5k^4-10k^2+1)/(k^5-10k^3+5k)=-q_0.
```

Let `S_q(k,t,w)` be the transverse quadratic from the endpoint theorem.  It
satisfies

```text
S(k,t,0)=10(k-t)H(t),
H=q(t^3-3t)+3t^2-1,

S(k,t,1)=-(k-t)^2 H_1(k,t),
H_1=k^2q+3kqt+5k+6qt^2-10q+15t.                    (S8)
```

On the complete rectangle from the isolated `r` box to the isolated `k`
box, 128 exact rational interval cells prove

```text
H'(t)<0,        H_1(k,t)<0,
coefficient_{w^2} S=-D_q(k,t)>0.                    (S9)
```

Since `H(r)=0`, (S8)-(S9) give `S(0)<0<S(1)` in the
interior.  The product of the two quadratic roots is negative, so there is
exactly one positive root, it lies in `0<w<1`, and `S_w>0` on it.  This
proves a global glued branch without a numerical root atlas; its endpoint
limits are `w=0` and `w=1`.

## 4. A degree-110 no-turn certificate

On an implicit branch, a turn of `w` satisfies

```text
(k-t) partial_t Q+b partial_b Q=0.                  (S10)
```

Eliminate `b`, substitute the exact terminal relation
`q=-(5k^4-10k^2+1)/(k^5-10k^3+5k)`, and eliminate `k` with (S7).  The
square-free stationary eliminant has degree 120.  The checker proves exact
division

```text
E_120(t)=K(t) E_110(t).                              (S11)
```

Exact Sturm counts on the deliberately broad rational interval
`[8.7899,14.7]` are

```text
# roots E_120 = 1,    # roots K = 1,    # roots E_110 = 0.   (S12)
```

The sole root is the terminal root `t=k`; hence the selected open branch has
no turn.  At the rational section `t=10`, exact signs isolate its root in

```text
0.430<w<0.433,       S_w>0,       S_t<0.            (S13)
```

Thus `w_t=-S_t/S_w>0` there and therefore everywhere: `w` increases from
zero to one.  In particular its terminal limit cannot be the zero root of
`S(k,k,w)`; the section value in (S13) and monotonicity force the other root,
`w=1`.

## 5. Outward orientation and the large negative support payment

The algebraic graph must still be identified with the outward inverse-ray
arm.  This costs no atlas.  The nonzero zeros and critical points of `F` are

```text
(-5+-i sqrt(15))/2,       -2+-i sqrt(2),             (S14)
```

whose upper-half-plane `t=Re(x)/Im(x)` coordinates are respectively
`-5/sqrt(15)<-1` and `-sqrt(2)<-1`.  Our graph stays in `t>r>8`, so neither
`F` nor `F'` vanishes on it.  Near the cubic start,

```text
Re(10(r+i)^3)=10(r^3-3r)>0,
```

so it begins on the positive ray.  Moreover `w_t>0` gives

```text
b_t=w_t/(k-t)+w/(k-t)^2>0.
```

Thus `x_t` is nonzero.  The derivative of the ray scalar cannot vanish,
because that would give `F'(x)x_t=0`; its initial positive orientation is
therefore preserved.  This proves that the glued graph is precisely the
outward lift used in the excess definition.

Let `p=da/db` be the physical tangent slope.  The stable formula from the
endpoint certificate is

```text
p=t+w(k-t)S_w/[wS_w-(k-t)S_t].                      (S15)
```

All terms added to `t` are positive, so `p>t>0`.  The physical tangent and
the terminal direction `(k,1)` therefore have positive dot product.  Their
angle is less than `pi/2`, and its half-angle factor `h` is strictly below
one.  By monotonicity,

```text
J=integral h |dw|=integral_0^1 h dw < 1.            (S16)
```

The exact projection identity of the endpoint theorem gives

```text
e_0 <= (J-k)/sqrt(1+k^2)
    < (1-k)/sqrt(1+k^2)
    < -(k-1)/(k+1)
    < -13/15,                                       (S17)
```

where the last comparison is exactly `k>14`.  Equations (S2)-(S3) now close
all three wall-limit resolutions.

## 6. Claim boundary

The checker is exact for the algebraic endpoint isolation, the global branch
signs, the Sturm no-turn theorem, and the rational fan-in.  The analytic
support inequality used in (S16) is the already proved identity (E13) of
`QuinticMinusTenEndpointExcessCertificate.md`.  No floating-point value is a
proof input.  The result closes only the `mu=-10` punctures of the wall-sheet
reduction; `mu_*` endpoint rays and the ordinary double-tight carrier remain
separate obligations.
