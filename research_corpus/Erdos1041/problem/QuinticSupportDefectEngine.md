# Erdős 1041: square-root-free fixed-strip support certificate

Date: 2026-08-30. Exact replay:
`scripts/check_erdos1041_support_engine_point.py`.
Consumes `QuinticDoubleTightSupportStieltjesReduction.md`.

## 1. Result

The support--Stieltjes reduction can be certified without square roots,
angle functions, curvature isolation, or arclength quadrature.

> **Theorem FST (fixed-strip certificate).**  Split a rotated inverse-ray
> arm at its vertical turns and at fixed rational horizontal strip
> boundaries.  On every resulting monotone subarc, a rational polynomial
> inequality certifies an upper bound for the half-angle density.  The sum
> of that bound times the exact vertical variation, minus the terminal
> support, is an exact one-sided excess certificate.  Both the hub and
> terminal endpoints have regular polynomial charts.

The theorem supplies the final certificate format for the compact
double-tight atlas.  It does not assert that all parameter cells have
already been run.

## 2. Square-root-free cone test

Retain the notation of Theorem SS:

```text
H'(z)=A+iB,   R=sqrt(A^2+B^2),
f=|tan(arg(z_s)/2)|=|B|/(R+A).                      (FST1)
```

For every rational `tau>0`,

```text
f<=tau  iff  2 tau A-(1-tau^2)|B|>=0.              (FST2)
```

Indeed, with `g=A/|B|`, one has
`f=sqrt(1+g^2)-g`.  Squaring is reversible because the right-hand
inequality implies `g+tau>0`.  On a cell where `sigma=sign B` is fixed,
(FST2) is the polynomial inequality

```text
C_tau=2 tau A-(1-tau^2) sigma B >=0.                (FST3)
```

It also rules out a backward horizontal tangent at a boundary point with
`B=0`.

## 3. Exact fixed-strip upper sum

Split an arm first into its `B`-sign excursions and then at crossings of
the rational levels

```text
v=j/16.                                              (FST4)
```

Keep different excursions separate even when they visit the same strip.
If `tau_{ell,j}` satisfies (FST3) on one such subarc and
`Delta v_{ell,j}` is its exact vertical span, then

```text
e_arm <= sum_{ell,j} tau_{ell,j} Delta v_{ell,j}
         -Re(alpha).                                 (FST5)
```

This is just (SS7) and monotonicity of `v` on each excursion.  Dyadic
ceilings for `tau` make every comparison rational.  A checker may bisect a
strip or parameter cell until (FST3) has a strict sign; no numerical angle
is an acceptance input.

## 4. The cone test in the compact arm chart

In the compact chart (CV20)--(CV23),

```text
H'(z)=alpha^4 F'(x)
     =[r^5/(1-r)^8] alpha^4 G_y.                    (FST6)
```

The scalar factor is positive on `0<r<1` and cancels from (FST3).  Thus use

```text
A_tilde=Re(alpha^4 G_y),
B_tilde=Im(alpha^4 G_y).                             (FST7)
```

These quantities are regular at both endpoints.  At the hub,
`G_y=2(10+mu)y(0) !=0`; at the terminal endpoint,

```text
G_y(1,eta)=5 eta^4,
alpha^4 G_y(1,eta)=5.                               (FST8)
```

Since the level parameter increases with `r`, `B_tilde=0` is exactly a
vertical turn.

## 5. A regular terminal coordinate

Put `t=1-r` and

```text
y=eta r^-3(1+t^2 T).                                (FST9)
```

Then

```text
z=alpha x=r^2/t^2+r^2 T,
v=r^2 Im T,                                         (FST10)
```

so the divergent longitudinal term is real and the transverse coordinate
remains regular.  After substituting (FST9) in `G=0`, using `eta^5=d`, and
multiplying by `r^6/(t^2 eta^2)`, the exact terminal equation is

```text
J(t,T)=
 r^6 eta^3[5T+10t^2T^2+10t^4T^3+5t^6T^4+t^8T^5]
 +5eta^2r^4(1+t^2T)^4
 +10eta r^2t^2(1+t^2T)^3
 +(10+mu)t^4(1+t^2T)^2=0.                           (FST11)
```

At `t=0`,

```text
J(0,T)=5eta^2(eta T+1),
T(0)=-alpha,   J_T(0,T)=5eta^3 !=0.                 (FST12)
```

Thus strip crossings and cone bounds remain ordinary interval-Newton
obligations all the way to infinity.

## 6. First two exact complete carrier fibres

The replay checker binds the support engine to the complete degree-ten
carrier fibres at

```text
kappa=+-1/1000.                                      (FST13)
```

It Krawczyk-isolates all five upper-half-plane roots on each fibre.  The two
exceptional roots are near

```text
mu=-13.12127424757375+1.76377901069898 i  (kappa>0),
mu=-12.47621333187578+2.47296147674895 i  (kappa<0). (FST14)
```

For this weak branch the checker reconstructs the wall direction from the
unordered active pair, certifies the third-gap chamber sign, and runs both
compact arms on 2048 exact rational cells.  Monotone cells use (FST5);
cells containing a possible turn use the original nonnegative support
density.  The `k=16` tail theorem gives the exact rational comparison

```text
mathcal E < -1/36  (kappa>0),
mathcal E < -1/50  (kappa<0).                       (FST15)
```

The other four roots on each fibre have much larger margins and are
certified by the existing oriented-arclength point engine.  On each side the
five root balls are pairwise disjoint, lie strictly in the upper half-plane,
and exhaust the upper roots by Theorem CV.  The decimal upper endpoints are
approximately

```text
kappa=+1/1000:
 -0.03599, -1.1833, -0.9136, -1.2651, -1.0249;

kappa=-1/1000:
 -0.02170, -0.9898, -1.0977, -1.2652, -1.0247.      (FST16)
```

Thus both whole physical double-tight fibres have the uniform exact gap
`mathcal E<-1/50`.  These are fully certified fibres, not floating samples.

## 7. Finite remaining run

The exact atlas run now consists of carrier interval Newton, the two compact
arm continuations, isolation of `B_tilde=0` and `v=j/16`, dyadic (FST3)
checks, and the finite sum (FST5).  A uniform rational `r` subdivision such
as `j/32` is a convenient initial schedule, with exact bisection on rejected
cells.  This paragraph specifies an algorithm, not a completed coverage
claim.  The compact double-tight sign theorem and its downstream consumers
remain open until every parameter cell is accepted.
