# Erdős 1041: exact negative curved excess at the centre of the `mu=-10` stratum

Date: 2026-08-30.  Exact checker:
`scripts/check_erdos1041_quintic_minus_ten_central_excess.py`.  Lean algebra:
`QuinticMinusTenCentralExcessCertificate.lean`.

## 1. Result

In the universal quintic chamber of `QuinticTraceMaxUniversalChamber.md`, the
point

```text
(mu,phi)=(-10,0)
```

is a repeated-critical-point boundary.  The two simple-hub inverse branches
from the real chamber converge there to the conjugate branches of

```text
F(x)=F_{-10}(x)=x^3(x^2+5x+10),
F(x)=s,  s>=0,
```

born with arguments `+2pi/3` and `-2pi/3`.  Their curved inverse-ray pair
excess satisfies the exact bound

```text
mathcal E(-10,0) < -2853/100000 < 0.                 (M0)
```

Thus the centre of the `mu=-10` singular stratum is closed for the actual
curved pair.  This is not a substitute straight connector and is not merely a
floating-point sign.

The two other critical displacements are `-2+-i sqrt(2)`.  Their gaps from the
selected value are

```text
12 -+ 24 i sqrt(2),
```

while the coalesced critical gap is zero.  Hence `phi=0` satisfies the chamber
inequalities.  For real `mu<-10`, the two branches born at the selected simple
hub are conjugate; coefficient continuity identifies their `mu -> -10` limit
with the two non-real cubic branches above.

## 2. The complete branch is one quadratic curve

Write the upper branch as `x=a+ib`, with `b>0`.  Since the value ray is real,
`Im F(x)=0`.  Direct expansion gives

```text
Im F(a+ib)/b
 = b^4-10(a+1)^2 b^2+5a^2(a^2+4a+6).                (M1)
```

Put `t=a/b`.  After division by `b^2`, (M1) becomes

```text
Q(t,b)=A(t)b^2+B(t)b+C(t)=0,                         (M2)
A(t)=5t^4-10t^2+1,
B(t)=20t(t^2-1),
C(t)=10(3t^2-1).
```

Let `k` be the small positive root of

```text
5k^4-10k^2+1=0,
k=tan(pi/10)=0.324919696232906... .                  (M3)
```

The selected root of (M2) is a single continuous positive branch

```text
-1/sqrt(3) < t < k.                                  (M4)
```

It starts at `b=0`, which is the cubic direction `arg x=2pi/3`, and satisfies

```text
b(k-t) -> 1                                          (M5)
```

at infinity.  Thus `1+x` is asymptotic to the direction

```text
u=(k+i)/sqrt(1+k^2)=exp(2pi i/5).
```

Here are the exact global branch checks.  The discriminant of (M2) is

```text
-40(5t^6-15t^4+3t^2-1),
```

and its last factor has no zero on `[-3/5,1/3]`.  On the part `t<-k`,
the selected root is the smaller positive root and has `Q_b>0`; on
`-k<=t<k`, it is the unique positive root, again with `Q_b>0`.  Moreover
`Q_t` has no selected-branch zero.  The nonzero critical points
`-2+-i sqrt(2)` have non-real `F`-values, so this connected component of
`Im F=0` never stalls and is exactly the positive real inverse ray.

Finally, set `w=b(k-t)`.  Clearing denominators in (M2), substituting
`t=k-s`, and reducing by (M3) shows that the first nonzero terminal term is

```text
-20 k w (k-1)(k+1)(w-1)s.
```

This proves (M5) directly.

## 3. A finite tangent partition

Let `p=da/db` be the physical tangent slope.  Implicit differentiation of
(M2) gives

```text
p=t-b Q_b/Q_t.                                       (M6)
```

If `theta` is the signed angle from `u` to the tangent, then

```text
tan(|theta|/2)
 = |k-p| /
   (sqrt(1+p^2)sqrt(1+k^2)+1+pk).                    (M7)
```

The transverse coordinate relative to `u` is especially simple:

```text
Im(conj(u)(1+x))
 = (w-1)/sqrt(1+k^2).                                (M8)
```

On the initial wedge

```text
-1/sqrt(3) <= t <= -577/1000
```

the checker encloses the whole branch in the rational rectangle
`[-289/500,-577/1000] x [0,b(-577/1000)]`.  Exact interval arithmetic on
that rectangle proves `Q_b>0`, `Q_t<0`, `w'>0`, `p<k`, and that (M7) is less
than `1/2`; this supplies the whole initial-wedge variation bound, not only
an endpoint check.  From `-577/1000` to `0`, split the rational interval into
256 equal cells.  At every node the checker isolates the selected root of
(M2) between rational endpoints.  On every entire cell, exact natural
interval arithmetic proves

```text
Q_b>0,  Q_t<0,  w'>0,  p<k,
```

and evaluates an outward rational enclosure of (M7).  Multiplying each
cell's half-angle ceiling by its exact outward `w` increment gives

```text
sum_cells tan(|theta|/2) Delta w
  < 0.292353136726.                                  (M9)
```

Floating point chooses the small rational root boxes only.  The checker
accepts a box only after rational endpoint signs and rational interval
derivative signs prove it.

## 4. The infinite tail is algebraic

The tail `0<=t<k` does not require truncating the inverse ray.  Eliminating
`b` from (M2) and the level sets of (M6), followed by exact Sturm counts,
proves

```text
3/10 < p < 1/3.                                      (M10)
```

The two resultants have no zero on `0<t<1/3`; their sides are fixed exactly
at `t=0`, where `b=sqrt(10)` and `p=1/sqrt(10)`, using
`(3/10)^2<1/10<(1/3)^2`.

The terminal transverse coordinate obeys

```text
1 < w < 26/25.                                       (M11)
```

For the lower bound, substitute `t=ku` and `w=1` in the cleared form of
(M2).  Modulo (M3) it factors as

```text
(10k^2-1)(u-1)^3(3u+1),
```

which is negative for `0<=u<1`.  For `w=26/25`, the corresponding cubic in
`u` has four strictly negative Bernstein coefficients, so its cleared value
has the opposite sign.  Since `Q_b>0`, these signs give (M11).

Eliminating `b` and `k` from `Q=0` and `w'=0` leaves, apart from the terminal
factor `A(t)`, a degree-28 polynomial with exactly one root in `(0,1/3)`.
Thus `w` turns at most once on the tail.  Equations (M10)--(M11) therefore
give

```text
TV_tail(w)<2/25,
tan(|theta|/2)<1/80,
tail weighted budget < 1/1000.                       (M12)
```

Combining the initial wedge, (M9), and (M12), with outward rounding, gives

```text
J := integral tan(|theta|/2) |dw| < 309/1000.         (M13)
```

## 5. Negative fan-in

For a unit-speed arm, projection on its terminal direction gives

```text
e = integral (1-cos theta) ds - Re(conj(u)*1)
  = integral tan(|theta|/2) |d transverse| - Re(u)
  <= (J-k)/sqrt(1+k^2).                               (M14)
```

The lower arm is its conjugate and has the same excess.  The checker proves
the rational enclosures

```text
k > 324919696232906/10^15,
1/sqrt(1+k^2) > 951/1000,
J < 309/1000.
```

Therefore

```text
E_pair
 <= 2(951/1000)(309/1000-324919696232906/10^15)
 < -2853/100000,
```

which proves (M0).

## Claim boundary

This is an ordinary exact proof of the curved limiting-pair excess at the
single central point `(mu,phi)=(-10,0)`.  The Python checker is the authority
for the Sturm, resultant, Bernstein, and rational interval certificate.  The
Lean companion checks the singular normal form, level-curve factorization,
terminal algebra, and final rational arithmetic.

`QuinticMinusTenEndpointExcessCertificate.md` closes both endpoints of the
allowed `mu=-10` phase arc, and the later uniform theorem
`QuinticMinusTenFullArcExcessCertificate.md` closes every phase between them.
Thus the complete canonical singular obligation (EX-10) is now discharged.
This note itself remains the sharper pointwise central certificate.  The
weighted wall-sheet maximum principle reduces regular (EX-W) to its
one-dimensional double-tight boundary and explicit puncture limits; it does
not automatically identify every direction-dependent simple-hub tract-pair
limit at `mu=-10` with the canonical pair certified here.  Those residual
wall limits, the other (EX-W) branches, actual-polynomial real-scale transfer,
degree five, and unrestricted Erdős 1041 remain open.
