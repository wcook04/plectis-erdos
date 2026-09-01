# Erdős 1041: compact unordered critical-value carrier for every double-tight wall

Date: 2026-08-30. Exact checker:
`scripts/check_erdos1041_quintic_double_tight_critical_value_carrier.py`.
Consumes `QuinticWallSheetSubharmonicReduction.md`.

## 1. Result

The weighted wall-sheet maximum principle reduces regular `EX-W` sheets to
their double-tight boundary.  The first exact boundary carrier used an
ordered pair of critical roots and a degree-ten polynomial in that root.
This note removes the root labels altogether.

> **Theorem CV.**  Every regular unordered double-tight gap pair is carried
> by one degree-ten equation
>
> ```text
> K_kappa(mu)=0,       -1/2<kappa<1/2,               (CV1)
> ```
>
> with exactly five upper-half-plane `mu` branches on each of four explicit
> regular `kappa` intervals.  The pair direction and the third gap are
> rational functions of `(kappa,mu)`, with a denominator proved nonzero on
> every regular physical fibre.  All branch events are
>
> ```text
> kappa=-1/2, kappa_-, 0, kappa_+, 1/2,
> kappa_+-=(1+-3sqrt(3))/13.                         (CV2)
> ```
>
> On every such branch the two inverse-ray arms admit one compact parameter
> `0<=r<=1` which is regular at both the double hub and infinity.  Their
> excess is an ordinary finite-interval integral with a nonnegative bending
> density.

This is a strict finite-dimensional reduction: the remaining double-tight
sign problem is a four-interval, five-branch, two-arm compact atlas.  The
note does **not** claim that this final interval atlas or its negative bound
has already been executed.

## 2. The cubic of critical gaps

For

```text
C_mu(x)=5x^3+20x^2+30x+20+2mu,
g(x)=(1/2)x^3(3x^2+10x+10),
```

exact elimination gives

```text
Res_x(C_mu(x),Y-g(x))=-3125 Q_mu(Y),                 (CV3)

Q_mu(Y)=Y^3+A Y^2+B Y+C,
A=4(mu+4),
B=-(12/25)(3mu^3-5mu^2-100mu-200),
C=(4/3125)(mu+10)^3(27mu^2+140mu+200).              (CV4)
```

Thus the three roots of `Q_mu` are exactly the three critical gaps.  Let
`a,b` be an unordered double-tight pair, put

```text
p=a+b,  q=ab,  h=-A-p,
kappa=ab/(a^2+b^2).                                  (CV5)
```

If the ordered ratio is `t=b/a in [-1,1]`, then

```text
kappa=t/(1+t^2) in [-1/2,1/2].                      (CV6)
```

The two identities

```text
kappa+1/2=(t+1)^2/[2(1+t^2)],
1/2-kappa=(t-1)^2/[2(1+t^2)]
```

make the compact range exact.

## 3. Elimination and rational reconstruction

Vieta and (CV5) give

```text
kappa p^2=(1+2kappa)q,
q-Ap-p^2=B,
q(A+p)=C.                                           (CV7)
```

Eliminating `p,q` produces `(1+2kappa)^2 K_kappa(mu)`, where

```text
K=C^2(1+kappa)^3
  -ABC kappa(1+kappa)(1+4kappa)
  +(A^3C+B^3)kappa^2(1+2kappa)
  -A^2B^2 kappa^3.                                  (CV8)
```

There are no algebraic impostors hidden in this carrier.  If `a,b,h` are
the three roots of `Q_mu`, exact symmetric expansion gives

```text
K=- product_{unordered {u,v} subset {a,b,h}}
       [kappa(u^2+v^2)-uv].                         (CV8a)
```

Thus every finite root of `K` is one of the three unordered pair ratios;
the chamber and reality filters decide which factors are physical.

Away from the event `kappa=0`, reduction of (CV7) recovers

```text
p=[C(1+kappa)^2-AB kappa^2]/[kappa D],
D=A^2 kappa-B(1+kappa),
h=-A-p.                                             (CV9)
```

For `-1<t<=1`, `p=(1+t)a` has the active-gap direction.  Define

```text
epsilon=-sign Im(conj(p)h),
d=e^{-i phi}=-epsilon i p/|p|.                      (CV10)
```

Then both selected gaps are tight and

```text
Re(e^{i phi}h)
 =-epsilon Im(conj(p)h)/|p| >=0,                    (CV11)
```

so (CV10) reconstructs the chamber ray without recovering either critical
root.  At `Im(conj(p)h)=0`, both signs are the triple-tight event.

## 4. Complete event calculation

Put `Khat=5^10 K`.  It is degree ten in `mu`, with leading coefficient

```text
11664(1+kappa)^3.                                   (CV12)
```

The exact discriminant resultant, up to a nonzero rational constant, is

```text
kappa^14(kappa+1)^3(2kappa-1)^6(2kappa+1)^5
(14kappa+9)(13kappa^2-2kappa-2)^2
(1553kappa^2-1312kappa+288)^3 J(kappa)^2,           (CV13)

J=2634375kappa^9-1903125kappa^8-837500kappa^7
  +459000kappa^6+334450kappa^5-91554kappa^4
  -57716kappa^3+13176kappa^2+3159kappa-729.
```

The reconstruction-denominator resultant is, again up to a nonzero
constant,

```text
Res_mu(Khat,25D)=(kappa+1)J(kappa)^2.                (CV14)
```

Exact Sturm and discriminant checks give

```text
# roots J on [-1/2,1/2] = 0,
disc(1553kappa^2-1312kappa+288)=-67712<0,
-9/14<-1/2.                                         (CV15)
```

Hence (CV2) is the complete physical event list and `D` never vanishes on a
regular physical fibre.  Exact isolators are

```text
-1/3<kappa_-<-8/25,
19/40<kappa_+<12/25.                                (CV16)
```

At the representatives

```text
-2/5, -1/10, 1/5, 49/100,
```

Sturm gives zero real `mu` roots.  Between events the discriminant and
leading coefficient do not vanish; since `Khat` has real coefficients and
degree ten, every one of the four regular intervals therefore has exactly
five upper-half-plane branches and their conjugates.

The finite event fibres are also exact:

```text
Khat(0)=16(mu+10)^6(27mu^2+140mu+200)^2,             (CV17)

Khat(-1/2)=2(27mu^5+5450mu^4+23000mu^3
               -105000mu^2-700000mu-1000000)^2,    (CV18)

Khat(1/2)=2(mu^2-100mu-200)^2
             (27mu^2+100mu+100)^3.                 (CV19)
```

At `kappa_-`, `mu=50+30sqrt(3)` is exactly double; at `kappa_+`,
`mu=50-30sqrt(3)` is exactly double.  After division by these squares, the
degree-eight quotients are squarefree.  These are the two real triple-tight
fibres.

### 4.1 The triple-tight crossings have finite linear slopes

The double roots in the projected `(kappa,mu)` carrier are transverse
conjugate crossings, not square-root branch points.  At either event,

```text
K=K_mu=K_kappa=0.
```

Writing `mu=mu_0+z(kappa-kappa_0)+O((kappa-kappa_0)^2)`, the first nonzero
Taylor equation is

```text
K_{mu mu} z^2+2K_{mu kappa}z+K_{kappa kappa}=0.     (CV19a)
```

After removing a nonzero real factor, (CV19a) is respectively

```text
kappa_- , mu_+=50+30sqrt(3):
 z^2+(388+228sqrt(3))z+459744+265392sqrt(3)=0,

kappa_+ , mu_-=50-30sqrt(3):
 z^2+(388-228sqrt(3))z+459744-265392sqrt(3)=0.      (CV19b)
```

Thus the exact slopes are

```text
-194-114sqrt(3) +- 2i sqrt(95780+55290sqrt(3)),
-194+114sqrt(3) +- 2i sqrt(95780-55290sqrt(3)),     (CV19c)
```

and both quadratic discriminants are strictly negative.  A certified atlas
can therefore cross either triple-tight value with finite one-sided linear
charts; the upper-half-plane representative switches between the conjugate
slopes at the real crossing.

### 4.2 Regular Newton coordinates at `kappa=0`

The apparent high multiplicities in (CV17) also have small exact local
coordinates.  At `mu=-10`, give `delta=mu+10` weight one and `kappa` weight
three.  Substitution

```text
delta=s z,  kappa=s^3
```

shows that the coefficient of `s^6` in `K` is

```text
(2304/625)(z^6+16200z^3+590490000).
```

Equivalently, for the Newton coordinate

```text
q=(mu+10)^3/kappa,
```

the leading equation is

```text
(2304/625)(q^2+16200q+590490000)=0,
q=-8100 +- 16200i sqrt(2).                          (CV19d)
```

Both roots are simple.  They are the algebraic three-lobe directions of the
nonzero-active `mu=-10` puncture.

For

```text
mu_*=(-70+10i sqrt(5))/27,
mu-mu_*=q kappa,
```

the coefficient of `kappa^2` in `K` is a nonzero constant times

```text
q^2+[(-28+4i sqrt(5))/15]q
   +(352-112i sqrt(5))/675.                         (CV19e)
```

Its discriminant is

```text
(704-224i sqrt(5))/675 != 0,                        (CV19f)
```

so the two endpoint branches at `mu_*` are ordinary linear Newton charts.
Conjugation supplies the charts at the other root of
`27mu^2+140mu+200`.

### 4.3 Exact branch derivatives for one-dimensional certification

On a regular branch, implicit differentiation and (CV9) give

```text
mu'=-K_kappa/K_mu,
p'=P_kappa+P_mu mu',
phi'=-Im(p'/p),                                     (CV19g)
```

where `P(kappa,mu)` denotes the rational expression for `p` in (CV9), and
prime means `d/dkappa`.  The last identity follows from
`e^{-i phi}=-epsilon i p/|p|`; `epsilon` is constant on a regular chamber
cell.

Consequently, if a certified wall cell supplies

```text
G_mu >= |grad_mu mathcal E|,
G_phi >= |partial_phi mathcal E|,
```

then the exact chain rule and triangle inequality give the transport bound

```text
|d mathcal E/dkappa|
 <= G_mu |K_kappa/K_mu|
    +G_phi |Im((P_kappa+P_mu mu')/P)|.              (CV19h)
```

Thus a point enclosure `mathcal E(kappa_0)<=-m` and a cell enclosure of the
right side by `L` close every point with
`|kappa-kappa_0|<m/L`.  Formula (CV19h) is a proved reduction of the future
covering calculation; this note does not claim that the required gradient
cells or negative point enclosures have already been executed.

## 5. A single compact arm chart

For the reconstructed chamber ray `d`, set

```text
s=(r/(1-r))^10,
x=[r^5/(1-r)^2] y,        0<=r<=1.                  (CV20)
```

Multiplying `F_mu(x)=d s` by `(1-r)^10/r^10` gives the polynomial equation

```text
G(r,y)=r^15y^5+5r^10(1-r)^2y^4+10r^5(1-r)^4y^3
       +(10+mu)(1-r)^6y^2-d=0.                     (CV21)
```

It has the two regular endpoint equations

```text
G(0,y)=(10+mu)y^2-d,
G(1,y)=y^5-d.                                       (CV22)
```

Thus its two finite roots at `r=0` are precisely the double-hub arms, while
each endpoint `eta=y(1)` is a fifth root of the terminal ray direction.  For
`0<r<1`, the exact derivative identity is

```text
G_y=[(1-r)^8/r^5] F_mu'(x).                         (CV23)
```

On a regular chamber fibre the positive inverse ray contains no critical
value, so `G_y` never vanishes.  Each hub root therefore continues through
one closed compact interval directly to its terminal tract; no square-root
start excision and no infinite tail chart remain.

## 6. Exact finite-interval excess

Let

```text
A_r=r^5/(1-r)^2,
V=x_r=A_r' y-A_r G_r/G_y.                           (CV24)
```

For the arm ending at `eta`, `|eta|=1`, direct projection and the terminal
limit give

```text
e_arm=integral_0^1 D_eta(r) dr-Re(conj(eta)),
D_eta=|V|-Re(conj(eta)V)>=0.                        (CV25)
```

Indeed, with `X=eta(r/(1-r))^2`, coefficient comparison gives

```text
x=X-1-(mu/5)X^-2+((2mu+5)/5)X^-3
    -((mu+4)/5)X^-4+O(X^-5),                       (CV26)
```

so `|1+x|-Re(conj(eta)(1+x))->0`.  At the hub,
`V=5r^4y(0)+O(r^5)`, hence `D_eta=O(r^4)`.  At infinity the leading velocity
is longitudinal of size `O((1-r)^-3)` and its transverse remainder is
`O((1-r)^3)`, so

```text
D_eta=O((1-r)^9).                                   (CV27)
```

Whenever the denominator is positive, the exact rationalization

```text
D_eta=Im(conj(eta)V)^2/
      (|V|+Re(conj(eta)V))                          (CV28)
```

makes the nonnegative bending loss interval-friendly.  An atlas must prove
that denominator positive on a cell before using (CV28); otherwise it must
bound the original square-root expression.  No global forward-projection
assumption is made here.

## 7. New finite target and claim boundary

The former degree-ten critical-root cover required ordered-root recovery,
denominator-exception filtering, a hub singular chart, and a separate tail.
The exact target is now smaller:

```text
4 regular kappa intervals
x 5 upper-half-plane mu branches
x 2 hub arms
x 1 compact r interval.                             (CV29)
```

All algebraic identities, branch events, denominator safety, conjugate
branch count, finite triple-tight slopes, `kappa=0` Newton leading forms,
branch-derivative formulas, endpoint regularity, and the excess identity are
proved and replayed by the checker.  What remains is the interval-Newton
continuation, certified point values, and the DT-Lip covering calculation on
this compact carrier.  The formerly separate `mu_*` endpoint inequalities
are now closed by `QuinticMuStarEndpointExcessCertificate.md`, which proves
the exact bounds `E_+<-47/125` and `E_-<-2/5`; together with
`QuinticMuStarAngularFiberReduction.md` (or independently the global phase
Sturm theorem), this closes both gap-zero phase fibres.  Thus the compact
atlas in (CV29) is the sole remaining model-metric obligation.  The later
event-excision theorem `QuinticDoubleTightCompactAtlas.md` proves strict
negativity on relative neighborhoods of all three interior event fibres
`kappa_-,0,kappa_+`; consequently the effective residual consists only of
disjoint compact truncations of the twenty regular branches.  This note does
not itself prove those truncations, `EX-W`, `EX-U`, the model-to-real
transfer, degree five, or unrestricted Erdős 1041.
