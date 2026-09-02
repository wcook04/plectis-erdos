# Erdős 1041: the quintic trace-max excess is a compact universal three-real-variable problem

Date: 2026-08-30.  Checker:
`scripts/check_erdos1041_quintic_trace_max_universal_chamber.py`.  Lean:
`QuinticTraceMaxUniversalChamber.lean` checks the exact centering, derivative,
and critical-gap algebra.

## 1. Why this coordinate is useful

The remaining metric obligation in the quintic star-kernel route is

```text
(EX)   E_pair(H,c) <= 0
```

for the two lifts of the rightward ray from a trace-maximal critical point
`c` of

```text
H(z) = z^5 + b_2 z^2 + b_1 z.
```

The coefficient-core presentation uses three real parameters after its
normalization, but it hides two facts seen in the computation: the magnitude
of the chosen hub is only an overall scale, and trace-maximality is itself an
exact algebraic chamber condition.  The reduction below exposes both.  It
does not prove (EX), but it turns (EX) into one universal compact certification
problem and proves an explicit, if deliberately crude, outer radius for that
problem.

## 2. Exact hub-centred normal form

Let `c != 0` be a critical point and put

```text
mu  = b_2/c^3,
phi = arg(c^5).
```

The critical equation gives `b_1 = -(5+2mu)c^4`.  With `z=c(1+x)`, direct
expansion gives the exact identity

```text
H(c(1+x))-H(c) = c^5 F_mu(x),
F_mu(x) = x^2 (x^3+5x^2+10x+10+mu).                 (U1)
```

Likewise

```text
H'(c(1+x)) = c^4 x C_mu(x),
C_mu(x) = 5x^3+20x^2+30x+20+2mu.                    (U2)
```

Thus the other three critical points are `c(1+x_j)`, where the `x_j`
are the roots of `C_mu`.  At such a root the gap from the selected critical
value simplifies without `mu`:

```text
H(c)-H(c(1+x_j)) = c^5 g(x_j),
g(x) = (1/2)x^3(3x^2+10x+10).                        (U3)
```

There is a second useful collapse hidden by (U3).  Reducing once more by
`C_mu(x)=0` gives the quadratic formula

```text
g(x) = x(2mu+20-3mu x)/5.                             (U3q)
```

Equivalently, after `y=x+4/3`,

```text
y^3 +(2/3)y +20/27 +(2/5)mu = 0,
g = -(3y-4)(3mu y-6mu-20)/15.                         (U3d)
```

Thus the chamber inequalities can be evaluated from a depressed cubic and
a bilinear gap expression rather than a quintic evaluation.  This does not
change the chamber dimension, but it lowers the algebraic degree of a future
interval implementation.  The tangent checker and Lean companion replay
both identities exactly.

The three gap values are the roots of the explicit cubic

```text
3125 y^3 + 12500(mu+4)y^2
 +(-4500mu^3+7500mu^2+150000mu+300000)y
 +(108mu^5+3800mu^4+50000mu^3+300000mu^2
   +800000mu+800000) = 0.                            (U4)
```

In particular `sum_j g(x_j)=-4(mu+4)`, agreeing with the critical-value
trace identity because `H(c)=-(mu+4)c^5`.

## 3. The universal trace-max chamber

Define `C_5` to be the set of pairs `(mu,phi) in C x (R/2piZ)` such that,
for all three roots of `C_mu` counted with multiplicity,

```text
Re(e^{i phi} g(x_j)) >= 0.                            (CH)
```

Equation (U3) says exactly:

> `c` is trace-maximal among the four critical points of `H` if and only if
> `(mu,phi)` satisfies (CH).

There is no lost non-pure case at `c=0`.  If `c=0` is critical, then `b_1=0`.
For `b_2 != 0`, the three nonzero critical points give a nonzero equilateral
triple of critical values with sum zero, so one has strictly positive real
part; hence zero is not trace-maximal.  If also `b_2=0`, `H=z^5` is the pure
power degeneration and the parent connector is trivial.

Now write `c^5=|c|^5 e^{i phi}`.  The rightward ray equation
`H(z)=H(c)+t`, `t>=0`, becomes, after `z=c(1+x)` and
`s=t/|c|^5`,

```text
F_mu(x) = e^{-i phi}s,   s>=0.                         (U5)
```

Let `mathcal E(mu,phi)` be the pair excess of the two branches of (U5)
born at `x=0`, measured as

```text
sum_arms lim (length_x(0 to x)-|1+x|).
```

Lengths and terminal moduli both scale by `|c|`, so

```text
E_pair(H,c) = |c| mathcal E(mu,phi).                   (U6)
```

This proves that the observed correlation with `|c|` is not merely
statistical: hub modulus is the exact multiplicative coercivity coordinate.
The sign problem contains no coefficient magnitude at all.

## 4. The chamber is compact, with an explicit outer radius

The non-obvious point is that `mu` cannot escape to infinity while (CH)
holds.  Here is a quantitative proof.

Choose `lambda` with

```text
lambda^3 = -2mu/5
```

and put `x=lambda y`.  The other-critical equation becomes

```text
y^3-1 +(4/lambda)y^2 +(6/lambda^2)y +4/lambda^3 = 0.  (U7)
```

Assume `|lambda|>=30` and put `r=3/50`.  On each circle
`|y-omega^j|=r`, where `omega^3=1`, the unperturbed term has the lower
bound

```text
|y^3-1| >= r(sqrt(3)-r)^2
          > (3/50)(17/10-3/50)^2 = 5043/31250,
```

whereas the perturbation in (U7) is at most

```text
(4/30)(53/50)^2 +(6/30^2)(53/50)+4/30^3
  = 52997/337500 < 5043/31250.
```

Rouché therefore puts one root `y_j` in each of the three disks.  Normalize
the corresponding gaps by `(3/2)lambda^5`.  From (U3),

```text
g(lambda y)/((3/2)lambda^5)
  = y^5 +(10/(3lambda))y^4 +(10/(3lambda^2))y^3.
```

For `|y_j-omega^j|<3/50`, its distance from `(omega^j)^5` is less than

```text
(53/50)^5-1 +(1/9)(53/50)^4 +(1/270)(53/50)^3
  = 4074569711/8437500000 < 1/2.                       (U8)
```

The three ideal points `(omega^j)^5` form a unit equilateral triple.  After
any common rotation, one has real part at most `-1/2` (one of their arguments
lies within `60 degrees` of the negative real axis).  The strict error in
(U8) leaves that gap with negative real part.  This contradicts (CH).
Consequently

```text
(mu,phi) in C_5  ==>  |lambda|<30  ==>  |mu|<67500.     (U9)
```

The chamber is closed: along a convergent sequence, take convergent
subsequences of the phases and of a labelling of the three polynomial roots;
(CH) passes to the limit.  Combining closedness with (U9) makes `C_5`
compact.  The constant `67500` is a proof convenience, not a proposed sharp
radius.

## 5. Exact real-axis chamber classification

The whole slice `mu in R` can be classified exactly.  Put

```text
Q(M) = 27M^5+5450M^4+23000M^3-105000M^2-700000M-1000000.
```

It has exactly three real roots

```text
alpha_1 in (-198,-197),  alpha_2 in (-4,-3),  alpha_3 in (5,6),
```

numerically

```text
alpha_1=-197.4409737432...,
alpha_2=  -3.8418987272...,
alpha_3=   5.2478789224....
```

Then the exact real slice of the universal chamber is

```text
{mu in R : exists phi, (mu,phi) in C_5}
 = [alpha_1,-10] union [alpha_2,alpha_3]
     union {50+30sqrt(3)}.                               (R1)
```

Proof.  The discriminant of `C_mu` is

```text
-100(27mu^2+100mu+100)<0,
```

so it has one real root `r` and one conjugate pair.  The corresponding gaps
are `G` and `A+-iB`, with `G` real.  If `B!=0`, a common rotation puts all
three gaps in the closed right half-plane if and only if `GA>=0`: when
`G>0` the rotation must have `cos(phi)>=0`, and the conjugate inequalities
force `A cos(phi)>=|B sin(phi)|`, hence `A>=0`; the other sign is symmetric,
and `phi=0` or `pi` proves sufficiency.  If `B=0`, all three gaps are real
and the perpendicular rotation makes every projected real part zero.

The gap-cubic discriminant factors exactly as

```text
-156250000 (mu^2-100mu-200)^2
             (27mu^2+100mu+100)^3,
```

so `B=0` occurs precisely at `mu=50+-30sqrt(3)`.  The smaller point lies
inside the second interval of (R1); the larger is the isolated tangent point.
For `B!=0`, the only real zero of `G` is `mu=-10`.  Eliminating the real root
`r` from `A=0` and `C_mu(r)=0` gives exactly `Q(mu)=0`.  Sturm proves the
three isolating intervals above and no other real root.  Finally the rational
test points `mu=-425/2,-100,-75/16,0,25/2` alternate the sign of `GA` as

```text
negative, positive, negative, positive, negative,
```

which proves (R1), including its endpoints by closedness.  The checker
replays every discriminant/resultant and Sturm count exactly.

Thus `alpha_1` is the sharp radial extreme on the real `mu`-axis.  A global
reduced-coordinate search also finds no complex chamber point of larger
modulus, suggesting the stronger sharp bound `|mu|<=-alpha_1`; that last
two-dimensional assertion remains computational and is not used here.

## 6. Exact status of the closed boundary anchors

At the landed tangent representative, the small trace-max hub gives exactly

```text
mu = 40/(sqrt(3)-1)^3 = 50+30sqrt(3),
phi = -pi/2.
```

This is a boundary point of (CH).  The existing exact skip-pair certificate
proves a *straight two-ray connector* at this same hub with metric budget
`-0.0777592874...`.  The new
`QuinticTangentCurvedExcessCertificate.md` proves the stronger statement for
the canonical curved rightward inverse-ray pair itself.  Exact
resultant/Sturm slope control and rational transverse-oscillation bounds feed
the support--oscillation lemma and give, in the real tangent normal form,

```text
E_pair <= -19517458527181/5000000000000000 < 0.
```

Positive similarity transfers the sign to `mathcal E`, so (EX-U) is proved
at the isolated tangent point rather than merely rescued there by another
connector.

The slice `mu=0` is genuinely analytic: it is exactly the `b_2=0` one-face
family, and `OneFaceRadialScatteringTheorem.md` gives

```text
mathcal E(0,phi) <= 2(pi/5-1) < 0
```

whenever the corresponding hub is trace-maximal.

The repeated-critical endpoint `mu=-10` has a second exact point.  At
`phi=0`,

```text
F_{-10}(x)=x^3(x^2+5x+10),
```

and the limiting simple-hub pair is the conjugate pair born in directions
`+-2pi/3`.  `QuinticMinusTenCentralExcessCertificate.md` puts the whole upper
arm on one quadratic level curve, certifies it by a 256-cell exact rational
tangent partition plus an algebraic tail, and proves

```text
mathcal E(-10,0) < -2853/100000 < 0.                    (R2)
```

At the two ends of the same allowed arc, put

```text
phi_0=arctan(1/(2sqrt(2))).
```

`QuinticMinusTenEndpointExcessCertificate.md` treats the upper arms for both
signed parameters `q=+-1/(2sqrt(2))` on their exact quadratic level curves.
A 640-cell rational interval partition and a full degree-120 eliminated Sturm
turn bound prove

```text
mathcal E(-10,+-phi_0) < -1/80 < 0.                   (R3)
```

The later uniform certificate
`QuinticMinusTenFullArcExcessCertificate.md` uses the same signed quadratic
arms in fixed-box coordinates and exact rational anchor-plus-derivative
transport to prove

```text
mathcal E(-10,phi) < -1/100 < 0
```

for every `|phi|<=phi_0`.  Thus the entire `mu=-10` phase arc is closed.
The central and endpoint bounds (R2)--(R3) remain sharper at their respective
phases.

## 7. What is now left

The quintic model metric obligation is exactly the following compact
statement:

```text
for every simple-hub (mu,phi) in C_5,
mathcal E(mu,phi) <= 0.                                  (EX-U)
```

The isolated tangent boundary, the one-face point `mu=0`, and the entire
canonical `mu=-10` phase arc are now proved.  By
`QuinticChamberWallReduction.md`, the remaining universal model statement is
exactly (EX-W).  `QuinticWallSheetSubharmonicReduction.md` then removes one
more real dimension by proof: after dividing by the fifth root of the active
gap, the wall ray is fixed and
`mathcal E/|g_j|^(1/5)` is subharmonic on each regular lifted wall sheet.
Thus sign on the former two-real-dimensional wall is controlled by its
one-real-dimensional double-tight boundary and explicit puncture limits.

The later `QuinticDoubleTightCriticalValueCarrier.md` eliminates ordered
critical-root labels from that boundary.  Its unordered invariant
`kappa=t/(1+t^2)` has exactly five physical event values, four regular
intervals, and five upper-half-plane `mu` branches per interval; a single
compact arm parameter is regular at both the hub and infinity.  Thus the
ordinary boundary residual is a finite `4 x 5 x 2 x [0,1]` sign atlas.

The direction-dependent nonzero-active limits over `mu=-10` are now closed
by `QuinticMinusTenWallLimitSideArmCertificate.md`, which certifies all three
tract-pair resolutions.  The two gap-zero fibres
`mu=(-70+-10i sqrt(5))/27` are also closed: the exact endpoint theorem
`QuinticMuStarEndpointExcessCertificate.md` gives the two representative
pairs below `-3/8`, and `QuinticMuStarAngularFiberReduction.md` (independently,
the global theorem `PhiConvexitySturmBound.md`) propagates that bound across
each full phase half-circle.  Thus the compact ordinary double-tight atlas is
the sole remaining model-wall obligation.  `QuinticDoubleTightCompactAtlas.md`
further excises relative negative neighborhoods of all three interior event
fibres `kappa_-,0,kappa_+`, using two fresh certified point margins and the
already-closed exceptional limits.  Hence only disjoint compact truncations
of the twenty regular branch traces remain.  The regular chamber interior is
already subsumed by the two successive maximum-principle reductions.  The
factorization (U6) means no interval is needed for `|c|`.

This is a strict reduction and an explicit compactification, not a proof of
(EX-U), the real-scale transfer, degree five, or unrestricted Erdős 1041.
The checker proves all polynomial identities exactly, verifies the rational
Rouché budget and the real-axis Sturm classification, confirms (U6) on
independent random instances, and replays the tangent coordinate.  The
separate tangent, full-arc, wall-sheet, side-arm, critical-value-carrier,
`mu_*` endpoint, and angular-fibre checkers certify their respective finite
algebraic and curved-ray inputs.
