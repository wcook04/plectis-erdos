# The complete fixed-template polyhedral cell around the block-L1 rescue

## Result

The quantitative square in `TiedNewtonFaceBlockL1RationalChart.md` is only an
inscribed patch.  The same hub, two arms, two tails, topology passport, and
metric budget work on a complete explicit open convex cell in the real
two-parameter family

~~~text
P_{a,b}(z)=-z^6+a z^2+b.
~~~

Keep

~~~text
h=7/10+(57/80)i,  R=5/4,
u=1,  v=1/2+(sqrt(3)/2)i.
~~~

For `w=u,v`, let `T_{w,j}+a S_{w,j}+b`, `0<=j<=6`, be the degree-six
Bernstein controls of `Re P_{a,b}` on `[h,Rw]`.  Define `C` by

~~~text
-1875/128 < a < 0,  b < 0,
T_{w,j}+a S_{w,j}+b < 0  for w=u,v and 0<=j<=6.            (1)
~~~

Then every `(a,b)` in `C` has:

- both complete finite arms strictly in `{Re P_{a,b}<0}`;
- both outward tails from radius `R` strictly in that half-plane preimage;
- one connected six-ended negative component containing those arms and tails;
- the same connector length, about `1.2776427568`, strictly below `2<2R`.

Thus `C` is a full exact semialgebraic chart cell.  It is unbounded in the
negative `b` direction and contains the closed square

~~~text
|a+3|<=1/192,  |b+5997001/10^9|<=1/192.                   (2)
~~~

## All affine controls

The `u`-arm sensitivities `S_{u,j}` are

~~~text
-113/6400, 2687/9600, 27061/48000, 26687/32000,
104687/96000, 4/3, 25/16,
~~~

and the corresponding constant controls `T_{u,j}` are

~~~text
-13814656687/262144000000,
274918973/327680000,
40742687/26214400,
46277/32768,
2825/65536,
-4375/2048,
-15625/4096.
~~~

The `v`-arm sensitivities are

~~~text
-113/6400,
-(-429+475 sqrt(3))/3200,
-(-2787+3800 sqrt(3))/16000,
-19(-173+450 sqrt(3))/32000,
-(2571+7600 sqrt(3))/32000,
-(19 sqrt(3)+48)/128,
-25/32,
~~~

and the constant controls are

~~~text
-13814656687/262144000000,
-(-2199351784+2403129063 sqrt(3))/5242880000,
-(1442784 sqrt(3)+40742687)/52428800,
-46277/32768,
-25(113+6384 sqrt(3))/131072,
-625(56+57 sqrt(3))/32768,
-15625/4096.
~~~

Direct substitution gives these fourteen affine expressions.  Condition
(1), followed by Bernstein convex-hull containment, proves both arms.

## Exact lower envelope

For a fixed `a`, condition (1) says

~~~text
b < F(a) := min_{w,j}(-T_{w,j}-a S_{w,j}).                 (3)
~~~

Only eight of the fourteen arm facets occur on the lower envelope over
`-1875/128<a<0`.  In increasing order of `a` they are

~~~text
V6, V4, V3, V2, V1, H, U1, U2,                            (4)
~~~

where `H=U0=V0` is the common hub control.  If adjacent labels in (4) are
`p,q`, their exact transition is

~~~text
a_{p,q}=(T_q-T_p)/(S_p-S_q),
b_{p,q}=-T_p-a_{p,q}S_p.                                  (5)
~~~

The seven transition abscissae are approximately

~~~text
-5.8164186673, -5.4566459939, -4.7806774434,
-3.9458149886, -3.0528004192, -2.9967353841,
-2.5195034549.
~~~

The last two are rational:

~~~text
a_{H,U1}=-701249505261/234004480000,
a_{U1,U2}=-468729229/186040320.
~~~

Formula (5), together with the explicit `S,T` table, is an exact radical
description of every other vertex.  The checker proves the ordering and,
on each resulting interval, compares the active affine function with all
thirteen competitors at both endpoints.  Linearity then proves (4) on the
whole interval.  This is finite exact elimination, not a sampled atlas.

## Tails and topology

On the `u` ray,

~~~text
Re P_{a,b}(ru)=-r^6+a r^2+b<0
~~~

for `a<0,b<0`.  On the `v` ray,

~~~text
G_{a,b}(r)=-r^6-(a/2)r^2+b.
~~~

Its derivative is `r(-6r^4-a)`.  Since

~~~text
a>-1875/128=-6R^4,
~~~

the derivative is strictly negative for every `r>=R`.  The cutoff condition
`G_{a,b}(R)<0` is exactly the endpoint facet `V6` in (1), because

~~~text
G_{a,b}(R)=-15625/4096-(25/32)a+b.
~~~

This proves both tails.

Finally

~~~text
P'_{a,b}(z)=-2z(3z^4-a).
~~~

For `a<0` its five critical points are simple.  The central critical value
is `b`; the other four are `b+(2a/3)z^2` with `z^2` purely imaginary.  All
five critical values therefore have real part `b<0`.  The component-degree
identity gives `6 = number of negative components + 5`, so there is one
six-ended component throughout `C`.

## Consequence and boundary

The fixed-template feasible set is no longer an unknown local continuity
neighbourhood: it is the exact cell (1)--(5).  A chart-cover argument can now
work with cell overlap, uncovered passports, and template changes instead of
re-solving arm strictness near this sextic.  This still covers only one
two-real-dimensional tied-face family; it is not an all-degree atlas, a dense
successful subclass, or a proof of unrestricted Erdős #1041.

The exact checker reconstructs the fourteen controls, proves the eight-facet
lower envelope and all transition comparisons, verifies (2), and checks the
tail/topology identities.  Lean checks the generic affine-cell consumer, the
tail cutoff identity, the derivative bracket, and the critical-value real-part
kernel.  Bernstein containment and the component-degree identity remain
ordinary proof.
