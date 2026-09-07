# Rational finite-connector rescue of the block-L1 sextic

## Result

The exact sextic that refutes pointwise component-block L1 contraction is
not a metric obstruction. Let

~~~text
x=999/1000,
epsilon=x^3+3x-4=-5997001/10^9,
Q(z)=-z^6-3z^2+epsilon.
~~~

As proved in TiedNewtonFaceBlockL1NoGo.md, {Re Q<0} is one connected
six-ended component and a regular negative fibre has block speed larger than
the regular baseline. Nevertheless the same component contains a strict
finite connector. Put

~~~text
h=7/10+(57/80)i,
R=5/4,
u=1,
v=1/2+(sqrt(3)/2)i.
~~~

The segments [h,Ru] and [h,Rv], followed by the radial tails in
directions u,v, lie strictly in {Re Q<0}, while

~~~text
|Ru-h|+|Rv-h| < 2 < 5/2 = 2R.                              (1)
~~~

Thus the block-L1 excess is an artefact of summing all six instantaneous
speeds. The target geometry already wins by jointly choosing one adjacent
end pair and a noncritical rational hub.

## Exact finite-arm certificates

Parameterize each arm by z(t)=h+t(Rw-h), 0<=t<=1. The degree-six
Bernstein coefficients of Re Q(z(t)) on the u-arm are

~~~text
-187661814643/32768000000000,
-6859138399/1024000000000,
-293067436173/2048000000000,
-70121042439/64000000000,
-413998038003/128000000000,
-24568909879/4000000000,
-68065554133/8000000000.                                  (2)
~~~

Every entry is strictly negative. On the v-arm they are

~~~text
-187661814643/32768000000000,
-(-185279460616+213778321875 sqrt(3))/16384000000000,
(-5348002137971+2805682500000 sqrt(3))/4096000000000,
(-110490573689+51300000000 sqrt(3))/64000000000,
-19(-2876378401+6806250000 sqrt(3))/256000000000,
-(-3256816936+41080078125 sqrt(3))/64000000000,
-11815554133/8000000000.                                  (3)
~~~

The elementary bounds 3/2<sqrt(3)<7/4 make all seven signs in (3)
immediate. Bernstein convex-hull control proves strict negativity on both
complete arms.

## Exact tails

On the two selected rays,

~~~text
Re Q(ru)=-r^6-3r^2+epsilon <0,
Re Q(rv)=-r^6+(3/2)r^2+epsilon.                             (4)
~~~

The first is negative for every r>=0. For r>=R=5/4, the second is
strictly decreasing because

~~~text
d/dr[-r^6+(3/2)r^2+epsilon]=3r(1-2r^4)<0,
~~~

and at the cutoff

~~~text
Re Q(Rv)=-11815554133/8000000000<0.                         (5)
~~~

Hence both outward tails are strictly contained.

## Exact metric budget

The squared arm lengths are

~~~text
|Ru-h|^2=1037/1280,
|Rv-h|^2=2157/1280-(57/64)sqrt(3).                          (6)
~~~

The first is below one. The second is below one because
877<1140 sqrt(3), already implied by sqrt(3)>3/2.
Thus both arm lengths are below one, proving (1).

## Proof consequence

This closes the new sextic regression in the strongest useful way:

~~~text
one six-ended target component
  + pointwise full-block speed excess
  + strict rational finite connector.
~~~

Therefore neither pointwise full-block L1 nor an attempt to amortize that
entire excess is necessary for the tied-face metric theorem. A viable
arithmetic producer should target the action of one selected monodromy class;
the chart-cover producer should include this rational hub as a strict seed
cell. The strict inequalities also give a qualitative open coefficient
neighbourhood by continuity. No all-degree chart cover or unrestricted
Erdős #1041 proof is claimed.

## Formal boundary

The exact checker reconstructs the polynomial substitution, Bernstein
conversion, tail identities, and metric squares. Lean checks all coefficient
signs, the radical bounds, the tail endpoint/monotonicity consumer, and the
strict metric budget. The ordinary proof supplies Bernstein convex-hull
containment and the component-passport link already established in the no-go
source.
