# Exact no-go for hubwise horizontal-fibre negativity

## Result

The strict horizontal-fibre defect cannot be negative at every negative
critical point.  This fails already for the real quintic

```text
Q(z)=15z+5z^2-z^5.                                           (1)
```

At the simple negative critical point `c=-1`, the two lifts of the leftward
real ray have renormalized total-length defect at least

```text
(sqrt(5)-1)/2 > 0.                                           (2)
```

Thus any horizontal-fibre proof of the tied-face selector must retain the
existential minimum over negative critical points, or replace it by a genuine
component aggregate.  The example does not refute that existential statement.

## Critical values on the lifted ray

Differentiation and exact factorization give

```text
Q'(z)=15+10z-5z^4=-5(z+1)(z^3-z^2+z-3).                    (3)
```

Hence `c=-1` is simple,

```text
Q(-1)=-9,                 Q''(-1)=30.                       (4)
```

The cubic in (3) has exactly one real root: its derivative
`3x^2-2x+1` is strictly positive.  That root lies in `(1,2)`, and at any
root `r` of the cubic the critical equation gives

```text
Q(r)=3r(r+4)>0.                                              (5)
```

The other two critical points are nonreal and their critical values are
nonreal.  Indeed, again `Q(z)=3z(z+4)` at such a point.  If this were real,
writing `z=x+iy`, `y != 0`, would force `x=-2`.  Substitution of
`z=-2+iy` into the cubic forces simultaneously `y^2=17` from the imaginary
part and `7y^2=17` from the real part, a contradiction.  Consequently the
open real ray `(-infinity,-9)` contains no critical value.

The local square-root normal form at (4) produces one conjugate pair of
simple lifts

```text
Q(gamma_+(t))=Q(gamma_-(t))=-9-t,       t>0,                (6)
```

initially in the upper-left and lower-left quadrants.  Since (6) encounters no
critical value, the pair continues for all `t>0` and never becomes real.

## The sectors are forced

On the imaginary axis,

```text
Q(iy)=-5y^2+i(15y-y^5).                                    (7)
```

For the levels in (6), the only crossings are

```text
z=+/- i 15^(1/4),             Q(z)=-5 sqrt(15)<-9.          (8)
```

At the upper crossing, with `a=15^(1/4)`,

```text
Q'(ia)=-60+10ia,
Re(1/Q'(ia))=-60/(3600+100 sqrt(15))<0.                     (9)
```

As the real value decreases, (9) makes the upper lift cross from the left
half-plane to the right half-plane.  It cannot cross back: (7) supplies only
the single eligible upper crossing point and a lift of the real ray cannot
visit that point at two different parameter values.  The lower lift is its
conjugate.  Since neither lift can become real, their asymptotic fifth-root
directions are therefore

```text
omega=exp(2 pi i/5),                conjugate(omega).        (10)
```

This is the only analytic continuation step in the proof.  It uses the
absence of critical values on the ray, conjugation, the exact crossing list,
and the standard inverse-polynomial asymptotics.

## Positive defect from Euclidean displacement

Let `z_+(T),z_-(T)` be the endpoints after lifting to value `-9-T`, and let
`L(T)` be the sum of the two lifted arc lengths from `c`.  Every curve is at
least as long as its chord, so

```text
L(T) >= |z_+(T)-c|+|z_-(T)-c|.                              (11)
```

There is no `z^4` term in (1).  The inverse expansion at infinity therefore
has no constant translation:

```text
z_+(T)=T^(1/5) omega+o(1),
z_-(T)=T^(1/5) conjugate(omega)+o(1).                       (12)
```

Using `|R eta-c|=R-Re(c conjugate(eta))+o(1)` for unit `eta`, (10)--(12)
give

```text
liminf_(T->infinity) (L(T)-2T^(1/5))
  >= -Re(c(conjugate(omega)+omega))
   = 2 cos(2 pi/5)
   = (sqrt(5)-1)/2 > 0.                                    (13)
```

The integral definition of `delta_Q(c)` is exactly the limit on the left of
(13): its subtracted integrand is the derivative of `2T^(1/5)`.  Hence
`delta_Q(-1)>0`, with the explicit lower bound (2).

## Corrected producer

This theorem refutes only the hubwise strengthening

```text
for every negative critical c, delta_Q(c)<0.
```

The live statement remains

```text
min_{negative critical c} delta_Q(c)<0,                    (HF-strict)
```

or a componentwise aggregate whose total charge forces one negative pair, or
a direct finite connector.  The distinction is load-bearing: a paired trace
may select a topologically valid negative saddle whose individual scattering
defect is nevertheless positive.

This also exactly refutes the `Leftmost-Fibre Inequality LF` proposed in the
subsequent stratified-transfer return.  Here `c=-1` is the **unique leftmost**
critical point.  The other real critical point `r` lies in `(1,8/5)` and its
value `3r(r+4)` lies in `(0,27)`.  The conjugate critical-value pair has common
real part `(9-3r(r+4))/2>-9` by the critical-value trace, and is nonreal by the
kernel above.  Under the return's substitution `t=s^5`,

```text
integral (|dz_+/ds|+|dz_-/ds|-2) ds = delta_Q(c).           (14)
```

Thus its canonical leftmost fibre has the strictly **positive** lower bound
(13), not negative defect.  The return's exact all-branch speed-product
identity may still be useful, but—as the return itself notes—a product bound
does not control the arithmetic sum of a marked pair.  Its RSCT statement is
a conditional transfer consumer: the signed resolution of every zero contact
is an explicit hypothesis and is not supplied merely by the paired trace.
Accordingly neither RSCT nor the product identity reduces the tied-face
residual to the proposed LF statement.

`TiedNewtonFaceHorizontalFibreHubwiseNoGo.lean` checks (3)--(5), (7)--(9),
the nonreal-critical-value exclusion kernel, and the exact golden-ratio
constant in (13).  The global lift continuation, sector identification,
inverse asymptotics, and equality of the defect integral with the endpoint
limit remain ordinary complex analysis.  No all-degree selector, finite
near-Fekete transfer, or proof of unrestricted Erdős #1041 is claimed.
