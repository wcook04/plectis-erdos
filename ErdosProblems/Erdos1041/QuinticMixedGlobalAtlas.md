# Erdős #1041: a finite atlas for the full normalized quintic mixed model

Status: complete computer-assisted analytic proof of the normalized quintic
mixed-model theorem, with exact outward-integer replay and a focused Lean
certificate kernel, 2026-08-25. This closes the compact model below, not the
finite near-Fekete transfer or unrestricted Erdős #1041.

## 1. Target theorem

For

```text
H_{A,B}(z)=Re(Az+Bz^2-z^5),             max(|A|,|B|)=1,   (1)
```

the target is a pair of fifth-root directions, a positive common truncation
radius, and the joining chord on which `H_{A,B}<=0`, including both outward
ray tails. This is the compact mixed-model selector left open by the
first-nonzero-mode argument.

## 2. Exact normalization and symmetry

The coefficient boundary is the union of two compact three-dimensional
faces:

```text
|B|=1, |A|<=1,                  |A|=1, |B|<=1.             (2)
```

Rotating `z` by a fifth root sends

```text
(A,B) -> (A omega^k, B omega^(2k)),                       (3)
```

and conjugation sends `(A,B)` to `(conj A,conj B)`. Hence the unit coefficient
phase may be restricted to `[0,pi/5]`; the other phase uses four overlapping
quadrant charts.

No trigonometric interval evaluation is needed. Each chart uses the rational
stereographic parameterization

```text
U(t)=((1-t^2)/(1+t^2), 2t/(1+t^2)).                       (4)
```

The four full-phase charts take `t in [-0.415,0.415]` and multiply by
`1,i,-1,-i`. The fundamental chart takes `t in [0,0.326]`. These rational
intervals strictly contain the required algebraic endpoints
`tan(pi/8)=sqrt(2)-1` and `tan(pi/10)`. Lean proves `|U(t)|=1` exactly in
`stereographic_unit`.

## 3. A finite strict connector certificate

Fix a root pair `(j,k)` and rational radius `r`. On its chord put

```text
z(t)=r((1-t)omega^j+t omega^k),             0<=t<=1.       (5)
```

Then (1) is a real polynomial of degree at most five. Elevate it to Bernstein
degree 2000. If every Bernstein control is nonpositive, the whole chord is
nonpositive because the Bernstein basis is nonnegative. For a coefficient
box centred at `(A_0,B_0)`, the control perturbation is bounded uniformly by

```text
r delta_A + r^2 delta_B,                                    (6)
```

since the elevated controls of `z/r` and `(z/r)^2` are convex combinations of
unit complex numbers. Thus one strict control vector certifies an entire
three-dimensional parameter box.

On a selected ray the upper-box polynomial is

```text
r a x+r^2 b x^2-r^5 x^5,                  x>=1.            (7)
```

Two exact sufficient tests cover every selected ray in the atlas:

```text
r a+r^2 b-r^5 < 0,       r^2 b<=0,                         (8a)
```

or

```text
r a+r^2 b-r^5 < 0,       r^2 b-4r^5<=0.                   (8b)
```

The first is higher-power domination; the second says the residual quartic is
decreasing from radius one. Lean checks both box implications in
`ray_of_upper_endpoint` and `ray_of_upper_quarticDrop`.

## 4. Closing the unique zero-margin neighbourhood

The strict Bernstein atlas cannot include the equality point itself. Its
symmetry-reduced coordinates are

```text
A_*=u_* omega^2,     B_*=exp(i pi/10),     u_*^3=27/320.   (9)
```

The four-contact theorem supplies the missing open box. Work in the symmetry
chart in which the centre is `(A_*,B_*)=(u_*,i)`. Decompose the unit-circle
displacement of `B` as

```text
B-i = tau+i nu,              nu<=0,       |nu|<=tau^2,    (10)
```

and put `delta_t=(|A-A_*|^2+tau^2)^(1/2)`. The last inequality is the exact
circle identity `(1-cos theta)<=sin(theta)^2`; hence a coefficient ball of
radius `17/2500` gives `delta_t<=17/2500` and
`|B-i|<=(1+17/2500)delta_t`.

Exact algebraic intervals give the following conservative constants for its
four connectors:

```text
tetrahedral first-order support       >= 59/1000,
quadratic chord/normal remainder     <= 8 delta_t^2,
all ray-tail coefficient tolerances  > 17/2500.           (11)
```

Here is the full origin of the middle constant. If `r` is one of the four
contact radii, `d=|omega^k-omega^j|`, and the centre chord is bounded by
`-kappa(t-t_0)^2`, the parameter-dependent cross term is at most

```text
L delta_t |t-t_0|,
L=d r(1+2r(1+17/2500)).                                  (12)
```

Exact replay gives, connector by connector,

```text
L^2/(4 kappa)+r^2 < 25/4 < 8.                            (13)
```

Completing the square accounts for `L^2/(4 kappa)`; the `r^2` term accounts
for the normal contact value `Re(i nu z_0^2)`. Thus there is no hidden
asymptotic `O`-term in this local estimate. Consequently, for
`0<delta_t<=17/2500`, the selected contact satisfies

```text
H <= -(59/1000)delta_t + 8 delta_t^2 < 0.                 (14)
```

The Lean theorem `equalityBall_margin` checks the final strict inequality.
The interval checker independently verifies the three numerical bounds above
before this neighbourhood may be consumed.

## 5. Finite cover architecture

The generator starts from 128 rational stereographic boxes. A box is accepted
only if one fixed pair and one fixed radius pass every degree-2000 Bernstein
upper control and both analytic ray tests. Otherwise it bisects the largest
scale-relevant coordinate. Boxes wholly inside the exact ball (14) are routed
to the equality-tetrahedron theorem. Failure at depth 32 is fatal.

The generator produced 3,834 strict boxes and 81 local equality boxes, using
76 distinct radii and no unresolved boxes. The outward-integer replay verified
all 3,834 strict boxes, all 81 local boxes, and all 181 selected
pair-radius groups at scale `10^24`. It also verified the phase-chart cover and
every constant in (11)--(13). Floating point chooses candidates but never
decides a sign; deleting any exact sign gate makes the checker fail closed.

## 6. Claim boundary

This proves the **entire compact degree-five mixed model** (1), including both
coefficient-boundary faces and the sharp equality orbit. It supplies the
finite low-mode-envelope selector missing from the degree-five near-Fekete
expansion.

It still does not by itself prove unrestricted Erdős #1041: the exact
origin-anchored remainder must be shown smaller than these model margins at
the selected perturbation scale, and analogous finite mode faces remain in
higher degrees. The next handoff is therefore the degree-five finite-expansion
consumer, followed by the general `n` mode-envelope induction.

## 7. Exact degree-five scale for that handoff

The consumer has a canonical normalization, so no further scale search is
needed. For Fourier coefficients `E_1,E_2` put

```text
rho=max(|E_1|^(1/4), |E_2|^(1/3)),
A=E_1/rho^4,                 B=E_2/rho^3.                 (15)
```

Then `max(|A|,|B|)=1` and, at `z=rho zeta`,

```text
rho^(-5) Re(E_1 z+E_2 z^2-z^5)
   = Re(A zeta+B zeta^2-zeta^5).                          (16)
```

The disk-tangent pairing from `FormACutQuantitativeExpansion` gives

```text
|E_4+conj(E_1)|<=2 Delta,
|E_3+conj(E_2)|<=2 Delta,           Delta=-Re E_0.        (17)
```

Fourier inversion and (17) give the useful exact estimate

```text
eta <= Delta+(2/5)(|E_1|+|E_2|).                          (18)
```

Consequently, in the transverse branch `Delta<=K rho^3`, one has
`eta=O_K(rho^3)`. At `z=rho zeta`, the paired high modes then read

```text
E_3 z^3/rho^5 = -rho conj(B) zeta^3+O_K(rho),
E_4 z^4/rho^5 = -rho^3 conj(A) zeta^4+O_K(rho^2),         (19)
```

and the anchored nonlinear remainder is `O_K(rho^2)` after division by
`rho^5`. At a strict atlas box these terms are absorbed directly. At the sole
zero-margin orbit, the paired third mode has the already-proved opposite signs
on the two axis contacts, so the four-contact lexicographic selector supplies
the first strict term.

This exposes an exact downstream bifurcation rather than concealing it in an
`O`-symbol. The atlas closes the transverse low-mode branch. The complementary
radial-dominant branch `Delta>K rho^3` must consume the inward radial cone (or
use its own scale); (18) alone does not allow `Delta` to be called a harmless
remainder. That radial-deficit lemma is the next finite-expansion proof
obligation.
