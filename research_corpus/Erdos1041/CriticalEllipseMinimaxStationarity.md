# Critical-ellipse minimax stationarity

## Status and purpose

This note gives an exact finite-contact reduction for the moving-hub part of
CE--GM.  It does not prove CE--GM or Erdős #1041.  Its point is to replace an
unstructured minimization over hubs and whole segments by at most three active
contact points satisfying explicit algebraic equations.  The corrected form
below distinguishes contacts on the same arm from contacts on distinct arms
and treats the common hub endpoint separately.

Let `a,b` be a fixed pair of roots, let `E` be their closed ellipse, and put

```
z_i(h,t) = (1-t)h+t a_i,
M(h) = max_{i in {a,b}, 0<=t<=1} |f(z_i(h,t))|,
F(h) = log M(h).
```

The modulus envelope `M` is continuous and positive, so minimizing `F` is
equivalent to minimizing `M`.  This avoids treating `log 0` as an ordinary
endpoint value.  When differentiating `F`, every active contact has nonzero
polynomial value.

## The finite-contact theorem

By the maximum theorem, `M` is continuous; because the ellipse and parameter
intervals are compact, `F` attains a minimum.  Let `h_*` be a minimizer and
let `A(h_*)` be its active contact set.
At a contact `(i,t)` define the real two-vector

```
g_(i,t) = grad_h Phi_i(h_*,t)
        = (1-t) (Re(f'/f)(z), -Im(f'/f)(z)).                (1)
```

Standard directional differentiation of a maximum (Danskin's theorem) and
the convex Fermat rule give

```
0 in conv {g_(i,t) : (i,t) in A(h_*)} + N_E(h_*),          (2)
```

where `N_E` is the outward normal cone of the ellipse.  In particular, if
`h_*` is in the interior of the ellipse, zero lies in the convex hull of the
active gradients.  Carathéodory's theorem in the real plane then reduces (2)
to at most **three** active contacts.

Every active contact with `0<t<1` is also stationary along its segment:

```
Re((a_i-h_*) f'(z)/f(z)) = 0.                              (3)
```

Thus an interior minimizer has a Caratheodory certificate of one of the
following finite types:

1. a critical contact, `f'(z)=0`;
2. two active contacts on one arm with opposed normal gradients;
3. two contacts on distinct arms, which force the arms to be collinear;
4. a contact at the common hub endpoint `t=0`, possibly balanced against one
   or two interior contacts.

On the ellipse boundary one adds one normal vector.  Degenerate multiple
maxima are handled by retaining all active contacts before applying
Carathéodory; no uniqueness hypothesis is needed for the convex-hull form.

### Two cross-arm noncritical contacts collapse to a chord

Suppose the two contacts lie on the two **distinct** selected arms.  If neither
active gradient vanishes, convex balance makes the gradients oppositely
directed.  Equation (3) says that each of the two hub-to-root directions is
perpendicular to this common nonzero normal.  In the real plane they are
therefore parallel.  Hence

```
a-h_*  is parallel to  b-h_*.
```

So `a,h_*,b` are collinear.  The union of the two arms then contains the whole
root chord `[a,b]`; a cross-arm two-contact stationary hub cannot beat that
chord's level.  This collapse is Lean-checked by
`twoContact_tangent_balance_forces_parallel`.

The distinct-arm hypothesis is load-bearing.  Two contacts on the same arm
have the same hub-to-root direction, so the parallelism conclusion is
tautological and says nothing about the other root.  Such a pair can balance
if its two scalar normal derivatives have opposite signs.

### Why three interior noncritical contacts reduce to a same-arm pair

Assume the two arms are nonparallel and exclude the hub endpoint.  Tangency
puts every noncritical gradient from the first arm on its one-dimensional
normal line `N_a`, and every gradient from the second on the distinct line
`N_b`.  In any positive convex balance, the total `N_a` coefficient and the
total `N_b` coefficient must vanish separately.  Hence either an individual
gradient is zero (a critical contact), or one represented arm already has two
oppositely signed gradients whose convex hull contains zero.  In particular,
a `2+1` three-contact balance forces the singleton contact to be critical.

Thus a genuinely three-direction interior certificate requires a contact at
the common hub endpoint `t=0`, where the two-sided tangent equation (3) is not
available.  On the ellipse boundary the normal cone supplies the analogous
extra direction.  Lean checks the independent-normal algebra in
`coefficients_zero_of_independent_balance` and
`twoPlusOne_independentNormals_forces_singletonScale_zero`.

### Hub endpoint as an inverse-square descent-disc contact

At a non-root hub `h`, let

```
P = f'(h)/f(h),
S = sum_j |h-a_j|^(-2),
B = h-conj(P)/S.
```

In real coordinates the logarithmic gradient is exactly

```
g_h = (Re P,-Im P) = S(h-B).                                (4)
```

The barycentric descent theorem gives
`closedDisc(B,|h-B|) subset {|f|<=|f(h)|}`.  If `u` is a unit
direction from `h` and `s>0`, the ray point `h+s u` is in this disc exactly
when

```
s <= 2 (B-h) dot u.                                         (5)
```

The boundary point `s=0` is always in the disc; a nontrivial initial interval
exists exactly when `(B-h) dot u>0`.

Consequently the one-sided endpoint KKT condition
`D_u log|f|(h)<=0` is precisely the condition that the selected arm initially
enters a certified sublevel disc.  The identities (4)--(5) are Lean-checked by
`inverseSquare_logGradient_dot`, `descentDisc_ray_squaredDifference`,
`ray_mem_descentDisc_of_le_projection`, and
`ray_mem_descentDisc_iff_le_projection`.

This closes the *local* hub-endpoint containment question, but not the arm.
On the degree-six, degree-nine, and exact degree-seven hard rows, the single
descent disc covers only about `1.6e-5` to `2.2e-4` of either arm.  A proof
must therefore accumulate correlated descent discs or combine this initial
entry with the equal-level interior contacts; one disc cannot bridge the hard
configuration.

Equations (1)--(3), the equal-active-level equations, the segment equations,
and the ellipse inequality form a finite semialgebraic system after replacing
complex quantities by real and imaginary parts and clearing denominators.
Therefore a counterexample to CE--GM would have a certificate with at most
three segment contacts (plus one boundary normal when needed).  Its surviving
interior branches are: a critical contact; a same-arm opposing pair; or a hub
endpoint balanced against interior contacts.

The formerly proposed pointwise converse was false: an exact quartic has an
interior one-contact critical KKT saddle strictly above `Gcrit`, even though a
different feasible hub lies below `Gcrit`.  See
`CriticalEllipseStationaryNoGo.md`.  Compactness reduces CE--GM only to the
**minimum** over the finite KKT locus, not to an upper bound on every
stationary branch.  At a simple critical hub with strict arm maxima, a genuine
local minimizer must also pass the second-order filter

```
Re(conjugate(f(h)) f''(h) (a-h)(b-h)) >= 0.
```

## What the hard rows show

The companion probe minimizes the two-arm objective numerically and rescans
each reported segment maximum through all real critical points of the exact
float polynomial `|f(h+t(a-h))|^2`.  It then puts every near-active gradient
into a small convex-hull program.

On the stored degree-six, degree-nine, and exact degree-seven hard rows, the
winning hubs are strictly inside the ellipse (ellipse ratios about `0.895`,
`0.769`, and `0.740`).  Their active-gradient convex-hull residuals are
`6.6e-9`, `9.8e-9`, and `1.1e-8` after normalization.  The degree-nine row is
especially diagnostic: two arbitrarily selected arm gradients have cosine
only about `-0.605` and do not balance, but the full five-point near-active set
does.  The corrected probe detects the shared hub geometrically rather than
counting its `t=0` occurrence once per arm.  The hub endpoint is active on all
three hard rows; the degree-six row additionally has an opposing same-arm pair
within the near-active tolerance.  This explains why one-per-arm selection is
the wrong extraction and isolates the hub-endpoint KKT system as the branch
actually pressed by the hard data.

Several easier rows land instead on a critical contact: the largest active
gradient norms are between `1e-10` and `1e-6`.  This is the other branch of the
finite classification, not optimizer noise to be discarded.

The computation is not a proof of stationarity or CE--GM.  Its decisive use is
structural: it falsifies the idea that one should balance only the largest
contact from each arm, and it identifies the exact finite algebraic systems a
proof or certified counterexample search must eliminate next.

## Next analytic target

At a same-arm two-contact stationary point, (1)--(3) force the two scalar
normal derivatives of `f'/f` to have opposite signs after the positive factors
`1-t`.  At a hub-endpoint balance, the endpoint logarithmic gradient joins one
or two tangent-normal gradients.  Since

```
f'(z)/f(z) = sum_j 1/(z-a_j),
```

the remaining target is an **existential** product-critical-value inequality:
among the KKT branches surviving first- and second-order necessary conditions,
at least one must have level at most `Gcrit`.  This is genuinely narrower than
CE--GM, but the exact stationary no-go shows that a single above-threshold
branch is not a stop condition.  The lane stops negatively only with an exact
polynomial for which the global minimum of the two-arm objective exceeds
`Gcrit`; otherwise its output must be a certified low branch.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_critical_ellipse_minimax_stationarity.py
```
