# Erdős #1041: an admissible critical-forest curvature charge

## Sharp sufficient theorem

Translate the circumcentre of the roots to zero and let their circumradius be
`R`.  Call a critical point admissible when `|f(c)|<1`; only those hubs give
descending inverse-ray pairs contained in the target lemniscate.  For a
generic polynomial, the two descending branches at an admissible simple
critical point combine into a root-to-root arc.  The admissible arcs form the
level-one subforest of the full critical tree.  Write `L(c)` for the length of
the arc through `c`, let `A={c:f'(c)=0, |f(c)|<1}`, count critical points with
multiplicity, and set `m=|A|`.

The following aggregate is stronger than the remaining #1041 obligation:

\[
  \sum_{c\in A} L(c)\leq 2Rm.                     \tag{A}
\]

Indeed, averaging (A) gives `min_{c in A} L(c) <= 2R`.  At least one admissible
critical point exists in the target setting, roots in the open unit disk give
`R<1`, and convex-hull invariance plus Newton descent then supplies a strictly
contained root-to-root path of length below two.  The symmetric degeneration
`z^n-r^n` spends the whole aggregate budget: its central critical point is
admissible, and after resolving its multiplicity into `n-1` edges, every edge
tends to two radial arms of total length `2r`.

The deterministic checker measures (A) when every simple critical hub was
successfully continued and stores the maximum normalized ratio

\[
  \frac{\sum_{c\in A} L(c)}{2Rm}.
\]

Finite survival is a falsifier result, not a proof.

## Exact tangent-support identity

There is a useful representation of the missing charge which does not repeat
the eliminated angular-coarea sampling.  Let `gamma:[a,b] -> C` be one
piecewise `C^2` tree edge, parametrized by arclength, with unit tangent `T`,
left unit normal `N=iT`, and signed curvature `kappa`, so `T'=kappa N`.
For the real Euclidean inner product,

\[
  \frac{d}{ds}\langle\gamma,T\rangle
  =1+\kappa\langle\gamma,N\rangle.
\]

Consequently its length is **exactly**

\[
  L(\gamma)
  =\langle\gamma(b),T(b)\rangle
   -\langle\gamma(a),T(a)\rangle
   -\int_a^b \kappa(s)\langle\gamma(s),N(s)\rangle\,ds.       \tag{B}
\]

Convex-hull invariance gives `|gamma(s)|<=R`, but replacing the last integral
by total absolute curvature loses the sharp constant.  The point of (B) is
that the **signed** curvature-support moments can cancel when summed over the
admissible critical forest.  The radial equality family has zero edge curvature;
all of its cost is in the endpoint tangent terms.  Thus curvature, rather than
raw inverse-ray length, is the correct residual currency.

## Polynomial specialization

On a regular half-edge whose value has fixed argument `theta`, use value
radius `rho` as parameter:

\[
  f(z(\rho))=\rho e^{i\theta},\qquad
  z'(\rho)=\frac{e^{i\theta}}{f'(z(\rho))}.
\]

Hence

\[
  \arg T=\theta-\arg f'(z),
  \qquad
  d\arg T=-\operatorname{Im}\!\left(\frac{f''(z)}{f'(z)}\,dz\right). \tag{C}
\]

Equations (B) and (C) turn (A) into a concrete analytic theorem about the
sum, over the admissible critical forest, of endpoint tangent terms and signed
`f''/f'` support integrals.  They also expose the required cancellation:
bounding each edge separately is impossible, while summing `f''/f'` is
compatible with its divisor of `n-1` critical points.

## Exact remaining charge

Orient one admissible edge from root `a` through its critical point to root
`b`.  Let `U_a,U_b` be the unit tangents pointing from the respective roots
toward the critical point.  The endpoint term in (B) is then

\[
 E_e=-\langle a,U_a\rangle-\langle b,U_b\rangle.
\]

Put `K_e=integral_e kappa <z,N> ds`.  Formula (B) gives the sharper exact
budget identity

\[
 2R-L(e)=
 \underbrace{(R+\langle a,U_a\rangle)
            +(R+\langle b,U_b\rangle)}_{D_e\geq0}
 +K_e.                                             \tag{D}
\]

The endpoint deficit `D_e` is nonnegative solely because the roots lie in the
centred radius-`R` disk.  Thus (A) is **equivalent** to the signed charge lemma

\[
             \sum_{e\subset A}(D_e+K_e)\geq0.       \tag{E}
\]

This separates the available geometric slack from the dangerous negative
curvature.  It is materially stronger than merely rewriting the length:
computation directly falsifies the tempting shortcut `sum_e K_e>=0`, while
near the radial equality family both `D_e` and `K_e` tend to zero.  Splitting
each edge at its critical point and demanding a nonnegative charge at every
root star is false as well.  The cancellation required by (E) is therefore
global across both terms, not curvature-only and not root-local.

## Topology-aligned surviving lemma

The admissible forest decomposes according to the connected components of
`{|f|<1}`.  This suggests the stronger componentwise statement

\[
  \sum_{e\subset C}(D_e+K_e)\geq0                 \tag{F}
\]

for every nontrivial admissible component `C`, always using the circumradius
`R` of the **full** root set in `D_e`.  Summing (F) gives (E).  Unlike a root
star, a component is closed under every admissible merger below level one, so
its boundary is a regular polynomial lemniscate and argument-principle
cancellation can be applied without cutting through a selected edge.

Deterministic component grouping has not falsified (F), including a targeted
degree-six two-cluster configuration whose central merger is inadmissible and
whose admissible forest has two nontrivial components.  A stronger-looking
localization is false: replacing global `R` by the circumradius of the roots
inside `C` produces a negative normalized charge on that same IEEE-pinned
configuration.  The roots outside `C` still occur in `f'/f` and change the
Newton trajectories, so they cannot be discarded from the metric budget.

Thus (F), with global `R`, is the smallest topology-aligned theorem still
standing.  A proof can uniformize one lemniscate component at a time, but its
metric estimate must retain the external-root factors in `f'/f`.

## Component uniformization

Let `Omega` be the level-one component corresponding to `C`, and suppose it
contains `k>=2` roots, counted with multiplicity.  Polynomial sublevel
components are simply connected, and

\[
                  f:\Omega\longrightarrow\mathbb D
\]

is a proper holomorphic map of degree `k`.  After a Riemann map
`phi:D -> Omega`, the composite `B=f o phi` is a finite Blaschke product of
degree `k`.  Riemann--Hurwitz gives exactly `k-1` critical points in `Omega`,
counted with multiplicity.  Pulling the admissible inverse-ray tree back by
`phi` gives the critical radial tree `Gamma_B` of `B`; every tree edge is
counted once and

\[
       \sum_{e\subset C}L(e)=\int_{\Gamma_B}|\phi'(w)|\,|dw|.  \tag{G}
\]

Consequently (F) is equivalent to the trace estimate

\[
       \int_{\Gamma_B}|\phi'(w)|\,|dw|
       \le 2R(k-1),                                  \tag{H}
\]

with the additional polynomial coupling `B=f o phi`.  A bound for arbitrary
bounded univalent `phi` would be too broad: the usable radius control is known
on the pulled-back critical tree through convex-hull confinement, not on all
of `Omega`.  Formula (H) is nevertheless the clean boundary for an
extremal-length or argument-principle proof: construct a multiplicity-weighted
measure on `Gamma_B` whose `|phi'|` trace is controlled by the global support
deficit in (D).  Coalescing critical rays are allowed and must be charged by
their Riemann--Hurwitz multiplicity rather than sampled as distinct angles.

The next proof step must exploit the cyclic order of the selected critical
rays together with the argument-principle structure in (C) to control this
combined charge.

**The endpoint half of that object is now explicit.**
[AttachmentAwareReeb.md](AttachmentAwareReeb.md) Theorem 4 shows the incident
tangent at a simple root `a` is exactly `exp(i(theta_c - arg f'(a)))`, so
`sum_i <a, U_a^{(i)}> = Re(a exp(i arg f'(a)) S_a)` with
`S_a = sum_i exp(-i theta_{c_i})`, and (F) reads

\[
  2Rm+\sum_{a\in V(C)}\operatorname{Re}\!\big(a\,e^{i\arg f'(a)}S_a\big)
      +\sum_{e\subset C}K_e\;\ge\;0.
\]

That note also proves the Reeb/strip lane cannot beat `min_c L(c)`, so this
charge is the whole remaining obligation for the inverse-ray route, not one
option among several.  A per-edge absolute-curvature estimate is a stop condition
because it discards the needed cancellation.  Passing to circumradius one
without also transforming the level threshold is another stop condition:
admissibility is not purely affine geometric data.

## Claim boundary

The tangent-support formula, its Newton specialization, and the budget identity
(D) are ordinary exact calculus.  Convex-hull confinement is separately
proved, with its supporting half-plane algebra checked in Lean.  Inequality
(A), equivalently (E), remains open and would solve Erdős #1041.  The two sign
failures just described are deterministic numerical falsifiers, not exact
counterexamples, and no surviving numerical ratio is promoted to proof.
