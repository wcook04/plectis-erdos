# Critical-ellipse geometric-mean free-hub lab

## Retired programme target

Let `c_*` be a critical point of least critical-value modulus
`mu=|f(c_*)|`, let `rho=mu^(1/n)`, and let `a,b` be the two roots nearest to
`c_*`.  The already-landed theorem
`exists_two_roots_dist_sum_le_two_mul_geomMean` in
`CriticalTwoRootProximity.lean` gives

```
|a-c_*|+|b-c_*| <= 2 rho.                                   (1)
```

Let

```
Gcrit = (product_{f'(c)=0} |f(c)|)^(1/(n-1)).
```

The target tested here was:

> **CE--GM.** There is a hub `h` in the ellipse
> `|h-a|+|h-b|<=2rho` such that both straight segments `[h,a]` and `[h,b]`
> lie in `{|f|<=Gcrit}`.

CE--GM would have proved Erdős #1041.  The two segments have total length at most
`2rho`.  The discriminant/Fekete identity gives `Gcrit<=R^n`, while
`mu<=Gcrit<=R^n`, so after minimum-enclosing-disc normalization the path has
length at most `2R<2` and lies in `|f|<=R^n<1`.

This is stronger than the existing free-hub conjecture `V_E<=Gcrit`: the pair
is fixed to the nearest pair at the least-critical point and the allowed
ellipse has major axis `2rho`, not `2`.

**Exact disposition (2026-08-25).** CE--GM is false in minimal degree four.
The selected nearest roots in `CEGMQuarticFixedPairNoGo.md` lie in different
components even at level `Gcrit`, so no hub or path of any shape can rescue
that fixed pair.  Everything below is retained as mechanism history; it is not
evidence that CE--GM remains open.  The surviving producer is the genuinely
free-pair inequality `V_E<=Gcrit`, with the pair and hub selected jointly.

## Earlier falsifiers and now-retired surviving form

The still stronger assertion `h=c_*` is false.  On the stored degree-six and
degree-nine hard configurations, the second-smallest exact spoke maximum
divided by `Gcrit` is respectively about `1.0000109` and `1.0000170`.  Thus the
geometric-mean critical-value buffer does not by itself make two spokes from
the critical point safe.

Allowing `h` to move in the ellipse repairs both rows: the deterministic search
finds exact-rescored maxima about `0.9999526` and `0.9999488`, below their
respective `Gcrit` values `0.9999984` and `0.9999934`.  CE--GM also survives the
exact degree-seven refutation of `V_E=mu`, all other stored free-hub hard rows,
and boundary-biased random tests.  This is evidence, not proof: the inner hub
minimization is numerical even though every reported segment maximum at the
winning hub is evaluated by the exact degree-`2n` critical polynomial.

## Analytic route exposed by the barycentric envelope

For fixed `z`, the exact disc envelope says membership in the lemniscate is the
existence of a probability vector `p` with

```
n T^(2/n) G(p) - sum_j p_j |z-a_j|^2 >= 0.                 (2)
```

For fixed `z`, the left side is concave in `p`, so its feasible set is convex.
This statement must not be promoted to joint convexity in `(p,z)`: the point
may move along an arm, and the bilinear coupling then matters.  CE--GM can
still be attacked as a correlated family of fixed-point convex feasibility
problems, with the hub displacement as the outer variable.  The first
necessary analytic task is a sensitivity bound at `c_*`: show that the
positive level buffer `Gcrit-mu` controls the displacement needed to make the
two nearest visibility kernels overlap inside the ellipse slack from (1).

Near equality, the discriminant/Hadamard defect already forces the root set
toward a regular polygon, while equality in (1) is rigid.  Away from equality,
the connected-cluster Bergman certificate supplies a structurally different
consumer.  The intended dichotomy is therefore:

```
cluster/capacity defect -> connected-cluster Bergman certificate,
small defect            -> CE--GM sensitivity around the regular polygon.
```

Neither arrow is asserted as proved here.

## Exact linear-simplex arm certificate

There is one non-tautological finite-dimensional sufficient condition.  For a
positive probability vector `p`, put

```
h = sum_j p_j a_j,
V = sum_j p_j |a_j-h|^2,
G = (prod_j p_j)^(1/n).
```

Interpolate from `p` to the root vertex `e_i`:

```
p_i(s) = (1-s)p+s e_i,       0<=s<1.
```

Its barycentre is exactly `h_i(s)=(1-s)h+s a_i`, so these centres trace the
literal straight arm.  The mixture-variance and geometric-mean identities are

```
V(p_i(s)) = (1-s)(V+s|a_i-h|^2),
G(p_i(s))/(1-s) = G (1+s/((1-s)p_i))^(1/n).
```

Consequently the whole arm is certified inside `K_T` if, for every `s<1`,

```
V+s|a_i-h|^2
  <= n T^(2/n) G (1+s/((1-s)p_i))^(1/n).                   (3)
```

Thus CE--GM has a concrete sufficient producer: find one `p` for which (3)
holds for the two selected vertices and whose barycentre lies in the sharp
ellipse.  This is stronger than actual segment containment, because it insists
that one linear weight path certify every point of an arm.

A five-restart Powell search finds this certificate on the cubic rows and the
two degree-five rows.  It does **not** find one on the degree-six, degree-nine,
or exact degree-seven hard rows: the best arm ratios are respectively about
`1.00946`, `1.01244`, and `1.01016`, even though direct free-hub segment search
does find CE--GM hubs.  Numerical non-discovery is not a refutation of the
certificate, but the stable percent-scale gaps are a rotation signal: linear
simplex interpolation is not currently the promising proof of CE--GM.

## Two further discriminating probes

The cubic one-parameter reduction was re-derived as an audit.  An arbitrary
root spoke from a least critical point can exceed `Gcrit` by a factor above
`2.49`; the claim becomes true only after selecting the two nearest roots.
That selected result is not new: it is the already-landed degree-three theorem
in `CubicCriticalHub.md`.  The scalar factorisation merely recovers why the
selection is essential and is not entered as a new packet result.

A 600-step simulated-annealing hill climb on angular perturbations of the
regular boundary hexagon was then rescored at higher hub fidelity.  Its best
row had optimized ratio `0.9963941`, comfortably below one.  This does not
prove CE--GM, but it failed to turn the fixed-pair strengthening into a quick
counterexample and pushed the search away from the regular equality case.
