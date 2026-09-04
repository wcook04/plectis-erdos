# Component-lifetime transport identity for mean access and perimeter

Status: new exact identity, Type-A landed 2026-08-28 (batch 03, return 005,
improved).  Ordinary proof, verified in exact closed-form arithmetic on the
quadratic family by
`scripts/check_erdos1041_global_tree_admissible_product.py`.  It is a
parent-coupled transport law, **not** a parent producer; the obstruction that
stops it is stated exactly at the end.

## Setup

Let `f` be monic of degree `n` with simple critical values, and let `W` be a
nontrivial component of the lemniscate forest with degree `d = deg(f|_W) >= 1`,
born at level `beta` (a merge level, or `0`) and alive on the regular interval
`(beta, delta)`.  For regular `t in (beta, delta)` write

```text
K_t(W)   = component of {|f| <= t} corresponding to W,
p_W(t)   = H^1(dK_t(W)),
L_W(t)   = (1/(2 pi)) int_0^{2 pi} Lambda_theta(W, t) dtheta,
```

where `Lambda_theta(W, t)` is the total length, over the `d` sheets of `W`,
of the lifts of the value segment `[0, t e^{i theta}]` starting at the `d`
zero occurrences in `W` (defined for every phase `theta` whose ray avoids the
critical values of `f` in `W`, a full-measure set of phases).

## Lemma A (componentwise coarea)

```text
L_W(t) = (1/(2 pi)) int_beta^t p_W(s) ds / s,      hence
L_W'(t) = p_W(t) / (2 pi t)   for a.e. regular t.
```

Proof.  Fix `s`.  The map `arg f` restricts to a degree-`d` cover
`dK_t(W) cap {|f| = s} -> S^1`, and along it
`|d(phi)/d(ell)| = |f'(z)|/s`, i.e. `d(ell) = s d(phi)/|f'|`.  Therefore

```text
int_0^{2 pi} sum_{f(z) = s e^{i phi}} 1/|f'(z)| dphi = (1/s) p_W(s),
```

and Fubini in `(s, phi)` against `ds` gives the identity.  `[]`

## Theorem B (integrating factor at alpha = 1/pi)

With `d nu(t) = alpha t^{alpha - 1} dt` and `alpha = 1/pi`, for a.e. `t`,

```text
d/dt ( t^alpha L_W(t) ) = (alpha/2) t^{alpha-1} ( 2 L_W(t) + p_W(t) ),
```

and equivalently, over any lifetime interval `[beta, delta] sub (0, 1]`,

```text
int_beta^delta ( 2 L_W(t) + p_W(t) - 2 d ) d nu(t)
  = 2 [ t^{alpha} ( L_W(t) - d ) ]_{t=beta}^{t=delta}.            (T)
```

Proof.  Multiply Lemma A by `t^alpha`:

```text
d/dt (t^alpha L_W) = alpha t^{alpha-1} L_W + t^alpha p_W/(2 pi t)
                   = alpha t^{alpha-1} L_W + (alpha/2) t^{alpha-1} p_W,
```

because `1/(2 pi) = alpha/2` exactly when `alpha = 1/pi`.  Integrate and
subtract `2 d int d nu = 2 d (delta^alpha - beta^alpha)`.  `[]`

## Additivity at mergers (parent coupling)

At a merger of components `W_1, W_2` into `W` at level `beta`, the parent's
lifts are the union of the children's lifts and degrees add, so

```text
L_W(beta+) = L_{W_1}(beta-) + L_{W_2}(beta-),
d_W = d_{W_1} + d_{W_2},
```

hence the excess charge `t^alpha (L_W - d_W)` is exactly additive across the
whole merge forest.  Summing `(T)` over every component lifetime telescopes
the forest identity

```text
int_0^1 ( 2 L(t) + p(t) - 2 n ) d nu(t)  =  2 ( L(1) - n )  <=  0,
```

where the last step is the occupied global inverse-fibre budget `L(1) <= n`
(claim row r005_c03; the coarea-plus-Polya aggregate).  No child is ever
replaced by a standalone majorant: the identity carries each component's
actual access slack until its ancestor consumes it.

## Why this is still not a parent producer

Under the failure hypothesis for Erdős #1041, every component of degree
`d >= 2` whose cyclic adjacent-lift gaps join distinct roots satisfies
`2 L_W + p_W > 2 d` at every regular level of its lifetime (otherwise the
occupied moved-block criterion `2 Lambda + P <= 2 d` of
`PartialClusterPreimagePerimeterIdentity.md` (PP2) closes the theorem for
that component).  Degree-one components contribute negative slack that can
absorb the entire global excess: `(T)` only yields

```text
int sum_{d_W >= 2} (2 L_W + p_W - 2 d_W) d nu
  <=  int sum_{d_W = 1} (2 - 2 L_W - p_W) d nu  +  2 (L(1) - n),
```

and the right side is singleton slack.  Turning a surviving degree-one loop
at the virtual level-one cut into a distinct-root route is precisely the
unproved virtual-cut/grafting implication recorded in
`AdmissibleCriticalArcProductLab.md`; the exact no-go
`universal_radial_contour_sharp_criterion_no_go_2026_08_28` (quadratic
`z^2 - (5/6)^2`) shows no pointwise-in-level sharpening of the integrand can
be universal, and negative entry 65 shows separately-resolved contours pay
`(2/k) sum_c L(c)` asymptotically.  Because `(T)` is an identity, no
reweighting `d nu` can avoid the obstruction: the weight `alpha = 1/pi` is
forced by the coarea constant in Lemma A.

## Exact verification (quadratic family)

For `f(z) = z^2 - r^2`, `r = 0.8`, with closed-form lift integrands
`(1/2)((s + r^2 cos theta)^2 + r^4 sin^2 theta)^{-1/4}` and perimeter
integrand `(t/2)((t - r^2)^2 + 4 r^2 t sin^2((phi - pi)/2))^{-1/4}`, the
script checks `L(t) = (1/(2 pi)) int_0^t p(s) ds / s` to relative error
`4 x 10^{-21}` below the merge (`t = 0.5`) and `<= 2.1 x 10^{-5}` absolute
through the pinch and above (`t = 0.63, 0.7, 0.85, 0.97`), and checks
`p(t)/(2 pi t) = L'(t)` to `3 x 10^{-9}` at smooth levels.  The identity
itself is analytic; the numerics only guard the constants.

## Claim boundary

New: the lifetime-integrated transport law `(T)` with the exact weight
`alpha = 1/pi`, its merger additivity, and the forest telescoping.  Occupied:
the fixed-level criterion `(PP2)`, the global `L(1) <= n`, the singleton-slack
and virtual-cut obstructions.  No parent-facing consumer follows; the open
producers (`one_root_covering_of_the_first_merge_component`,
`critical_point_selection_with_inverse_ray_length_control`,
`fixed_safe_monodromy_block_average_lift_length`) are unchanged.
