# Erdős #1041: the first critical-value merge

## Outcome

The unrestricted problem has a substantially smaller topological core than the
spanning-tree route suggests.  For a generic polynomial, choose a critical
point `c` for which `|f(c)|` is minimal.  Then `|f(c)|<1`, the two descending
inverse-ray branches at `c` terminate at two distinct roots, and their interiors
lie in the strict unit lemniscate.  Thus one local two-branch metric inequality
would solve the generic case:

```text
length(branch_1(c)) + length(branch_2(c)) < 2.
```

The tempting straight-spoke completion of this reduction is false in degree
five; the exact witness below leaves only the curved branch inequality in the
display.  The reduction deliberately avoids the false
epsilon-sharp tree budget: no tree through every root is constructed and no
saddle attachment is charged more than once.

There is also a useful scale normalization.  Put

```text
R = max_j |z_j| < 1.
```

Replacing every root and every point of a path by its quotient by `R`
multiplies critical values by `R^(-n)`, so it preserves their modulus ordering,
and multiplies all Euclidean lengths by `R^(-1)`.  Consequently it is enough
to prove the non-strict closed-disk statement

```text
first_merge_branch_length_1 + first_merge_branch_length_2 <= 2
```

when `max_j |z_j|=1`.  Scaling back would give a path of length at most
`2R<2` in the original strict lemniscate.  This is the natural analytic target;
an unnormalized finite search can hide a failure merely by placing all roots
well inside the disk.

## Exact critical scale from the discriminant

The outer radius `R` is not the only natural scale.  If `c` is a
minimum-modulus critical point, put

```text
rho = |f(c)|^(1/n).
```

Then

```text
rho <= R.
```

Indeed, list the `n-1` critical points with multiplicity.  Minimum-critical
ordering and the resultant identity give

```text
|Disc(f)|
  = n^n product_(f'(d)=0) |f(d)|
  >= n^n |f(c)|^(n-1)
  = n^n rho^(n(n-1)).
```

On the other hand, the Fekete/Hadamard bound for `n` points in the radius-`R`
disk gives

```text
|Disc(f)| <= n^n R^(n(n-1)).
```

Taking the `n(n-1)`-st root proves the assertion.  Equality throughout forces
the Fekete equality case: the roots form a rotated regular `n`-gon on
`|z|=R`, the critical point is zero, and the two-arm length is exactly `2R`.

This separates two analytic conjectures:

```text
strong: L_1+L_2 <= 2 rho,
weak:   L_1+L_2 <= 2 R.
```

The strong statement implies the weak one and is exact on the regular family,
but it may be false.  The objective
`critical-scale-normalized-minimum-critical-newton-hub` is its dedicated
one-way falsifier.  A crossing above one kills only the strong statement; the
scale-normalized `2R` completion remains the actual solution route.

There is a useful rigidity subcase.  If every distance `|z_j-c|` equals `rho`,
then after translating by `c` and dividing by `rho` the roots lie on the unit
circle, zero is minimum-critical, and the same lower resultant bound meets the
unit-circle Fekete upper bound.  Hence the normalized roots are a regular
polygon.  Thus the equal-distance case of the strong statement is not a new
family: it is exactly the sharp regular model.

## Proposition: the canonical first merge supplies two contained branches

Let

```text
f(z) = product_(j=1)^n (z-z_j)
```

have distinct roots in the open unit disk.  Assume for the moment that all
critical points are simple, all critical values are nonzero, and their moduli
are distinct.  Put

```text
mu = min { |f(c)| : f'(c)=0 }.
```

Then:

1. `mu<1`;
2. every component of `{|f|<t}` with `0<t<mu` contains exactly one root and
   `f` maps it conformally onto `{|w|<t}`;
3. at the unique critical point `c` with `|f(c)|=mu`, two different one-root
   components meet; and
4. the two local inverse branches of the ray
   `f(z)=s f(c)`, `0<=s<=1`, continue from `c` to two distinct roots and, away
   from `c`, satisfy `|f(z)|=s mu<1`.

### Proof

The Vandermonde determinant of `n` points in the closed unit disk has modulus
at most `n^(n/2)`, with equality only at a rotated regular `n`-gon on the unit
circle.  Because every root is strictly inside, the inequality is strict.
The resultant identity

```text
|Disc(f)| = n^n product_(f'(c)=0) |f(c)|
```

(critical points counted with multiplicity) therefore gives

```text
product_(f'(c)=0) |f(c)| < 1.
```

Hence at least one critical value, and in particular the minimum one, has
modulus below one.

For a regular value `t`, the restriction of `f` from a component `U` of
`{|f|<t}` to the value disk is a proper holomorphic map.  Its degree is the
number of roots in `U`, counted with multiplicity.  If `t<mu`, the component
contains no critical point.  It is therefore an unbranched finite cover of a
simply connected disk, hence has degree one.  This proves the one-root and
conformal assertions.

At the first critical level, the local model at a simple critical point is a
four-pronged saddle.  A component of a polynomial sublevel set is simply
connected.  Indeed, if `H` were a bounded complementary hole, then
`|f|=t` on its boundary and the maximum-modulus principle would give
`|f|<t` throughout its interior.  At every regular boundary point a level arc
has sublevel points on only one side, whereas here both the component `U` and
the interior of `H` supply sublevel points on opposite sides.  Hence every
boundary point of `H` would be critical, impossible because a nonconstant
polynomial has only finitely many critical points.  Consequently the first index-one handle
cannot attach twice to one component and create a hole; it joins two different
one-root components.  The two descending sectors are precisely those two
components.

Finally, no point of the open value segment `s f(c)`, `0<=s<1`, is a critical
value, by the definition of `mu`.  Each local inverse branch therefore
continues without ramification along the whole open segment.  Properness rules
out escape at finite `s`, and at `s=0` the branches end at the unique roots in
the two components.  Their endpoints are distinct because the components are
distinct.  The displayed value equation gives strict lemniscate containment.

## Normalized analytic form

Translate `c` to zero and divide by its critical value:

```text
P(w) = f(c+w)/f(c).
```

The first-merge hypotheses become

```text
P(0)=1,
P'(0)=0,
|P(d)|>=1 for every other critical point d.
```

The two descending inverse branches are the two lifts of `[0,1]` that meet at
zero.  This normalization separates two possible completions:

- **straight completion (now eliminated):** two root spokes from zero stay in
  `|P|<=1`, and their unscaled Euclidean lengths sum to less than two;
- **curved completion:** the two lifts of `[0,1]` have total Euclidean length
  less than two after undoing the translation.

The logarithmic-balance theorem in `CriticalTwoRootProximity.lean` already
supplies two roots whose distances from `c` sum to at most
`2 |f(c)|^(1/n)<2`.  The unresolved selection issue is whether a pair with
that metric bound can also be given containment.  The exact balanced quintic
shows that this cannot be asserted at an arbitrary critical point; minimum
critical-value ordering is load-bearing.

## Exact degree-five failure of the straight completion

The minimum-critical qualifier does not rescue straight spokes.  Put
`r=999999/1000000` and use the rational unit-circle parametrization

```text
u(s) = ((1-s^2)/(1+s^2), 2s/(1+s^2))
```

at

```text
3705471/251106715,
440437799/579901420,
3032911868/924490473,
-2623783291/898185297,
-540347338/778985653.
```

The roots `r*u(s)` are distinct Gaussian rationals of exact modulus `r<1`.
The exact checker isolates all four zeros of `f'` in pairwise disjoint rational
Rouché disks.  Rational rectangle evaluation of `f` on those disks proves that
one critical-value squared-modulus interval lies strictly below the other
three and below one.

At that unique first critical point, dyadic spoke parameters

```text
651/2048, 69/512, 693/2048, 81/512
```

on root spokes `0,2,3,4`, respectively, have exact interval lower bounds
`|f|^2>1`.  Hence at most the remaining spoke can be contained in the strict
lemniscate.  Every two-spoke path uses at least one escaping arm.

This is an exact counterexample to

```text
the minimum-modulus critical point has two contained straight root spokes,
```

not to Erdős #1041.  For the same witness the two descending curved branches
at the first merge have numerical total length about `1.755`, below two.
Replay the exact result with

```sh
python3 research_corpus/Erdos1041/scripts/check_minimum_critical_straight_hub.py
python3 research_corpus/Erdos1041/scripts/check_minimum_critical_straight_hub.py --check
```

Canonical receipt:
`source-provenance://private-authoring-project/receipts/erdos1041_minimum_critical_straight_hub_counterexample_receipt.json`.

## Sharp boundary and theorem-driven falsifiers

The family `f(z)=z^n-r^n`, `r<1`, has one multiple critical point at zero.  Its
two-arm length is `2r<2`, while both the critical-value modulus `r^n` and the
normalized length `r` approach one as `r` tends to one.  Therefore neither
completion can have polynomial-independent positive slack.

`scripts/search_counterexample.py` contains two one-way objectives tied to the
reduction above:

- `minimum-critical-straight-hub` found the candidate now certified above;
  `strict-minimum-critical-straight-hub` additionally charges the gap to the
  next critical-value modulus so exactification cannot depend on a numerical
  tie;
- `minimum-critical-newton-hub` maximizes half the two descending inverse-ray
  lengths at that level; a certified score above one kills the canonical curved
  completion.
- `scale-normalized-minimum-critical-newton-hub` divides that length by the
  maximum root modulus before comparing with two.  This is the direct falsifier
  for the closed-disk theorem whose scaling-back consequence would solve the
  generic case.
- `critical-scale-normalized-minimum-critical-newton-hub` instead divides by
  `2|f(c)|^(1/n)`.  It tests the stronger discriminant-compatible completion
  above without conflating its failure with failure of the required `2R` bound.

A canonical degree-five, common-radius, near-regular run of 300 trials reached
critical-scale score `0.9495242630078684` without crossing one.  This is finite
route-selection evidence only.  Its durable receipt is
`source-provenance://private-authoring-project/receipts/erdos1041_critical_scale_minimum_newton_hub_probe.json`.

The neighboring reciprocal-sweeping and alternating-maze result of Pendyala is
assimilated in `ReciprocalSweepBoundaryLab.md`.  Its Crofton skeleton is a live
positive tool, while its maze construction forbids treating arbitrary
univalent-lobe length as uniformly bounded.

## Reconciliation with the legacy quartic descent report

`CriticalBudgetLab.md` records a quartic for which an older constant-argument
descent assigned the minimum critical point to two near-antipodal roots and
reported endpoint-distance budget about `2.0068`.  Read literally, that would
already refute both curved inequalities above, because every curve has length
at least the distance between its endpoints.

Recovering the four exact eight-decimal Gaussian-rational roots from the
original run resolves the conflict.  Rational Rouché disks and interval
evaluation still certify the same unique minimum critical-value box, but direct
inverse-value continuation

```text
f(z(u)) = (1-u^2) f(c)
```

lands at root indices `0` and `1`, not the formerly reported indices `1` and
`3`.  Three residual-gated step refinements agree.  Their total curved length
is about `1.4770648`, or normalized half-length `0.7385324`; the actual endpoint
distance budget is about `1.4348389`.  Thus the `2.0068` row was a branch
mistrack of the kind later diagnosed elsewhere in `CriticalBudgetLab.md`, not a
counterexample to minimum-critical selection.

The exact selector and numerical branch regression replay with

```sh
python3 research_corpus/Erdos1041/scripts/check_legacy_minimum_critical_descent_regression.py
python3 research_corpus/Erdos1041/scripts/check_legacy_minimum_critical_descent_regression.py --check
```

and bind to
`source-provenance://private-authoring-project/receipts/erdos1041_legacy_minimum_critical_descent_regression_receipt.json`.
The endpoint replay is finite numerical regression, not proof authority for the
open length inequality.

Subthreshold searches have no proof authority.  They decide which inequality
deserves proof effort and stop when the declared falsifier is not found.

## Genericity boundary

The proposition was stated with simple critical points and distinct
critical-value moduli so that “the first merge” is literal.  Multiple or
simultaneous first critical points can be handled either by a local multi-prong
version or by the already landed small coefficient perturbation.  A final
solution must preserve a data-dependent strict length margin during root
transfer; the regular-polygon family rules out a fixed perturbation budget.

## Claim ceiling

This note proves the ordinary-mathematics first-merge reduction and records an
exact counterexample to its straight completion.  It does not prove the curved
metric completion and does not solve Erdős #1041.  The remaining local producer
is the scale-normalized two-branch Newton length bound.
