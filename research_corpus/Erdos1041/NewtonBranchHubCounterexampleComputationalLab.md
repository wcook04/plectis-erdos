# Erdős 1041: the metric-selected Newton hub can exceed length two

## Claim boundary

This note eliminates one specific repair of the critical-pair metric theorem:

> take the critical point supplied by the metric argument and replace its two
> unsafe straight spokes by the two canonical descending inverse-ray branches.

For the exact balanced quintic already used to obstruct the nearest straight
spoke, those two curved branches have combined length greater than
`520999/250000 = 2.083996`.

This does not refute Erdős #1041. The same polynomial has other critical
points, and numerical reconnaissance finds a different critical hub with total
branch length about `0.53248`. The result is a selection obstruction: the
critical point that supplies the sharp metric scale need not supply the short
contained Newton hub.

## The exact configuration

Set

\[
 p=\frac{999}{1000},\qquad a=\frac{901}{902}p
\]

and let `f` be the monic polynomial with roots

\[
 a,\quad ip,\quad -ip,\quad
 p\frac{-451+780i}{901},\quad
 p\frac{-451-780i}{901}.
\]

Its exact expansion is

\[
 f(z)=z^5+\frac{1801197}{812702000}z^4
 +\frac{998001}{1000000}z^3
 -\frac{403785217592001}{406351000000000}z^2
 -\frac{896504000994504099}{902000000000000000}.
\]

Thus `f'(0)=0`, `f''(0)≠0`, and

\[
 v=f(0)=-\frac{896504000994504099}{902000000000000000},
 \qquad |v|<1.
\]

The point `0` is the critical point used by the existing critical-pair metric
construction.

## The canonical descending branches

Parameterize an inverse-ray branch by

\[
 f(z(s))=s v,\qquad 0\le s\le1.
\]

Away from critical points this is the same curve as Newton flow, with the
orientation reversed. Every point of the branch lies in the strict unit
lemniscate because `|f(z(s))|=s|v|<1`.

The exact critical-level resultant factors as `(s-1)` times a cubic having no
real root in `(0,1)`. Hence the ray contains no further critical value: the two
local branches issuing from the simple critical point at `s=1` continue to
roots at `s=0`.

To identify the branches at `s=1/2`, use the rectangle

\[
 -\frac45\le \Re z\le\frac15,
 \qquad
 -\frac45\le \Im z\le\frac45.
\]

Exact complex root counting gives two roots of `f(z)-v` in the rectangle,
namely the double root at zero, and two roots of `f(z)-v/2`. On each rectangle
edge, the checker isolates every point where `f(z)` is real and proves that
`f(z)/v` is either below `1/2` or above `1`. No level `sv`,
`1/2≤s≤1`, crosses the boundary. The two half-level roots in the rectangle are
therefore precisely the continuations of the two branches from zero.

## A one-way waypoint lower bound

Let

\[
 q=-\frac{1398549}{10^7}+i\frac{6823938}{10^7},
 \qquad \rho=10^{-6}.
\]

Taylor-expand `f(z)-v/2` at `q`. On `|h|=ρ`, the checker proves exactly that
the lower bound for the linear term exceeds the sum of the upper bounds for
the constant and all higher terms. Rouché's theorem therefore puts exactly one
half-level root in `D(q,ρ)` and, by conjugation, one in `D(conj(q),ρ)`.

The remaining estimate is deliberately elementary. Exact squared-distance
comparisons give

\[
 |q|>\frac{696}{1000}
 \quad\text{and}\quad
 |q-z_j|>\frac{346}{1000}
 \quad\text{for every root }z_j.
\]

Any branch from zero through `D(q,ρ)` to any root consequently has length

\[
 L>\frac{696}{1000}+\frac{346}{1000}-2\rho
   =\frac{520999}{500000}.
\]

The conjugate branch obeys the same bound, so

\[
 L_++L_->\frac{520999}{250000}=2.083996>2.
\]

This is an arc-length lower bound obtained from one certified intermediate
level, not a numerical integration estimate.

## Structural consequence

The prior state left curved descending branches as the most direct repair for
the failed straight spokes. This example closes that repair at the same
critical point. Three ingredients cannot simply be concatenated:

1. a critical value inside the unit lemniscate;
2. the sharp two-root metric bound through that critical point;
3. canonical Newton-ray containment.

The containment is automatic, but its curvature can consume more than the
entire metric slack. A surviving critical-hub proof needs a new selection
principle over critical points that controls inverse-ray arc length, rather
than accepting whichever critical point the discriminant/metric argument
supplies. Global Reeb or component geometry also remains live.

## Durable replay

The exploratory ODE and random search live in
`ErdosProblems/Erdos1041/scripts/search_counterexample.py`; they selected the
half-level waypoint and the correct falsifier. They are candidate-finding
tools only.

The exact checker contains the authority-bearing resultant, root-count,
boundary-isolation, Rouché, and rational distance certificates:

```bash
./repo-python source-provenance://private-authoring-project/scripts/check_erdos1041_newton_branch_hub.py
./repo-python source-provenance://private-authoring-project/scripts/check_erdos1041_newton_branch_hub.py --check
```

Its canonical output is
`source-provenance://private-authoring-project/receipts/erdos1041_newton_branch_hub_counterexample_receipt.json`.

The exact quintic's critical balance and earlier straight-spoke obstruction are
Lean-checked in `ErdosProblems.Erdos1041.CriticalTwoRootProximity`. The new
inverse-ray branch-length certificate is exact ordinary mathematics but is not
yet a Lean theorem.
