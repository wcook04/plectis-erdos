# Erdős 1041: the angular budget is empty, and the circle-slice packing that replaces it

## Status

Ordinary complete proof of an unconditional all-degree parent regime, with an
exact rational certificate. Not Lean-checked, not independently reviewed. Erdős
#1041 remains open.

This sharpens [HyperbolicPackingArityFloor.md](HyperbolicPackingArityFloor.md)
from `mu <= 2/5` to `mu <= 13/25`. Nothing in the mechanism changes
except the arity floor: the same Lemma 1 Bergman bound, the same COVER failure,
the same boundary hop, the same comparison ODE, the same rational rounding
discipline. Two things are new. First a **negative** result, retiring the
"angular budget" that [CriticalSpectrumClusterSeparation.md](CriticalSpectrumClusterSeparation.md)
§6 proposed as the rigorous replacement for the phantom profile `Lambda`: that
budget forces nothing at all. Second, the inequality that does replace it, and
whose numerical relaxation lies within `5%` of the best configurations found
at the tested arities; this comparison is not a certified optimality bound.

## Theorem

> **Theorem A''.** Let `f` be squarefree monic of degree `n >= 2` and
> `mu = min{|f(c)| : f'(c) = 0}`. If `mu <= 13/25`, then two distinct
> roots of `f` are joined by a rectifiable curve inside `{|f| < 1}` of length
> strictly below `2`.

> **Corollary B''.** Every squarefree monic `f` has two distinct roots joined
> inside `{|f| < (25/13) mu}` by a curve of length below
> `2 ((25/13) mu)^{1/n}`.

No hypothesis is placed on root locations, component arity, or component
capacity. A repeated root gives the constant curve, so the squarefree case is
the nontrivial branch.

## 0. The setting, unchanged

Assume for contradiction that no two distinct roots of `f` are joined inside
`{|f| < 1}` by a curve of length below `2`. At a regular level `t in (mu,1)`,
let `C_t` be the ancestor component, `k >= 2` its root count and
`a = Area(C_t)/pi <= 1`. Uniformise `C_t` by the disc, sending the COVER-failure
point `h` to `0`; the roots go to `b_1, ..., b_k`. Write `lam(d) = -log tanh(d/2)`,
`d_j = d(0,b_j)`, `x = log(t/mu)`. The three failure inputs of
`ClusterSeparationLowCriticalClosure.md` are

```text
(i)   d(b_i,b_j) >= D := d_min(a) = 4 artanh(sqrt(tanh(1/a))),  cosh(D/2) = e^{2/a};
(ii)  lam(d_j) <= delta(a)/2,  i.e.  d_j >= d_low(a) := lam(delta(a)/2);
(iii) sum_j lam(d_j) >= x.
```

The *arity floor* is any `k`-dependent upper bound for `sum_j lam(d_j)` under
(i)–(ii); inverting it in `k` and feeding it to the boundary-hop comparison ODE
is what closes the failure window.

## 1. The exact angular budget, and why it forces nothing

> **Lemma 1 (the angular budget, exact).** List `b_1, ..., b_k` in increasing
> order of argument about `0` and let `Theta_1, ..., Theta_k` be the cyclic
> angular gaps, so `sum_i Theta_i = 2 pi`. Then for every `i`,
>
> ```text
> cos Theta_i  <=  (cosh d_i cosh d_{i+1} - cosh D)/(sinh d_i sinh d_{i+1}) =: C_i,
> ```
>
> hence `Theta_i >= Theta(d_i, d_{i+1}) := arccos(min(1, max(-1, C_i)))`, and
> failure forces
>
> ```text
> sum_{i=1}^{k} Theta(d_i, d_{i+1})  <=  2 pi.
> ```
>
> The clamp cases are exactly `C_i >= 1  <=>  |d_i - d_{i+1}| >= D` (the
> constraint is vacuous: one root sits radially behind the other) and
> `C_i < -1  <=>  d_i + d_{i+1} < D` (the pair is infeasible at any angle).

*Proof.* The hyperbolic law of cosines at the origin reads
`cosh d(b_i,b_j) = cosh d_i cosh d_j - sinh d_i sinh d_j cos(arg b_i - arg b_j)`.
As `cos` is even and `2 pi`-periodic, `cos(arg b_{i+1} - arg b_i) = cos Theta_i`,
so `cosh d(b_i,b_{i+1}) >= cosh D` rearranges into the display (`sinh d_i sinh d_j > 0`).
The two clamp equivalences are `cosh(d_i - d_{i+1}) >= cosh D` and
`cosh(d_i + d_{i+1}) < cosh D`. ∎

At equal radii `Theta(d,d) = psi(d)` with `sin(psi(d)/2) = sinh(D/2)/sinh d`,
which is the ring bound the lead in `CriticalSpectrumClusterSeparation.md` §6
was built on. But the budget as a whole is worthless:

> **Proposition 2 (the budget is empty).** Let `M_ang(k,a)` denote the maximum
> of `sum_j lam(d_j)` over radius profiles `d_1, ..., d_k >= d_low(a)` admitting
> a cyclic order whose budget `sum_i Theta(d_i, d_{i+1})` is at most `2 pi`.
> Then for every `k >= 2` and every `a in (0,1]`,
>
> ```text
> M_ang(k,a)  >=  floor(k/2) * delta(a)/2,
> ```
>
> so `M_ang` grows at least **linearly** in `k`, while the realisable supremum
> grows like `log k`. At best the budget is a constant-factor gain over the
> corpus profile `Lambda(k,a) = max(delta/2 + (k-1) lam(g), k tau/2)`, which is
> also linear (`0.1147 k` against `0.1362 k` at `a = 1`), and at `a = 1` it is
> already worse than the packing bound `(P)` of `HyperbolicPackingArityFloor.md`
> for every `k >= 8`. It cannot be the rigorous replacement §6 of
> `CriticalSpectrumClusterSeparation.md` asked for.

*Proof.* Put `m = floor(k/2)` radii equal to `d_low` and the remaining `k - m`
equal to `d_low + D`, and order them cyclically so that no two `d_low` radii are
adjacent (possible because `m <= k - m`). A consecutive `(d_low, d_low + D)`
pair has `cosh d cosh d' - sinh d sinh d' = cosh D`, so `C_i = 1` exactly and
`Theta = 0`. The only other adjacency that can occur is a single
`(d_low + D, d_low + D)` pair when `k` is odd, contributing
`psi(d_low + D) < pi`. So the budget is at most `pi < 2 pi` and imposes nothing,
while the objective is at least `m lam(d_low) = m delta(a)/2`. At `a = 1`,
`delta/2 = 0.2293376` and `floor(k/2) delta/2` exceeds
`Lambda_pack(k,1)` from `k = 8` (`0.9174` against `0.8757`) on. ∎

The reason is structural and worth recording so the route is not re-attempted.
A hyperbolic packing is constrained between **all** pairs; the consecutive-gap
relation sees only `k` of the `k(k-1)/2` of them, and a root parked radially
behind another costs zero angle. Any number of near roots can therefore be
separated by decoys the budget cannot charge for. The same mechanism kills the
"disjoint angular shadows" heuristic: two disjoint `D/2`-balls at very different
radii have overlapping shadows.

**The fix is to impose the angular constraint at every radius, not only at the
radii the roots happen to occupy.**

## 2. The circle-slice packing lemma

Let `C_r` be the hyperbolic circle of radius `r` about `0`.

> **Lemma 3 (circle-slice packing).** Under (i), for every `r > 0`,
>
> ```text
> sum_{j=1}^{k} w(d_j, r)  <=  pi,
> w(d,r) := arccos( min(1, max(-1, (cosh d cosh r - cosh(D/2))/(sinh d sinh r))) ).
> ```
>
> Equivalently `w = arccos(1 - om) = 2 arcsin(sqrt(om/2))` with
> `om = (cosh(D/2) - cosh(d - r))/(sinh d sinh r)`, which is the form the
> certificate evaluates (no cancellation).

*Proof.* The open balls `B_j := B_hyp(b_j, D/2)` are pairwise disjoint, since a
common point would force `d(b_i,b_j) < D`. Fix `r > 0`. By the hyperbolic law of
cosines, the point of `C_r` at angle `theta` lies in `B_j` exactly when
`cosh d_j cosh r - sinh d_j sinh r cos(theta - theta_j) < cosh(D/2)`, i.e.
exactly when `|theta - theta_j| < w(d_j, r)` modulo `2 pi`. So `B_j cap C_r` is
an open arc of angular measure `2 w(d_j, r)` — empty when `w = 0`, all of `C_r`
when `w = pi`. Disjoint arcs of a circle have total measure at most `2 pi`. ∎

> **Corollary 4 (the ring bound and the observer-containing case).** Put
> `H = D/2`. For `d > 0`,
>
> ```text
> sup_{r > 0} w(d,r) = pi                         if d < H,
>                     pi/2                       if d = H,
>                     arcsin(sinh H / sinh d)     if d > H.
> ```
>
> In the last case the supremum is attained at the positive radius `r_t`
> with `cosh r_t = cosh d / cosh H`. At `d = H` it is approached as
> `r -> 0` and is not attained. For `k >= 2` pairwise `D`-separated roots
> at a common radius `d`, the triangle inequality forces `d >= H`.
> Thus the ring bound is `k alpha(d) <= pi`, with `alpha(H)=pi/2` and
> `alpha(d)=arcsin(sinh H/sinh d)` for `d>H`.

*Proof.* If `d < H`, every circle with `0 < r < H-d` lies wholly in the
ball by the triangle inequality, so `w=pi`. If `d=H`, the defining cosine
simplifies to `coth H * tanh(r/2)>0`; it tends to zero as `r -> 0`, so
`w<pi/2` and its supremum is `pi/2`. If `d>H`, a tangent geodesic from
`0` to the ball gives a right hyperbolic triangle and hence the angular
half-width `alpha(d)=arcsin(sinh H/sinh d)`. Every circle slice lies in
this sector. At `cosh r_t=cosh d/cosh H`, direct substitution gives
`cos w(d,r_t)=sqrt(cosh^2 d-cosh^2 H)/sinh d=cos alpha(d)`, proving
attainment. Finally two points at radius `d` have distance at most `2d`,
so common-radius separated configurations have `d>=H`; take the supremum
in Lemma 3 to obtain the ring bound. ∎

Lemma 3 evades Proposition 2 because slicing at a fixed radius inherits
disjointness from the balls with no hypothesis relating the radii at all. It is
strictly stronger than the ring bound (which is the single slice `r = r_t`) and
strictly stronger than the area/rearrangement bound `(P)` at the working arity.

## 3. The dual arity floor

> **Theorem 5.** Fix radii `r_1, ..., r_p > 0` and weights
> `sigma_1, ..., sigma_p >= 0`. Put `S = sum_i sigma_i` and
>
> ```text
> U = sup_{d >= d_low(a)} [ lam(d) - sum_i sigma_i w(d, r_i) ].
> ```
>
> If `U > 0` then failure forces
>
> ```text
> k  >=  (x - pi S)/U.                                                      (CS)
> ```

*Proof.* By (iii), Lemma 3 and (ii),

```text
x <= sum_j lam(d_j)
   = sum_j [ lam(d_j) - sum_i sigma_i w(d_j, r_i) ] + sum_i sigma_i sum_j w(d_j, r_i)
   <= k U + pi S.  ∎
```

Every non-negative `sigma` gives a valid floor, so the weights may be produced
by any heuristic whatsoever: the certificate has to bound only `S` and `U`. The
checker proposes them with a floating linear program — the exact dual of the
finite-`p` relaxation of Lemma 3 — and then certifies the resulting pair in
rational arithmetic, bounding `w` from **below** through
`w = 2 arcsin(sqrt(om/2))` with an everywhere-positive `arcsin` series, and
`lam` from above. The sup over `d` is taken by worst-first interval refinement,
using two elementary monotonicity facts: `lam` is decreasing, and
`c(d,r) = 1 - om(d,r)` is unimodal in `d` with an interior *minimum* (its
derivative has the sign of `cosh d cosh(D/2) - cosh r`), so `om` attains its
minimum on any interval at an endpoint. Beyond `d = max_i r_i + D/2` every `w`
vanishes and the bracket is just `lam`.

Two monotonicity facts make a coarse `a`-grid legitimate: `D(a)` and `d_low(a)`
are both decreasing in `a`, so the feasible set of (i)–(ii) grows with `a`, and a
pair `(S,U)` certified at `a' >= a` is valid at `a`. The checker builds its table
once on a fixed grid and rounds `a` **up** into it.

Finally `k` is an integer, so `ceil()` may be applied to every real-valued floor
before the maximum is taken. That is the side finding of
`CriticalSpectrumClusterSeparation.md` §8, re-audited here and now used:
`(CS)`, the packing floor `(P)` and the corpus profile `(2')` are each built
from upper bounds on `delta, tau, lam(g), S, U`, so each is a genuine real lower
bound for the integer `k`, and rounding it up is valid.

## 4. What the replacement is worth

At `a = 1` (`delta = 0.4586751`, `tau = 0.2723415`, `D = 5.3770727`,
`d_low = 2.1700771`, `cosh(D/2) = e^2`), against the corpus profile
`Lambda(k,1)`, the packing bound `Lambda_pack(k,1)` of `(P)`, the circle-slice
relaxation `M_circ(k,1)` of Lemma 3, and the best realisable configuration found
by the `Lambda_real` optimiser of `CriticalSpectrumClusterSeparation.md` §6:

| `k` | `Lambda` corpus | `Lambda_pack` (P) | `M_circ` (Lemma 3) | realisable (measured) |
|---|---|---|---|---|
| 2 | 0.3103 | 0.5899 | 0.3102 | 0.3103 |
| 3 | 0.4085 | 0.6878 | 0.3893 | 0.3784 |
| 4 | 0.5447 | 0.7475 | 0.4450 | 0.4306 |
| 5 | 0.6809 | 0.7906 | 0.4846 | 0.4694 |
| 6 | 0.8170 | 0.8244 | 0.5155 | 0.4986 |
| 7 | 0.9532 | 0.8521 | 0.5408 | 0.5208 |
| 8 | 1.0894 | 0.8757 | 0.5622 | 0.5413 |
| 10 | 1.3617 | 0.9142 | 0.5972 | 0.5759 |
| 14 | 1.9064 | 0.9710 | 0.6487 | 0.6228 |
| 20 | 2.7234 | 1.0298 | 0.7022 | 0.6717 |
| 30 | 4.0851 | 1.0955 | 0.7624 | 0.7283 |
| 100 | 13.617 | 1.2871 | 0.9428 | — |

The `M_circ` column is within `4.7%` of the measured realisable optimum at every
arity, against `64%` for `(P)` at the old attractor arity `k = 7` and a factor
`1.83` for the corpus profile. Both outer columns are floating searches. Their proximity suggests a small
gap, but does not give a rigorous bracket or an upper bound on the remaining
slack. Only feasible configurations certified exactly would supply rigorous
lower bounds for the realisable supremum.

The `M_circ` column is the value of the linear program of Lemma 3 on a
`2600`-point `d`-grid and a `1400`-point `r`-grid; discretising `d` makes it a
lower bound for the relaxation rather than an upper bound, and the `k = 2` row
shows the size of that artifact (`0.31018` against the exactly known `0.310338`).
**Nothing in the table is used by the certificate.** What the certificate uses
is Theorem 5 with explicitly certified `(S, U)`; in quick mode at `a = 1` those
give `k U + pi S = 0.4526, 0.5716, 0.6808, 0.7945` at `k = 4, 8, 16, 32`, i.e.
`1.6%` above the LP row at `k = 8` and comfortably below `(P)`.

## 5. Assembly

### From a missing path to the area inequality

Here is the analytic chain consumed by the certificate. It also fixes the
strict-path and component conventions needed when applying the earlier notes.
Let `f` be squarefree and let `mu>0` be its least critical-value modulus.
Choose a critical point at level `mu` and two descending inverse arcs into
distinct one-root components of `{|f|<mu}`. Their union is a compact connected
set `Gamma` containing two roots, with `|f|<=mu`. Below `mu`, each
component maps conformally onto the value disc because it contains no
critical point. Distinct local inverse arcs at the first critical point enter
distinct such components: two inverse images of a nearby regular value in
one component would contradict its degree one. At a regular level
`mu<t<1`, let `C_t` be its ancestor, let `k` be its number of roots, and put
`x=log(t/mu)`, `a=Area(C_t)/pi`. Pólya's area inequality gives
`a<=t^(2/n)<1`. The regular component is a Jordan domain, and a Riemann map
turns `f/t` into a degree-`k` finite Blaschke product.

For a Riemann map `phi`, its derivative has Bergman squared norm
`Area(C_t)`. The radial restriction of the Bergman kernel gives

```text
length(phi([0,r]))^2 <= a log(1/(1-r^2)).
```

Moving two preimages to `-s,s` instead gives

```text
length(phi([-s,s]))^2 <= 4a artanh(s^2),
```

because the corresponding kernel integrals are `-log(1-r^2)` and
`4 artanh(s^2)`. A path shorter than `2` therefore exists if any root pair
has hyperbolic distance below `D=4 artanh(sqrt(tanh(1/a)))`. Failure gives
condition (i).

Failure also gives an `h in Gamma` whose intrinsic distance to every root
is at least `1`. Otherwise the relatively open sets
`{h in Gamma : dist_C_t(h,a_j)<1}` cover `Gamma`. If two such sets meet,
concatenating their paths gives length below `2`; if only one is nonempty,
it contains the other root of `Gamma` and already gives a shorter path.
Connectedness excludes a disjoint cover by several nonempty sets. Sending
this `h` to zero, the one-root estimate gives
`rho_j>=sqrt(1-exp(-1/a))`. Thus `d_j>=d_low(a)`, condition (ii), and the
Blaschke product identity gives
`sum_j lam(d_j)=log(t/|f(h)|)>=x`, condition (iii).
Notice that distance **at least** `1`, not strictly greater than `1`, is
all this argument supplies and all the non-strict failure inequalities need.

For completeness, the metric part uses all root lifts in `C_t` together.
At a direction avoiding the finitely many critical-value arguments, lift
the value radius from `0` to `t exp(i theta)` from each of the `k` roots.
Split the lifts at level `mu`, and let `A_0` be the sum of the areas of their
one-root lobes below `mu`. If `phi(z)=sum_l b_l z^l` maps a unit disc onto
such a lobe, Cauchy--Schwarz in the radial variable and Parseval give

```text
mean_theta (int_0^1 |phi'(r exp(i theta))| dr)^2
    <= sum_{l>=1} l^2 |b_l|^2/(2l-1)
    <= sum_{l>=1} l |b_l|^2 = Area(lobe)/pi.
```

Summing and applying Cauchy--Schwarz bounds the mean total low lift length
by `sqrt(k A_0/pi)`. At a regular intermediate level `u`, let `P_C(u)`
be the total level perimeter inside this fixed `C_t`, and let `A_C(u)` be
the enclosed area there. The argument principle and coarea formula give

```text
P_C(u)^2 <= 2 pi k u A_C'(u).
```

Indeed, on the level curve `|dz|=u d(arg f)/|f'|`, its total argument
variation is `2 pi k`, and Cauchy--Schwarz gives the inequality. Integrating
`P_C(u)/(2 pi u)` from `mu` to `t` bounds the mean high lift length by
`sqrt(k x (pi a-A_0)/(2 pi))`. Combining the low and high bounds gives

```text
mean total lift length <= sqrt(k a (x+2)/2) =: M.
```

Some regular direction has total lift length at most `M`. Order its `k`
boundary endpoints cyclically and form `k` root connectors, each using two
lifts and the intervening boundary arc. The entire construction is in
`closure(C_t) subset {|f|<1}`. Under failure all these lengths are at least
`2`; hence `2k<=2M+P(t)`. At the outer level the same perimeter inequality
reads `P(t)^2<=2 pi^2 k a'(x)`. Rearrangement yields

```text
a'(x) >= (1/(2 pi^2)) [2 sqrt(k)-sqrt(2a(x+2))]_+^2.
```

This proves the differential inequality on every regular interval of the
ancestor. At merger levels the ancestor gains area, which strengthens the
integrated comparison below. A contradiction before `t=1` proves a path
strictly shorter than `2` in the open unit lemniscate, without any restriction
on where the polynomial roots lie.

### Certified area steps without a monotone numerical lookup

Let `A(x)=Area(C_(mu exp x))/pi` be the area of the chosen ancestor component.
Between its finitely many merger levels it is absolutely continuous; mergers
can only add area. Thus its derivative inequality integrates across a cell
with an additional nonnegative jump contribution.

Fix `xl <= x <= xr` and a trial area `m<=1`. If `A(x)<=m` throughout the
cell, every failure configuration obeys the weaker geometric constraints at
area `m`: the separation radius and the minimum distance from the observer
both decrease as the area parameter grows. The certified arity floor evaluated
at `(xl,m)` therefore remains valid for every point of the cell. Using `xr`
and `m` in the subtracted term of the boundary-hop inequality gives

```text
A'(x) >= g_cell_lower(xl,xr,m)   almost everywhere while A(x)<=m.
```

Suppose a certified lower bound at the left endpoint is `A(xl)>=ai`, and put
`h=xr-xl`. A trial value `m` satisfying

```text
m < ai + h*g_cell_lower(xl,xr,m)
```

is a strict lower bound for `A(xr)`. Indeed, if `A(xr)<=m`, monotonicity of
the actual area implies `A(x)<=m` on the cell. Integration, including the
nonnegative merger jumps, would give `A(xr)>=ai+h*g_cell_lower(xl,xr,m)>m`,
a contradiction. This argument needs no monotonicity of the *computed*
lookup across independently optimized area cells.

The checker starts its lower endpoint at `ai` and raises it only after this
test succeeds. An arbitrary upper search endpoint affects precision, not
validity. In particular, a predictor is not a certified lower endpoint:
`ai+h*g_cell_lower(xl,xr,ai+h*g_cell_lower(xl,xr,ai))` can overshoot when the
computed lower lookup increases. The exact `--comparison-audit` regression
exhibits this failure for a lower oracle beneath a decreasing true envelope.
The revised initialization avoids it. Every returned value is rounded down.

Finally `A(x_s)>=10^(-6)` follows from `k>=2`, `A<=1`,
`x_s=3/10^5`, and the explicit positive `start_shift` bound. The step argument
propagates a lower bound for *every* trajectory above that initial value.
Only this one start is needed; a grid of larger initial areas adds no coverage.
The reported hitting time is rounded upward before the final exponential
threshold test. The test at `m=1` certifies that the area cap has been exceeded before
`mu exp(x)=1`, yielding the contradiction.

The boundary-hop forcing remains
`G(x,a) = (1/(2 pi^2))[2 sqrt(k) - sqrt(2a(x+2))]_+^2` from
`LowCriticalPotentialClosure.md`, with
`k = k(x,a) = max(ceil(2'), ceil(P), ceil(CS))`. The preceding comparison
argument supplies the rigorous numerical integration without assuming that
independently certified table rows form a monotone lookup. The certified arity
floor at `a = 1`, from the four quick-mode duals quoted in §4:

| `x` | 0.40 | 0.45 | 0.50 | 0.55 | 0.60 | 0.63 | 0.65 | 0.70 |
|---|---|---|---|---|---|---|---|---|
| corpus `(2')` | 3 | 4 | 4 | 5 | 5 | 5 | 5 | 6 |
| packing `(P)` | 2 | 2 | 2 | 2 | 2 | 3 | 3 | 4 |
| circle-slice `(CS)` | 3 | 4 | 6 | 8 | 10 | 12 | 14 | 18 |

In one and the same explicit-Euler floating replica (step `10^-3`, geometric
grid of `40` initial areas from `10^-6` to `1`), the supremum of the hitting time
falls from `X_* = 0.89703` with the packing floor `(P)` — the replica's reading
of the `0.89374` recorded in `HyperbolicPackingArityFloor.md` — to
`X_* = 0.65503` with the quick-mode certified `(CS)` pairs, and to `0.63003` if
the relaxation's own LP value is used in place of the certified pairs. So
`exp(-0.65503) = 0.5194` is the new floating ceiling of this mechanism, against
`0.4078` for `(P)`. The exact rational certificate gives
`X_cert < 0.664374` in quick mode (`(51/100) exp(0.664374) < 1`) and
`X_cert < 0.6357629` in full mode (`(13/25) exp(0.6357629) < 1`), which is
Theorem A''. The gap between the two is the certificate's own resolution — step
`1/400` against `1/100`, `18` dual-table areas against `11`, `14` radii per dual
against `10`, seven `k` values against four — not a change of mechanism.

Fixed-degree rows were not re-run in this pass; the per-degree arm of
`FixedDegreeClusterSeparationClosure.md` is unchanged and still authoritative
where it is stronger, which is now only `n = 4` (`61/100`) and `n = 5`
(`139/250`). From `n = 6` on (`253/500`, `23/50`, `209/500`, `19/50`) the
all-degree constant `13/25` proved here is the better statement.

That note's Lemma 2 / Theorem 4 angular bound `Theta(k,a)` is the `s_ij`-summed
relaxation of the same law of cosines and is a genuine bound — it uses all pairs,
not only consecutive ones, which is exactly what Proposition 2 says the budget
must do. It is dominated by `M_circ` at every arity at `a = 1`
(`Theta(k,1) = 0.3238, 0.4054, 0.4940, 0.5860, 0.6799, 0.7749` at `k = 2..7`
against `0.3102, 0.3893, 0.4450, 0.4846, 0.5155, 0.5408`) but not contradicted;
re-running the fixed-degree lane against `(CS)` is the obvious next landing and
is not attempted here.

## 6. What is still on the table

*The numerical search suggests limited gains from this arity floor.* In the same floating replica,
replacing the certified `(CS)` pairs by the full relaxation moves `X_*` from
`0.65503` to `0.63003` (`exp(-X) : 0.5194 -> 0.5326`), and shrinking the
relaxation by the worst measured slack factor `1.045` — i.e. pretending the
relaxation were exact — moves it only to `0.60703` (`0.5450`). These computations suggest a mechanism ceiling near `0.545`; they do not
prove one. In particular, neither the discretized relaxation nor the fitted
slack factor rules out a stronger arity bound or a larger certified regime.
The apparent difference from `13/25 = 0.52` is about `0.025`.
The quantity
named at the end of
`ClusterSeparationLowCriticalClosure.md` — the exterior energy
`S = sum_l l |beta_l|^2` of the ancestor component, which would replace the cap
`a <= 1` by `a <= 1 - s_0` — is still the missing ingredient, and
`ExteriorEnergyFloorClosure.md` Theorem E says it cannot be derived from the
failure inequalities alone.

*Two smaller leaks in the present certificate.* The dual is restricted to `p`
radii (`10` in quick mode, `14` in full); at `a = 1, k = 8` that costs about
`1%` against the unrestricted family. The `a`-grid is coarse and rounded up,
which costs a comparable amount. Both are engineering, not mathematics.

*A genuinely open sub-statement, smaller than (C').* Determine
`M_circ(k,a)` exactly, i.e. solve

```text
maximise  sum_j lam(d_j)  subject to  d_j >= d_low  and  sum_j w(d_j, r) <= pi for all r > 0.
```

The optimiser's solution is a spread-out density in `d`, not the one- or
two-ring configuration the ring heuristic suggests, and it appears to grow like
`(pi/sinh(D/2)) * const * log k`. A closed form would determine the relaxation exactly and clarify the
COVER-failure geometry. How much it would improve the final threshold remains
unproved; the numerical `5%` comparison is not an error bound.

## 7. Claim boundary

The 2026-09-05 audit corrected the observer-containing case of Corollary 4,
removed unsupported optimality/ceiling claims from the floating discussion,
and replaced the implicit-step initialization by the direct end-area test
in §5. The revised full replay retains
`X_cert=635762889599/1000000000000` and `mu_threshold=13/25`, using 126
certified duals and one initial lower bound. Quick mode retains
`X_cert=664373027131/1000000000000` and `mu_threshold=51/100`.
The exact `--comparison-audit` countermodel shows why a nonmonotone lower
lookup cannot justify the old initialization in general; it does not assert
that the old run overshot on this particular table.

Theorem A'' is an ordinary argument with an exact rational certificate; it is
not Lean-checked and has not been independently reviewed. Lemma 1, Lemma 3 and
Corollary 4 are elementary hyperbolic trigonometry. The checker tests the
piecewise shadow formula in Corollary 4, including balls containing the
observer. Its `--geometry-audit` route runs these floating checks and an exact
rational boundary regression without executing the full ODE certificate.
The regression uses `a=1`, `d=9/4`, `r=1/4`: exact bounds give
`cosh(d+r)<exp(2)=cosh(D/2)`, so the whole circle lies in the ball and its
half-width is `pi`, not `pi/2`. Neither the dual certificate nor its
`U_upper` routine uses the shadow corollary; they use the clamped slice
formula in Lemma 3 directly.
Proposition 2 is a statement about a *relaxation*, not
about polynomials: it says the consecutive-gap budget admits profiles that no
configuration need realise, which is precisely why it cannot be used as a bound.
The `M_circ` and `realisable` columns of §4 are numerical searches and carry no
universal quantifier; the `M_circ` column is additionally a grid value and is
not a certified upper bound. The certified statement is Theorem 5 applied to the
explicit `(S,U)` pairs the checker prints, together with the unchanged
comparison ODE. The floating suprema `0.65503` and `0.63003` are measurements.
Erdős #1041 remains open; the regime `13/25 < mu < 1` is untouched. No
priority claim is made: Lemma 3 follows directly from the disjointness of the hyperbolic balls
and the law of cosines, and should be assumed known.

## 8. Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_angular_budget_closure.py --quick
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_angular_budget_closure.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_angular_budget_closure.py --quick --audit
```

One JSON line each. The second (no `--quick`) form takes about `13.5` minutes and
prints `X_cert = 635762889599/1000000000000 < 0.6357629`, hence `mu <= 13/25`:
**that is the run Theorem A'' is quoted from.** The first finishes in under two
minutes on a coarser grid and prints
`X_cert = 664373027131/1000000000000 < 0.664374`, hence `mu <= 51/100`.
`all_degree.mu_threshold` is the theorem constant for that run, and
`circle_slice.duals_at_a_1` lists the certified `(S,U)` pairs at `a = 1` that §4
quotes — `(0.085674, 0.045865)`, `(0.126361, 0.021829)`, `(0.163157, 0.010513)`,
`(0.208928, 0.004318)`. The `sigma` are
proposed by `scipy.optimize.linprog` when SciPy is importable and by a
stdlib uniform-density search otherwise; the proposer changes the constant it
can reach but never the validity of what is printed, and the checker asserts
that whatever it reaches beats the landed `2/5`.

## Correction note, 2026-09-06 (appended; nothing above is rewritten)

**This note's numbers are correct and are the authority.** The 2026-09-06
integration pass re-read §5, §7 and §8 and confirms the certified pair printed
here:

```text
X_cert = 635762889599/1000000000000 < 0.6357629,  (13/25) exp(X_cert) < 1
```

full mode, at 18 area-table levels, 14 radii per dual, 126 certified duals,
step `1/400`, single initial lower area `10^-6`, about 13.5 minutes; quick mode
`X_cert = 664373027131/1000000000000` at threshold `51/100`. The same pair is
printed by the public copy of this argument at
`research_corpus/Erdos1041/LowCriticalPathCertificate.md` §5 in the release
candidate, so the two trees agree.

**Four downstream surfaces disagree with it and must be re-emitted.** They
print `X_cert = 317881444799/500000000000`, which is
`635762889598/1000000000000`. The certified numerator `635762889599` is odd, so
that form was obtained by halving after rounding the bound DOWN by `10^-12`.
A smaller `X` is a strictly stronger and uncertified statement, so the printed
form is not a harmless simplification. The surfaces are:

- `state/formal_math/claim_frontier_v1.json`, row
  `erdos1041.circle_slice_angular_closure_thirteen_twentyfifths`;
- `formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/research_packet.json`;
- `docs/formal_math/claim_frontier/erdos1041.md`;
- `docs/formal_math/comparator_architecture/discovery/erdos1041_anchored_results.md`.

The same rows also print `12 grid areas` where the certified run uses `18`.
The correction is emitted as
`docs/strategy/staging/rapid_breakout/audit/patches/frontier_1041.json`; the
claim-frontier file is shared, so it is not edited in place here.

**Public placement.** Theorem A'' now leads the public short note. It is §2 of
`paper/erdos-1041-lemniscate-newton-flow.tex` in the release candidate, with
the theorem at `res:low-critical-thirteen-twentyfifths`, the scale-free
corollary at `res:low-critical-scale-free`, and the boundary paragraph at
`bdry:low-critical-closure`, and it is named in the abstract, the
`paperresult` block, the `externalreviewobject` block and the status table.
Nothing about the mathematics changed; only its placement did.
