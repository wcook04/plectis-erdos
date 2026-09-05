# Erdős 1041 at fixed degree: the angular separation bound

## Status

Ordinary complete proof of an unconditional fixed-degree family of theorems,
with an exact rational certificate. Not Lean-checked, not independently
reviewed. Erdős #1041 itself remains open.

This note supplies the fixed-degree arm that
[ClusterSeparationLowCriticalClosure.md](ClusterSeparationLowCriticalClosure.md)
declines to claim ("the fixed-degree lane has **not** been re-run against the
sharp floor (2') in this pass"). Re-running that lane was the assignment; doing
so turned up a strictly stronger ingredient, and the constants below come from
the new ingredient rather than from (2').

**The new ingredient.** The parent notes bound the COVER sum
`sum_j lam(d_j) >= x` using only the triangle inequality `d_i + d_j >= d_min`
between the two roots and the COVER point `h`. That inequality is the `phi = pi`
case of the hyperbolic law of cosines at `h`. Keeping the angle, and summing
`sin^2(phi_ij / 2)` over all pairs — an exact trigonometric identity bounded by
`k^2/4` — gives a second arity bound `Theta(k, a)` which is smaller than the
ordered-profile bound `Lambda(k, a)` at every degree `k >= 3`. The saving is
structural, not numerical: `Lambda` allows all `k` roots to sit at hyperbolic
distance `d_min/2` from `h`, and only **two** points can do that (they must be
antipodal as seen from `h`).

## Theorem

Let `f` be a squarefree monic polynomial of degree `n >= 3`, and put
`mu = min{ |f(c)| : f'(c) = 0 } > 0`.

> **Theorem A (fixed degree).** If `mu <= mu_n` then two distinct roots of `f`
> are joined by a rectifiable curve inside `{|f| < 1}` of length strictly less
> than `2`, where

| `n` | `mu_n` certified here | previously certified | mechanism value `exp(-B_n)` |
|---|---|---|---|
| 3 | `333/500` | (degree three is solved) | `0.666732` |
| 4 | `61/100` | `1/2` | `0.610204` |
| 5 | `139/250` | `9/20` | `0.556564` |
| 6 | `253/500` | `2/5` | `0.506687` |
| 7 | `23/50` | `7/20` | `0.460759` |
| 8 | `209/500` | `9/25` (all-degree) | `0.418688` |
| 9 | `19/50` | `9/25` (all-degree) | `0.380271` |
| 10 | `9/25` (inherited) | `9/25` (all-degree) | `0.345257` |
| 11 | `9/25` (inherited) | `9/25` (all-degree) | `0.313386` |
| 12 | `9/25` (inherited) | `9/25` (all-degree) | `0.284401` |

The "previously certified" column is the quick-mode fixed-degree row of
`ClusterSeparationLowCriticalClosure.md` against the crude floor; below degree
`10` the constants here are strictly larger, and at degrees `8` and `9` they are
the first fixed-degree constants to beat the all-degree `9/25`. At degree `10`
and above the all-degree theorem is still the better statement, and the rows are
inherited rather than proved here.

No hypothesis is placed on root locations, component arity, or component
capacity. A repeated root gives the constant curve, so the squarefree case is
the nontrivial branch. The scale-free corollary is the same as in the parent
note: every squarefree monic `f` of degree `n` has two distinct roots joined
inside `{|f| < mu/mu_n}` by a curve of length below `2 (mu/mu_n)^(1/n)`.

## The setup, unchanged

Assume for contradiction that no two distinct roots of `f` are joined inside
`{|f| < 1}` by a curve of length below `2`. Fix a least-critical point `c*`, let
`Gamma` be the union of two descending inverse arcs from `c*` into two distinct
one-root lobes of `{|f| < mu}`, and for regular `t > mu` let `C_t` be the
component of `{|f| < t}` containing `Gamma`, with `k = k(t) >= 2` roots and
`a = Area(C_t)/pi`. Since `t < 1`, Pólya gives `a <= t^(2/n) <= 1`, and `k <= n`.

Uniformise `C_t` by the unit disc, sending the COVER point `h` to `0`; `f/t`
becomes a finite Blaschke product of degree `k` with zeros `b_1, ..., b_k`. Write
`rho_j = |b_j|`, `d_j = 2 artanh(rho_j)`, `phi_j = arg b_j`, and

```text
lam(d) = -log tanh(d/2) = 2 artanh(e^-d),      lam(lam(d)) = d.
```

Three facts from `ClusterSeparationLowCriticalClosure.md` carry over verbatim:

* **(F1) the Blaschke identity.** `prod_j rho_j = |f(h)|/t <= mu/t = e^-x`, so
  `sum_j lam(d_j) >= x`, where `x = log(t/mu)`.
* **(F2) COVER failure.** Failure supplies `h in Gamma` at intrinsic distance
  above `1` from every root, and the one-root Bergman bound then gives
  `lam(d_j) <= delta(a)/2` for every `j`, `delta(a) = -log(1 - e^(-1/a))`.
* **(F3) pairwise separation.** Failure and Lemma 1 (two-point Bergman) give
  `d(b_i, b_j) >= d_min(a) = 4 artanh(sqrt(tanh(1/a)))` for every `i != j`.
  Equivalently `d_min = 2 lam(tau/2)` with `tau(a) = -log tanh(1/a)`.

Substituting `w_j = e^(-d_j) in (0, W]`, `W = W(a) := tanh(delta(a)/4)`, turns
(F1)+(F2) into

```text
sum_j 2 artanh(w_j) >= x,           w_j <= W.                             (1)
```

## The angular bound

> **Lemma 2 (pairwise, exact).** With `M = M(a) := cosh d_min(a)` and
> `s_ij = sin^2((phi_i - phi_j)/2)`, (F3) is equivalent to
>
> ```text
> (1 + w_i^2 w_j^2) s_ij + (w_i^2 + w_j^2)(1 - s_ij)  >=  2 M w_i w_j,
> ```
>
> and therefore implies the relaxed form
>
> ```text
> s_ij  >=  2 M w_i w_j - w_i^2 - w_j^2.                                   (2)
> ```

*Proof.* The hyperbolic law of cosines at the origin of the disc reads
`cosh d_ij = cosh d_i cosh d_j - sinh d_i sinh d_j cos(phi_i - phi_j)`. With
`cosh d = (1/w + w)/2` and `sinh d = (1/w - w)/2`, and
`1 - cos phi = 2 sin^2(phi/2)`, `1 + cos phi = 2 cos^2(phi/2)`,

```text
2 cosh d_ij = (1/(w_i w_j) + w_i w_j) s_ij + (w_i/w_j + w_j/w_i)(1 - s_ij).
```

Multiplying `cosh d_ij >= M` by `2 w_i w_j > 0` gives the displayed equivalence.
Moving the `s_ij` terms to one side, its coefficient is
`1 + w_i^2 w_j^2 - w_i^2 - w_j^2 = (1 - w_i^2)(1 - w_j^2) in (0, 1]`, so dividing
by it can only increase the right-hand side; if the right-hand side is negative
(2) is trivial. ∎

Taking `s_ij = 1` in Lemma 2 recovers exactly `w_i w_j <= e^(-d_min) =: P`, which
is the triangle inequality `d_i + d_j >= d_min` and is all the parent notes use.

> **Lemma 3 (angular second moment).** For any angles `phi_1, ..., phi_k`,
>
> ```text
> sum_{i<j} sin^2((phi_i - phi_j)/2) = ( k^2 - |sum_j e^{i phi_j}|^2 ) / 4
>                                    <= k^2/4.
> ```

*Proof.* `|sum_j e^{i phi_j}|^2 = k + 2 sum_{i<j} cos(phi_i - phi_j)`, and
`sin^2(theta/2) = (1 - cos theta)/2`. ∎

> **Theorem 4 (the arity bound).** Under the failure hypothesis, at every regular
> level `t in (mu, 1)`,
>
> ```text
> x  <=  Theta(k, a) := 2 S(k, a) / (1 - W^2),
> ```
>
> where `S(k, a)` is the positive root of
>
> ```text
> M S^2 - (M + k - 1) r S - [ k^2/4 + (M + k - 1) W (W - r) ]  =  0,
> r = r(a) := tanh(tau(a)/4) = e^(-d_min/2).
> ```

*Proof.* Put `S = sum_j w_j` and `Q = sum_j w_j^2`. Summing (2) over all pairs
and using Lemma 3,

```text
M (S^2 - Q) - (k - 1) Q  =  sum_{i<j} (2 M w_i w_j - w_i^2 - w_j^2)  <=  k^2/4,
```

that is `M S^2 <= k^2/4 + (M + k - 1) Q`. Order `w_1 >= ... >= w_k`. The
triangle-inequality form `w_i w_j <= P = r^2` applied to the pair `(1,2)` gives
`w_2 <= r`, hence `w_j <= r` for every `j >= 2`, so

```text
Q  <=  w_1^2 + r (S - w_1)  =  r S + (w_1^2 - r w_1)  <=  r S + W (W - r),
```

because `w -> w^2 - r w` is convex on `[0, W]` with values `0` at `0` and
`W(W - r) >= 0` at `W` (and `W > r` since `tau < delta`). Substituting and
solving the quadratic bounds `S`, and `2 artanh(w) <= w/(1 - w^2) * 2 <= 2w/(1 - W^2)`
converts the bound on `S` into a bound on `sum_j 2 artanh(w_j)`, which is at
least `x` by (1). ∎

**Assembly.** Failure forces, at every regular `t in (mu, 1)`,

```text
x = log(t/mu)  <=  B(n, a),      B(n, a) := min( Lambda(n, a), Theta(n, a) ),
```

using `k <= n`, the monotonicity of `Lambda` and `Theta` in `k`, and
`a <= t^(2/n) <= 1` with the monotonicity of both in `a`. Letting `t -> 1`
through regular values gives `log(1/mu) <= B(n, 1)`, so any `mu` with
`mu e^(B(n,1)) < 1` is contradictory. That is Theorem A, and the checker
certifies `mu_n * exp_upper(B_upper(n, 1)) < 1` in exact rational arithmetic.

At `a = 1` the constants are `delta = 0.4586751`, `tau = 0.2723415`,
`W = 0.1141688`, `r = 0.0679804`, `M = 108.19630`, and `Theta` is the binding
branch at every `n >= 3`. Asymptotically `Lambda(k,1) = 0.1361707 k` while
`Theta(k,1) ~ 0.0980460 k`, so the new bound is a uniform `1.389`-fold
strengthening of the arity floor, not a small-degree accident.

## What the per-component caps do, and do not, do

The assignment asked for the per-component cap of
[ExteriorBlaschkeFibreCapacityGap.md](ExteriorBlaschkeFibreCapacityGap.md)
Corollary 3 (6),

```text
Area(C_t)/pi < t^(2/n) (k/(2n-k))^(2/n)          for a component with k < n roots,
```

to be added rigorously, noting that `k` is known only from below while
`(k/(2n-k))^(2/n)` is *increasing* in `k`. The rigorous device is a case split on
the true arity: the arity `k(t)` of the ancestor component is a non-decreasing
integer function of `t` with values in `[2, n]`, so the failure trajectory can be
tracked as a branch DP over `k`, each branch carrying its own cap `(6)`, its own
area lower bound `a >= a_floor(x, k)` (the smallest `a` with `B(k, a) >= x`), and
its own boundary-hop forcing `a' >= G(x, a, max(k, k_low(x,a)))`. At `k = n` the
formula degenerates to the plain Pólya cap `t^(2/n)`, which is correct: a
component holding all `n` roots is `K_t` itself and has capacity exactly
`t^(1/n)`.

**Measured result: at every degree the cap changes nothing.** Running the branch
DP with and without Corollary 3 gives identical thresholds at `n = 7, 8` (and the
DP as a whole adds nothing below `n = 8`). The reason is structural and worth
recording so it is not re-attempted: the low-arity branches are already killed by
the area floor `a >= a_floor(x, k)` well before their smaller caps bite, and the
full-arity branch — which is the one that survives longest — is exempt from
Corollary 3 by construction. The full-arity branch is reachable at `x = 0`: for
`f = z^n - m` the component of `{|f| <= mu}` containing the descending arcs
already contains all `n` roots, since every lobe meets the origin. So no
hypothesis excludes it.

The boundary-hop ODE of the parent note likewise contributes nothing at
`n <= 7`: the floating supremum of the full mechanism (floor + forcing + caps) is
`0.666754, 0.610224, 0.556596, 0.506713, 0.460768` at `n = 3..7`, against
`0.666732, 0.610204, 0.556564, 0.506687, 0.460759` for the floor alone. At
`n >= 8` the ODE does contribute — floating `0.433071, 0.442668, 0.452328` at
`n = 8, 9, 10` — but that arm is not certified in exact arithmetic here, so the
`n >= 8` rows of Theorem A come from the floor alone.

## Consequence for the all-degree lane

The new arity bound is degree-free, so it also feeds the all-degree comparison
ODE of `ClusterSeparationLowCriticalClosure.md` in place of `Lambda`. Replacing
the floor there and re-running the same monotone comparison in floating point
moves the mechanism's supremum from `X_* = 0.99500` (`mu = 0.36972`) to
`X_* = 0.83753` (`mu = 0.432778`). That is a floating measurement, not a
certificate; the exact rational re-run of the all-degree arm against `Theta` is
the obvious next landing and is not attempted here.

## What is left, per degree

The surviving interval at degree `n` is `(mu_n, 1)`. No proved statement in this
corpus covers the top of that interval at any degree above three.

* `n = 3` is proved outright (`cubic_minimal_critical_value_short_hub`).
* `n = 4` is prior art (Pendyala's quartic proof, via the origin route).
* For `n >= 5` the near-Fekete route bites only at the very top. The resultant
  identity gives `mu^(n-1) <= D = prod_{i<j}|z_i - z_j|^2 / n^n`
  ([HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md)), so `mu > mu_n` only
  forces `D > mu_n^(n-1)`, which is `0.0956` at `n = 5` and `0.0332` at `n = 6` —
  far from the regime where Fekete stability
  ([NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) Theorem A) says anything.

**Degree five was measured, and the proposed closure chain is false.** Over
`57921` degree-five configurations with all roots strictly inside the disc and
`mu > 139/250` (shell and near-Fekete seeding; a plain uniform sample produced
`0` survivors in `40000` draws, so the theorem already removes every generic
degree-five configuration):

| `mu` band | survivors | max angular-gap deviation from `2 pi / 5` | min `D` | origin two-spoke certificate holds |
|---|---|---|---|---|
| `[0.557, 0.7)` | 2740 | `1.2166` rad | `0.0983` | `1.2 %` |
| `[0.7, 0.85)` | 3705 | `0.8574` rad | `0.2435` | `1.5 %` |
| `[0.85, 0.95)` | 5375 | `0.5856` rad | `0.5279` | `1.7 %` |
| `[0.95, 0.99)` | 7845 | `0.0955` rad | `0.8173` | `1.6 %` |
| `[0.99, 1.01)` | 38256 | `0.0230` rad | `0.9610` | `31.7 %` |

Two readings. First, near-regularity is genuine but only above `mu ~ 0.95`: the
band `(0.556, 0.95)` contains survivors `1.2` radians away from the regular
pentagon, so "`mu > mu_5` forces the root polygon within a quantified distance of
the regular pentagon" is **false** as stated. Second, the origin two-spoke
certificate `sum_{i=1}^{n-1}|c_i| < 1 - |c_0|` fails on `98 %` of the survivors
in every band below `0.99`, so it cannot be the high-regime half of a closure
chain at degree five. Degree five is not closed, and this particular chain is
retired. The same seeding at degree six behaves the same way.

The smallest open sub-statement this note leaves is the packing gap. The direct
optimum of the packing problem behind Theorem 4 — maximise `sum_j 2 artanh(w_j)`
over `w_j <= W` and angles subject to the exact constraint of Lemma 2 — was
measured by constrained local optimisation with `300` restarts per `k` at
`a = 1`:

| `k` | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|
| direct optimum | `0.3103` | `0.3784` | `0.4306` | `0.4694` | `0.4986` | `0.5208` | `0.5413` | `0.5578` | `0.5759` |
| `Theta(k,1)` proved here | `0.3238` | `0.4054` | `0.4940` | `0.5860` | `0.6799` | `0.7749` | `0.8706` | `0.9669` | `1.0635` |

Every direct optimum lies below the proved bound, as it must. Closing that gap —
proving `x <= V_k` for the measured `V_k` — would give `mu_4 >= 0.650`,
`mu_5 >= 0.625`, `mu_6 >= 0.607`, `mu_7 >= 0.594`. The measured optima grow like
`C log k` (consecutive "radial generations" must be separated by a factor
`e^(d_min) = 216` in `1 - rho`, and each generation contributes about
`2 pi e^(-d_min/2)`), so the packing route does **not** close the all-degree
problem; it is a `log n` improvement at fixed degree.

## Claim boundary

Theorem A is an ordinary argument, not Lean-checked and not independently
reviewed. Lemmas 2 and 3 are elementary hyperbolic trigonometry and an elementary
trigonometric identity; both were audited numerically against `4000` random disc
configurations with the Poincaré cross-ratio formula as the independent model
(maximum violation `0`, maximum identity error `1.1e-39` at 40 digits). The
inputs (F1)–(F3) are the parent note's and inherit its claim boundary. The
floating suprema and the degree-five survivor table are measurements, not
certificates. Erdős #1041 remains open; nothing here touches the interval
`(mu_n, 1)`.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_fixed_degree_cluster_closure.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_fixed_degree_cluster_closure.py --audit
```

The first form is the exact rational certificate for the whole table and runs in
a couple of seconds; `per_degree[n].mu_threshold` is the theorem constant. The
second adds the independent numerical audit of Lemmas 2 and 3 and the
`Lambda`-versus-`Theta` comparison, and is still under a minute.
