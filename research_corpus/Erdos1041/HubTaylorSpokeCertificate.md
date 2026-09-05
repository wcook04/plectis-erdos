# Erdős 1041: the hub-Taylor (truncation) straight-spoke certificate

Status, 2026-09-05. One proved elementary theorem whose metric side is free,
one exact certificate on the two configurations that refute the *critical*-hub
straight-spoke mechanism, one exact refutation of the whole standing hub set at
degree five inside the surviving regime, one exact no-go with a closed-form
constant, and a measurement over `9/25 < mu < 1`. **Erdős #1041 is not proved
here.** The lane's headline hypothesis — "some `mu_0 < 1` makes the criterion
hold at the least critical point `c*`" — is **false**, and the witness for that
part was already on file.

Replay: `./repo-python scripts/check_erdos1041_hub_taylor_spoke_certificate.py`

## 0. What was already corpus property before this note

The identity behind everything below is **not new**. Three existing rows own it:

- `abel_control_polygon_and_all_degree_trinomial_conclusion` — at a root `zeta`,
  `p(t zeta) = sum_{j<n} (t^j - t^{j+1}) S_j(zeta)` with `S_j` the coefficient
  partial sums, weights non-negative summing to `1 - t^n`. That is the hub-`0`
  case of everything in §1.
- `straight_spoke_hub_criterion_separation` — the sublevel test `|f| <= |f(c)|`
  and the open test `|f| < 1` are different statements; only the second is
  needed.
- [`GeneralSpokeIdentity.md`](GeneralSpokeIdentity.md) — identity (S) and
  criterion (SC) at a *critical* hub after the normalisation `G(0) = 1`,
  `G'(0) = 0`, with the 2026-08-23 correction recording that the crude form
  `|w| <= 1` is useless and the sharp form must be computed.

So §1 below is a **restatement at a general hub**, and the note claims novelty
only for §1.3 (the free length), §2 (the centroid certificate on the pinned
witnesses), §3 (the exact ceiling of the elementary-symmetric route), and §4
(the surviving-regime measurement).

## 1. The criterion at a general hub

Let `f` be monic of degree `n`, let `h` be any point of the plane, and let
`T_j` denote the degree-`j` Taylor truncation of `f` at `h`,

```text
T_j(z) = sum_{k=0}^{j} f^{(k)}(h) (z-h)^k / k! .
```

Write `b_k = f^{(k)}(h)/k!`, so `b_n = 1`. Let `a` be a **root** of `f` and put
`zeta = a - h`, `S_j = T_j(a) = sum_{k<=j} b_k zeta^k`.

**Lemma 1 (truncation identity).** For every `s`,

```text
f(h + s zeta) = sum_{j=0}^{n-1} (s^j - s^{j+1}) T_j(a).
```

*Proof.* `f(h+s zeta) = sum_{k=0}^{n} b_k zeta^k s^k`, and `f(a) = 0` gives
`zeta^n = - sum_{k<n} b_k zeta^k`. Hence
`f(h+s zeta) = sum_{k<n} b_k zeta^k (s^k - s^n)`. Abel summation of
`s^k - s^n = sum_{j=k}^{n-1}(s^j - s^{j+1})` reorders this into the stated form.
∎

Equivalently, in the coefficient form the lane started from,
`f(h + s zeta) = b_0 (1 - s^n) + sum_{i=1}^{n-1} b_i zeta^i (s^i - s^n)`.

On `[0,1]` the weights `s^j - s^{j+1} = s^j(1-s)` are non-negative and sum to
`1 - s^n`. Three criteria follow, each strictly sharper than the previous, all
sufficient for `[h,a] ⊂ {|f| < 1}`:

```text
(A)   max_{0<=j<n} |T_j(a)| < 1                                   (max form)
(A*)  max_{s in [0,1]} (1-s) sum_{j<n} |T_j(a)| s^j  < 1          (sharp form)
(E)   max_{s in [0,1]} |f(h + s zeta)| < 1                        (containment)
```

with `(E) <= (A*) <= (A)`, since `(A)` bounds `(A*)` by
`(1-s^n) max_j |T_j|` and `(A*)` bounds `(E)` by the triangle inequality.

### 1.1 The absolute-coefficient forms, and their exact suprema

The lane's stated criterion `sum_{i>=1} |b_i| r^i m_{i,n} < 1 - |b_0|` with
`m_{i,n} = max_s (s^i - s^n) = (i/n)^{i/(n-i)} (1 - i/n)` is the **term-wise**
weakening of

```text
(SC-sup)   max_{s in [0,1]} sum_{i=0}^{n-1} |b_i| r^i (s^i - s^n) < 1,
            r = |zeta|,
```

which is itself weaker than `(A*)`. With `beta_k = |b_k| |zeta|^k`, Abel
summation gives `sum_i beta_i (s^i - s^n) = sum_j (s^j - s^{j+1}) sum_{k<=j}
beta_k`, and `|T_j| <= sum_{k<=j} beta_k` termwise, so `(A*) <= (SC-sup)`.
Phases are the entire content of that gap; see §3.

### 1.2 `m_{i,n}` in closed form

`m_{i,n} = (i/n)^{i/(n-i)} (1 - i/n) < 1` for `1 <= i <= n-1`, `m_{0,n} = 1`.
Nothing below depends on this; it is recorded because the lane's brief named it.

### 1.3 The length obligation is free (new)

`T_{n-1} = f - (\cdot - h)^n`, so at a root `a`,

```text
T_{n-1}(a) = - (a - h)^n,       |T_{n-1}(a)| = |a - h|^n .
```

Criterion `(A)` therefore **contains** `|a - h| < 1`.

> **Theorem 2 (two-segment certificate with no metric hypothesis).** Let `f` be
> monic of degree `n` and let `h` be any point. If two distinct roots `a, b`
> satisfy
>
> ```text
> max_{0<=j<=n-1} |T_j(a)| < 1   and   max_{0<=j<=n-1} |T_j(b)| < 1,
> ```
>
> then the broken line `a -> h -> b` lies in `{|f| < 1}` and has length
> `|a-h| + |b-h| < 2`. Hence Erdős #1041 holds for `f`.

This is `two_segment_containment_reduction` with its condition (iii) —
`h` inside the open ellipse with foci `a, b` and major axis `2` — **deleted**:
it is implied by the containment certificate itself. The certificate is `2n`
complex numbers and no path tracking, so it is immune to the branch-tracking
defect class that produced five retracted counterexamples in this directory.

### 1.4 The criterion is exact on the equality family

For `f = z^n - lambda` and `h = 0`: `T_j = -lambda` for every `j <= n-1`, so

```text
(A) = (A*) = (E) = |lambda| = mu ,
```

with margin exactly `1 - mu`, and the two spokes have total length
`2 |lambda|^{1/n} = 2 cap{|f| <= mu}`. The criterion loses **nothing** on the
family that is the equality case of `capacity_geodesic_conjecture_and_its_equality_family`
and the extremal family of the whole problem. Every earlier straight-spoke
criterion in this directory was either marginal there (the sublevel form, where
`|f(t z_k)| = r^n(1-t^n)` touches its bound at `t = 0`) or lossy by ~10 percent
(`GeneralSpokeIdentity.md` (SC)).

## 2. Exact certificate at the centroid on the two pinned QC witnesses

[`StraightSpokeHubCriterionLab.md`](StraightSpokeHubCriterionLab.md) §3 pins two
configurations — degree six and degree nine, all roots strictly inside the disc,
stored as IEEE-754 hexadecimal literals in
`scripts/check_erdos1041_straight_spoke_hub_criterion.py` — at which **no**
critical point with `|f(c)| < 1` carries two open-contained straight spokes.
Both have `mu` deep in the surviving regime: `0.99995098...` and `0.99994148...`.

Take `h` = the **centroid of the roots** (an exact rational point, since the
roots are exact binary rationals). Then, in exact `Fraction` arithmetic:

| degree | `mu` | passing roots | `max_j |T_j(a)|^2` | length upper bound |
|---|---|---|---|---|
| 6 | 0.999950985997 | 0, 1 | 0.9999981468075212 | 1.9999283607213343 |
| 9 | 0.999941483500 | 5, 6 | 0.9999868689104863 | 1.9999669016543820 |

Both pairs satisfy criterion `(A)`, so by Theorem 2 the broken line through the
centroid lies in `{|f| < 1}` and is shorter than `2`. Every decision is a
comparison of exact rationals; the two lengths are bounded above by
`isqrt`-derived rationals with 48 fractional bits.

This is a second, independent positive resolution of the same two witnesses.
`pinned_witness_noncritical_hub_connectors` already resolved them with Bernstein
positivity certificates at the hand-chosen Gaussian-rational hubs
`h_6 = (3+2i)/25`, `h_9 = -1/5 - 4i/25`. What is new is that a **canonical**
hub — the centroid, with no search — works, and that the certificate is `2n`
rational comparisons rather than 64 Bernstein coefficients.

**Margins are small and are stated as such.** `1 - max_j |T_j|^2` is
`1.85e-6` and `1.31e-5`; the length slack is `7.2e-5` and `3.3e-5`. They are
exact, not estimated.

## 2b. Exact refutation of the whole hub set at degree five (new)

The wave's standing sampled truth was that every surviving-regime configuration
has a hub in `{critical c : |f(c)| < 1} ∪ {0}` carrying two contained straight
spokes (708 random survivors plus jittered and gap polygons to `n = 30`). That
is false, and the hub set can be widened to include the centroid and `c*`
without saving it.

> **Theorem 4.** There is an explicit monic quintic, all five roots strictly
> inside the unit disc, with `mu > 0.999987`, such that **no** point of
> `H = {c*} ∪ {critical c : |f(c)| < 1} ∪ {0} ∪ {centroid of the roots}`
> carries two straight spokes contained in `{|f| < 1}`. Every hub in `H` carries
> at most one.

The five roots are stored as IEEE-754 hexadecimal literals
(`QUINTIC_HUB_SET_WITNESS` in the checker); they are exact binary rationals,
of common modulus `0.999999995`, an angular perturbation of order `1e-4` of
the fifth roots of unity. The certificate is exact:

- all five `|a_j|^2 < 1` in `Fraction` arithmetic;
- the four critical points are isolated one per disc `D(c_i, 2^-30)` by an exact
  Rouché test against the linear part of the Taylor shift of `f'`;
- `mu >= 0.9999871398 > 9/25`, from the enclosed critical values with the disc
  absorbed by the crude Lipschitz bound `|f'| <= 5 * 3^4` on `|z| <= 2`;
- one critical disc has `|f| > 1` throughout, so it is inadmissible; the other
  three, and the hubs `0` and the centroid, each carry four spokes with an
  explicit rational escape parameter `t in {1/20, 1/10, 1/5}` at which
  `|f| - L * (1-t) * 2^-30 > 1`.

So each hub in `H` leaves at most one spoke inside, and two are needed.
Erdős #1041 is **not** refuted at this configuration: a free hub near
`-0.05 - 0.09i` carries two contained spokes (float evidence, criterion value
`0.99998752`). What dies is the hub *rule*.

Relation to what was already on file. `two_safe_origin_spokes_counterexample`
(with its 2026-08-24 correction) kills the origin hub alone;
[`CentroidHubCounterexample.md`](CentroidHubCounterexample.md) kills the
centroid hub alone; `StraightSpokeHubCriterionLab.md` §3 kills the critical-hub
set alone at degrees six and nine, and a near-Fekete quintic kills it at degree
five. Those are four configurations. Theorem 4 kills the **union** at **one**
configuration, and does so inside the surviving regime, which is what the
disjunction the wave was relying on actually required.

**Consequence for the criterion.** Since containment fails at every hub in `H`,
no criterion evaluated on `H` — `(A)`, `(A*)`, `(E)` or anything sharper — can
certify this quintic. Any completion must let the hub move off `H`. The
displacement is not small: the working free hub sits at distance `0.103` from
the centroid, which is the scale `rho_crit` of the split critical cluster, not
the scale of the perturbation.

## 3. Exact ceiling of the elementary-symmetric coefficient route (no-go)

The lane's task 3 proposed proving `mu > mu_0 ⇒` criterion, by bounding
`|b_i| = |e_{n-i}(a_j - h)| <= e_{n-i}(d_1, ..., d_n)` with `d_j = |a_j - h|`,
`prod_j d_j = |f(h)| = mu`, and taking the spoke radius `r = d_(2)`. That route
is dead, with an exact constant.

Since `sum_{i=0}^{n} e_{n-i}(d) x^i = prod_j (x + d_j)`, the route's checkable
condition is `Psi(s) < 1` for all `s in [0,1]`, where

```text
Psi(s) = prod_j (rs + d_j) - (rs)^n - s^n [ prod_j (r + d_j) - r^n ] .
```

On the regular configuration `f = z^n - mu` at its hub `0`, where
`d_j = r = mu^{1/n}` for every `j`, this collapses in closed form to

```text
Psi(s) = mu [ (1+s)^n - 2^n s^n ] ,
   sup_{s in [0,1]} Psi = c_n mu ,   c_n = 2^n / (2 * 2^{1/(n-1)} - 1)^{n-1} .
```

> **Proposition 3 (symmetric-function ceiling).** The elementary-symmetric
> coefficient route can certify a configuration only when `mu < 1/c_n`, and
> `1/c_n = 0.219420, 0.112816, 0.057436, 0.029084, ...` at `n = 4, 5, 6, 7`,
> decaying like `2^{-n}`. Since `1/c_n <= 1/c_4 = 0.2194196 < 9/25` for every
> `n >= 4`, the route lies **strictly inside** the regime already closed
> unconditionally by
> [`ClusterSeparationLowCriticalClosure.md`](ClusterSeparationLowCriticalClosure.md).
> It cannot reach the surviving regime at any degree `>= 4`.

The checker certifies this exactly for `4 <= n <= 64` by evaluating
`(1+s_n)^n - 2^n s_n^n >= 25/9` at stored rational probe points `s_n`; no
irrational optimisation enters the certificate. The term-wise `m_{i,n}` version
is worse: its multiplier is `M_n = sum_{i<n} C(n,i) m_{i,n}`, equal to
`4.8118, 9.2009, 17.8917, ...` at `n = 4, 5, 6`.

The reason is visible in one line. At the regular configuration the true
coefficients satisfy `b_i = 0` for `1 <= i <= n-1`, while
`e_{n-i}(d) = C(n,i) mu^{(n-i)/n}` is maximal. The bound `|b_i| <= e_{n-i}(d)`
throws away exactly the cancellation that makes the extremal family work.
**Any route that replaces the complex coefficients by moduli of symmetric
functions of the distances dies at the equality family, at every degree.**
`(SC-sup)` itself (using the true `|b_i|`) is not subject to Proposition 3, but
it is refuted directly in §4.

## 4. Measurement in the surviving regime `9/25 < mu < 1`

Floats; falsification evidence only. Hub set
`H = {c*} ∪ {critical c : |f(c)| < 1} ∪ {0} ∪ {centroid}`. A configuration
counts as covered by a criterion when some `h in H` carries two roots passing
it with `|a-h| + |b-h| < 2`. 250 survivors per degree, drawn from four families
(uniform in the disc, near-regular with perturbation `1e-6..1e-1`, deep
near-Fekete `1e-8..1e-3`, common-modulus circle), degrees 4 to 12,
2250 survivors total.

| n | `(A)` max form | `(A*)` sharp form | containment `(E)` | `(SC-sup)` absolute form | winning hub `(A)`: `c*` / other crit / `0` / centroid |
|---|---|---|---|---|---|
| 4 | 250 | 250 | 250 | 211 | 75 / 0 / 1 / 174 |
| 5 | 224 | 250 | 250 | 175 | 30 / 4 / 4 / 186 |
| 6 | 245 | 250 | 250 | 171 | 33 / 0 / 8 / 204 |
| 7 | 237 | 250 | 250 | 138 | 26 / 1 / 5 / 205 |
| 8 | 243 | 250 | 250 | 123 | 15 / 0 / 5 / 223 |
| 9 | 241 | 250 | 250 | 119 | 20 / 2 / 11 / 208 |
| 10 | 250 | 250 | 250 | 114 | 20 / 3 / 6 / 221 |
| 11 | 245 | 250 | 250 | 100 | 20 / 6 / 9 / 210 |
| 12 | 246 | 250 | 250 | 96 | 19 / 2 / 6 / 219 |

Readings.

1. **The sharp form `(A*)` covered every one of the 2250 *sampled* survivors** —
   but sampling is the wrong instrument here: the wall-guarded climb of reading
   5 found a degree-five configuration where `(A*)` and containment both fail at
   every hub of `H` (§2b). The max
   form `(A)` covered 2181; all 69 failures were near-regular and every one of
   them was still *contained*, so `(A)` is lossy, not violated as a geometric
   claim.
2. **The absolute-value form `(SC-sup)` degrades with degree** — 84% at `n = 4`
   down to 38% at `n = 12` — and fails at *every* hub on both pinned witnesses
   of §2. Together with Proposition 3 this closes the whole absolute-value lane.
3. **The centroid is the dominant hub**, winning 82% to 89% of covered cases
   from `n = 6` upward; `c*` wins 6% to 30% and falls with degree. This is the
   opposite of the corpus's default hub ordering.
4. **`c*` is refuted as a stand-alone hub, and the lane's task-3 hypothesis
   with it.** At both pinned witnesses the values at `c*` are `(A) = 1.0146` /
   `1.0092`, `(A*) = 1.000028` / `1.000030`, and `(E) = 1.0000093` / `1.0000104`
   at `mu = 0.99995` / `0.99994`. *Containment itself* fails at `c*` there, so
   no sharpening of the criterion can rescue it. There is **no `mu_0 < 1` for
   which `mu > mu_0` forces the criterion at `c*`**; the direction that survives
   is small `mu`, not large.
5. Wall-guarded adversarial climbs at degrees four and five (colliding critical
   points rejected; the objective is a direct polynomial evaluation, so the
   inverse-branch wall defect does not apply) maximising the best-hub value over
   configurations gave `0.99999994` for `(A*)`, `0.99999998` for `(A)` and
   `0.99999992` for containment at `n = 4`, each with `mu` equal to the value to
   within `1e-7` — the objective is pinned at `mu` from above. At `n = 5` the
   same climb **crossed 1**, for `(A*)` at `1.00000260` and for containment at
   `1.00000233`. That lead is certified exactly in §2b. Climbs at degrees six to
   eight were still running when this note was written and are not reported.
   Per the corpus's own methodological rule, the `n = 4` suprema below the
   threshold are reported as basin information only, not as evidence that the
   threshold is never crossed.

### 4.1 The residual quantity

The criterion value at the winning hub is bounded below by `|f(h)|` (take
`s = 0`, where every form equals `|T_0(a)| = |f(h)|`), and measurement says it
*tracks* `mu`. The right normalised objective is therefore

```text
N(f) = (1 - V(f)) / (1 - mu),        V(f) = min over h in H of the (A*) value.
```

`N > 0` is exactly "the criterion covers `f`". Over 200 survivors per degree the
infimum of `N` was `0.888, 0.793, 0.299, 0.477, 0.317, 0.038, 0.116` at
`n = 4..10`: **positive everywhere, but not visibly bounded away from zero as
the degree grows.** Whether `inf N > 0` uniformly is the open question this note
hands on.

## 5. Claim boundary

Proved unconditionally and exactly: Lemma 1 at a general hub (a restatement of
`abel_control_polygon_and_all_degree_trinomial_conclusion`), Theorem 2 including
the free length, the exactness of the criterion on `z^n - lambda` (§1.4),
Theorem 4 of §2b, and Proposition 3 with its closed-form constant `c_n`
certified for `4 <= n <= 64`.

Certified on three configurations: the centroid two-spoke certificate of §2 on
the two pinned QC witnesses, and Theorem 4 of §2b on the degree-five hub-set
witness.

Measured only: everything in §4. 2250 configurations is not a theorem, and the
`(A*)` coverage of 2250/2250 is a sampling statement in a regime whose hard
corner (`mu -> 1`) is reached only by families that were deliberately seeded.

Not proved: Erdős #1041, and no part of the surviving regime `9/25 < mu < 1`.
