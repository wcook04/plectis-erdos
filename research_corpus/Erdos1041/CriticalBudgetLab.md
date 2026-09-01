# Erdős 1041: the global critical-point length budget

The problem, exactly as stated: for `f(z) = ∏ᵢ(z − zᵢ)` with `|zᵢ| < 1`, must there
be a path of length less than 2 inside `{|f| < 1}` joining two of the roots?
Erdős, Herzog and Piranian proved that some component of that set contains at
least two of the roots, so a joinable pair always exists; the length is what is
open.

Everything in [TrueGeodesicLab.md](TrueGeodesicLab.md) measures a geodesic on a
grid, and its recurring failure is that a *tight* statement tested on a grid
reports a false violation — three times, in three different guises. The
load-bearing budget derivation in this lab takes the opposite approach: it is
**grid-free**, using exact algebra on roots and critical points, so the
thin-corridor trap cannot affect that proof. Later sections retain numerical
diagnostics, which are labelled as finite evidence and are not proof authority.
What replaces the grid in the proved portion is the observation that a path
through a critical point has a length *budget* that is pure algebra, and the
budget can be attacked without ever drawing a path.

## 2026-08-23 outcome: B1 holds globally

The two-nearest-root budget is now proved at **every** critical point, not only
in the formerly covered region `|c| ≤ 1 - 2/n`:

> **Global critical budget.** Let `f` have degree `n ≥ 2` and all roots in the
> closed unit disk. At every critical point `c`, the two nearest roots, counted
> with multiplicity, satisfy `d₁ + d₂ ≤ 2` (with the multiple-root case
> immediate).

The proof combines (STAR) below with reciprocal balance. Put `t = |c|`,
`δ = d₁`, and `e = d₂`. Then

`n ≤ (1-t²)(δ⁻² + (n-1)e⁻²)`,  `δ ≤ 1`,
`e ≤ (n-1)δ`, and `e ≤ 1+t`.

If `δ+e>2`, then `δ>1-t` and hence
`1-t² < δ(2-δ) < δe`. The displayed inverse-square estimate would give

`n < e/δ + (n-1)δ/e`.

But `x=e/δ` lies in `[1,n-1]`, and
`(x-1)(x-(n-1)) ≤ 0` is equivalent to
`x+(n-1)/x ≤ n`, a contradiction.

The complete ordinary proof and scope boundary are in
[GlobalCriticalTwoNearestBudget.md](GlobalCriticalTwoNearestBudget.md). The
algebraic implication is checked in
[`two_add_le_two_of_disk_inverse_balance`](CriticalTwoRootProximity.lean#L160-L166),
and the general root-selection consumer is
[`exists_two_roots_dist_sum_le_two_mul_geomMean`](CriticalTwoRootProximity.lean#L229-L234).
Replay the Lean module from the repository root with:

```sh
lake env lean research_corpus/Erdos1041/CriticalTwoRootProximity.lean
```

This closes the Euclidean metric subproblem B1. It still does not prove that
the selected roots can be connected within the lemniscate at that length.

## The identity

Let `c` be a critical point of `f`, so `Σᵢ 1/(zᵢ − c) = 0`. Put `wᵢ = zᵢ − c` and
expand `|c + wᵢ|² ≤ 1`:

`|c|² + 2 Re(c̄ wᵢ) + |wᵢ|² ≤ 1`,  with slack exactly `1 − |zᵢ|²`.

Divide by `|wᵢ|²`, use `Re(c̄wᵢ)/|wᵢ|² = Re(c/wᵢ)`, and sum over `i`. The
critical-point condition kills the cross term, because `Σᵢ Re(c/wᵢ) = Re(c Σᵢ 1/wᵢ) = 0`.
What is left is an identity:

> **(ID)** `Σᵢ (1 − |zᵢ|²)/|zᵢ − c|²  +  n  =  (1 − |c|²) Σᵢ 1/|zᵢ − c|²`
>
> at every critical point `c` of every monic `f`.

No disk hypothesis is used in deriving it. The disk hypothesis is what makes the
first sum non-negative, and that gives two corollaries at once:

> **(STAR)** `Σᵢ 1/|zᵢ − c|² ≥ n/(1 − |c|²)`, with equality iff every `|zᵢ| = 1`.
>
> **(NEAR)** the nearest root to `c` is within `√(1 − |c|²) ≤ 1`.

(NEAR) is sharp: at `n = 2` with roots `e^{iα}, e^{−iα}` the critical point is
`cos α` and both roots are at distance `sin α = √(1 − |c|²)`. The obvious
strengthening `d₁ ≤ 1 − |c|` is **false** — roots `1` and `i` give `d₁ = √2/2`
against `1 − |c| = 1 − √2/2 ≈ 0.293` — which is worth recording, because that
strengthening would have implied everything below in one line.

## Why a joinable pair exists at all: the discriminant

The existence half is a short consequence of two classical facts, and it is
included because its equality case turns out to be the same family that the
sharpness theorem in TrueGeodesicLab identifies as extremal.

For monic `f`, the resultant identity `res(f, f') = ∏ᵢ f'(zᵢ) = ±nⁿ ∏ₖ f(cₖ)`
gives

`∏ₖ |f(cₖ)|  =  ∏_{i<j} |zᵢ − zⱼ|² / nⁿ`

over the `n−1` critical points with multiplicity. Fekete's theorem says the
Vandermonde product over the closed unit disk is at most `n^{n/2}`, attained
exactly at the `n`-th roots of unity. So

`∏ₖ |f(cₖ)| ≤ 1`, with equality iff the roots are the `n`-th roots of unity.

With the roots in the **open** disk the inequality is strict, so some critical
value has modulus below 1, so `{|f| < 1}` has fewer than `n` components, so some
component holds two roots. That is the Erdős–Herzog–Piranian statement.

Two notes on authority. This is very likely EHP's own argument or a standard one,
and nothing about this derivation is claimed as new. The historical datum is
now pinned to the downloaded EHP58 primary PDF
`annexes/erdos-herzog-piranian-1958-metric-properties-of-polynomials/source.pdf`
(SHA-256
`bff39876de5e152b5a0d2b622eb6f9ca0c747d401ceea68146cfa2b2b5f28ce9`): printed
p. 139 / PDF p. 15 / `extracted.md` lines 594--602 records the unit-disc
setting, the component containing at least two zeros, and Problem 5's path
question. That source supports the historical problem setting only; it does
not certify this lab's derivation, its equality interpretation, or any novelty
claim. What *is* worth recording is the equality case: it is `zⁿ − 1`, the `r → 1`
limit of the family `zⁿ − rⁿ` that the sharpness theorem shows is extremal for the
constant 2. The mechanism that barely produces a joinable pair and the family that
barely admits a path of length 2 are the same polynomial.

## Historical selector computations and their corrections

A path from `z_a` up to a critical point `c` and back down to `z_b` has length
target `|z_a − c| + |z_b − c|`. The conjecture is that some hub and some pair keep
that below 2. Getting the *quantity* right took two corrections, and both went the
same way, so the pair is worth recording together.

**First attempt (corrected 2026-08-23).** A legacy descent run at `n = 4`, with
roots near `0.762`, `i`, `−0.970 + 0.115i`, `−i`, reported **2.0068** at the
least-critical-value hub. That number was a branch-tracking error, not a
counterexample and not valid selector evidence. Recovering the recorded roots
as exact eight-decimal Gaussian rationals and replaying residual-gated
inverse-value continuation lands the two branches at roots 0 and 1. At step
sizes `0.004`, `0.002`, and `0.001`, the normalized curved total converges to
**0.7385324012**. See
`scripts/check_legacy_minimum_critical_descent_regression.py` and its generated
receipt. The historical lesson about validating branch identities remains;
the claimed crossing does not.

**Second attempt (corrected 2026-08-23, same fault).** Minimise the merge-pair
budget over all hubs with `|f(c)| < 1`. A search maximising that reported apparent
violations of `2.132146`, `2.116316` and `2.013509` at `n = 3, 4, 7`, and I recorded
them, together with a "correction" that attributed the gap to restricting the pair.
**All three numbers came from the same mistracking descent as the first attempt, and
none of them is real.**

Retracing the `n = 3` configuration with a residual-gated continuation at 20000
steps — endpoints landing within `1e-16` of a root, worst value-ray residual
`1.1e-16` — gives:

| hub | `\|f(c)\|` | branches reach | budget | arc |
|---|---|---|---|---|
| `0.551999 − 0.057887i` | 0.769684 | roots 1 and 2 | **1.441607** | 1.459359 |
| `−0.293578 − 0.468494i` | 0.772535 | roots 2 and 0 | **1.445458** | 1.463519 |

Two different pairs, which is what a merge tree requires and what the broken run
could not produce — it returned the same pair at both hubs. The true merge-pair
budget is `1.441607`, which is **exactly the number I had quoted as the corrected
"component" value.** So on that configuration the merge-pair and component readings
are identical and the contrast I drew between them was entirely manufactured.

What survives and what does not. The *principle* is still sound: a hub's component
of `{|f| < 1}` can contain more roots than the two that merge at it, so restricting
to the merge pair does discard candidates from a minimum, and that direction of bias
is real. But I have **no configuration where it actually bites** — the evidence I
offered for it was an instrument artifact. It should be read as a hazard to guard
against, not as an observed phenomenon.

The independent arbitration also settles the first attempt from this side: at that
`n = 4` hub the branches reach roots 0 and 1 for a budget of `1.434839` and an arc
of `1.477065`, matching both the concurrent regression check and the inverse-ray
lab's own scorer to six decimals. Three instruments agree; mine was the outlier.

> **B3′.** Let `c` be a critical point with `|f(c)| < 1` and let `K(c)` be the
> component of `{|f| < 1}` containing it. The budget at `c` is the sum of the two
> smallest distances from `c` to roots of `K(c)`. Conjecture: the minimum of that
> over all such `c` is at most 2.

**B3′ collapses onto B1 in the generic case.** The number of components of
`{|f| < t}` is `n` minus the number of critical points with `|f(c)| < t`, so
`{|f| < 1}` is connected exactly when **every** critical value is below 1 — and
then `K(c)` is everything, so the budget at `c` is the sum of the two smallest
distances from `c` to *any* roots. That is precisely B1's quantity. So B1 is not a
cleaner cousin of the operative statement; in the connected case it **is** the
operative statement, and the theorem below applies to it directly. Only when some
critical value reaches 1 does the component structure bite, and then the merge
tree is needed.

**Third attempt, and where B3′ actually stands.** Maximising the corrected B3′
also produced values above 2 — `2.473` at `n = 5`, `2.396` at `n = 6`, `2.185` at
`n = 8`. Auditing those before believing them: every one is disconnected, and the
minimum was taken over **one or two usable hubs out of four to seven**, the rest
dropped because the merge-tree descent failed to track. The search had found the
instrument's drop rate, not the mathematics. In all four cases the certified
polyline bound on the actual geodesic is `1.553`, `0.955`, `0.899`, `1.990` — well
under 2 — so #1041 is comfortable at every one of them.

Two kinds of exclusion have to be told apart here, and only one of them is a bug.
A hub with `|f(c)| ≥ 1` is not in `{|f| < 1}` at all, so excluding it is correct
mathematics. A hub whose descent failed is an instrument failure, and dropping it
from a minimum is the same bias again.

At the time of the original experiment, the standing status was:

* **connected** (every critical value below 1): B3′ *is* B1's quantity and needs
  no descent. The new global theorem proves this metric budget at every `c`.
* **disconnected**: B3′ is **not measured**. The merge tree is needed, the descent
  is not yet reliable enough to build it on the configurations a maximising search
  selects, and no number reported for that case should be trusted in either
  direction.

**The lesson, in its fifth appearance and its general form.** TrueGeodesicLab
records this trap three times as *a tight conjecture tested numerically without a
guard reports failure*. The `n = 4` selector and the merge-pair restriction are
the same trap wearing a different coat, and the general statement covers all five:

> A conjecture that bounds a **minimum** from above is refuted by any test that
> minimises over a subset of the candidates. Restricting the pair, fixing the hub,
> and silently dropping a hub whose descent failed to track are all that error.

That rule is sound and worth keeping. What the retractions above add is a second,
worse failure mode sitting underneath it: the candidate set can be **wrong** rather
than merely incomplete. A branch-identification routine that names the wrong root
does not restrict the minimum, it computes a different quantity altogether, and no
amount of care about minima catches that. The tell was available and I ignored it —
the same routine had already returned the same merge pair at two different hubs,
which no merge tree permits.

The first `hub_rows` did all three. The rewrite takes the component and reports
the unresolved count — but it still *skips* those hubs when taking the minimum,
which is why the disconnected case above is marked unmeasured rather than
refuted. Reporting a drop is not the same as not dropping.

There is a companion to this, and TrueGeodesicLab already names it once under
*the optimiser finds the method's failure mode first*. This session added three
more instances — raw grid geodesics into thin corridors, the merge-pair
restriction, and now the unresolved-hub drop — which is enough to state it
generally:

> A search that maximises a statistic will find its instrument's failure mode
> before it finds the mathematics, because the failure mode is usually the
> cheapest way to make the number large.

The practical consequence is that an apparent violation is evidence about the
instrument until audited, and the audit is not optional: three times here the
audit reversed the verdict.

## Superseded partial proof: the former |c| ≤ 1 − 2/n region

The argument in this section remains a valid sharper case analysis and records
the equality family that exposed the threshold. It is no longer the claim
frontier: the global proof above removes the radius restriction by combining
(STAR) directly with reciprocal balance.

Write `t = |c|`, `m = √(1 − t²)`, and `zᵢ = c + dᵢe^{iφᵢ}` with `φᵢ` measured from
the direction of `c`. Two facts drive everything:

`(F1)  dᵢ² + 2t dᵢ cos φᵢ ≤ 1 − t² = m²`   (this *is* `|zᵢ| ≤ 1`)
`(F2)  Σᵢ cos φᵢ / dᵢ = 0`                  (the real part of `Σ 1/(zᵢ−c) = 0`)

Call a root **on the c-side** when `cos φᵢ ≥ 0`. By (F1) such a root has `dᵢ ≤ m`.

**Case `t = 0`.** (F1) reads `dᵢ ≤ 1` for every root, so `d₁ + d₂ ≤ 2`. ∎

**Case: two or more roots on the c-side.** Both are within `m`, so
`d₁ + d₂ ≤ 2m ≤ 2`. ∎

**Case: none.** Then every `cos φᵢ < 0` and (F2) fails. So this case is empty
unless every `cos φᵢ = 0`, in which case (F1) gives `dᵢ ≤ m` for all `i` and again
`d₁ + d₂ ≤ 2m ≤ 2`. ∎

**Case: exactly one root on the c-side.** This is the only case that survives, and
it is where every observed equality lives. Let `z₁` be that root, `δ = d₁`, and
`e = min_{j≠1} dⱼ`. Suppose `d₁ + d₂ > 2`. If two of the far roots were within `δ`
then `d₁ + d₂ ≤ 2δ ≤ 2m ≤ 2`; so the two smallest distances are `δ` and `e`, and
`δ + e > 2`. Since `δ ≤ m ≤ 1` and `e ≤ 1 + t`, this forces

`e > 2 − δ ≥ 2 − m ≥ 1`   and   `δ > 1 − t`.

For a far root, (F1) gives `−cos φⱼ ≥ (dⱼ² − m²)/(2t dⱼ)`, so with
`S := Σ_{j≠1} (−cos φⱼ)/dⱼ` and `dⱼ ≥ e > 2 − δ`,

`2tS ≥ (n−1)(1 − m²/(2−δ)²)`.

By (F2), `cos φ₁ = δS`, and (F1) for `z₁` reads `δ²(1 + 2tS) ≤ m²`. Combining,

`ψ(δ) := n δ² − (n−1) m² δ² / (2−δ)²  ≤  m²`.

Now `ψ'(δ) = 2δ[n − 2(n−1)m²/(2−δ)³]`, whose bracket decreases in `δ`, so `ψ`
rises then falls and its minimum over `(1−t, m]` is at an endpoint.
`ψ(m) = m²(1 + (n−1)(1 − m²/(2−m)²)) > m²` whenever `t > 0`. And

`ψ(1−t) ≥ m²  ⟺  (1−t)(1 + 2t(n−1)/(1+t)) ≥ 1+t  ⟺  (n−1)(1−t) ≥ 1+t  ⟺  t ≤ 1 − 2/n.`

So for `t ≤ 1 − 2/n` we have `ψ(δ) > m²` throughout `(1−t, m]`, contradicting the
display above. (At `t = 1 − 2/n` exactly, `ψ(1−t) = m²` and
`ψ'(1−t) = 2(1−t)·n(n−2)/(n−1) > 0` for `n ≥ 3`, so the strict inequality still
holds for `δ > 1 − t`.) ∎

> **Theorem.** Let `f` be monic of degree `n ≥ 2` with all roots in the closed unit
> disk, and let `c` be a critical point with `|c| ≤ 1 − 2/n`. Then the two smallest
> distances from `c` to the roots, listed with multiplicity, satisfy `d₁ + d₂ ≤ 2`.
> For `n = 2` the conclusion holds at every critical point, since the only one is
> the midpoint of the roots.

The two roots realising `d₁` and `d₂` are distinct points whenever `f` is
squarefree; if it is not, they may coincide and the statement is true but empty —
the same convention [CubicCriticalHub.md](CubicCriticalHub.md) uses, and #1041 is
trivial for a repeated root in any case.

Putting the theorem together with the component count gives the payoff:

> **Corollary.** Suppose every critical value of `f` satisfies `|f(cₖ)| < 1`, so
> that `{|f| < 1}` is connected and every pair of roots is joinable inside it, and
> suppose some critical point has `|c| ≤ 1 − 2/n`. Then two roots joinable inside
> `{|f| < 1}` satisfy `|z_a − c| + |z_b − c| < 2`, strictly, since the roots lie in
> the open disk.

That is the **length half** of #1041 settled for those configurations. What it does
not give is a path: the budget is a target, and whether some curve inside
`{|f| < 1}` achieves it is untouched. Both hypotheses are real restrictions — the
first fails as soon as one critical value reaches 1, and the second fails for
instance at `(z−1)³(z−9/10)`, whose critical points sit at `1` and `37/40`, both
past `1 − 2/4`.

**Within this superseded proof, the constant and the method threshold are both
sharp, and for different reasons.**

* `zⁿ − 1` has its only critical point at `c = 0`, well inside the covered region,
  with every root at distance 1: `d₁ + d₂ = 2`. So the constant 2 cannot be lowered
  anywhere in the region.
* `(z+1)^{n−1}(z−1)` has its non-root critical point at exactly `c = 1 − 2/n`, with
  `d₁ = 2/n` and `d₂ = 2 − 2/n`: `d₁ + d₂ = 2`. So the threshold `1 − 2/n` sits
  exactly on an equality case, and the hypothesis cannot be relaxed by sharpening
  the estimate — a strictly larger region would have to prove something the
  argument's own extremal configuration saturates.

The threshold is also forced geometrically, not just by the estimate. Put `n−1`
roots at the antipode `−c/|c|` and solve `Σ 1/(zᵢ−c) = 0` for the last root: it
must sit at `z₀ = t + (1+t)/(n−1)` on the ray through `c`, and `|z₀| ≤ 1` is
precisely `t ≤ 1 − 2/n`. The same threshold appears a third time in the symmetric
family with `k` far roots at each of two conjugate boundary points: there
`δ = e²t/(k(e²−m²))`, and `δ = 1−t` with `e = 1+t` forces `t = 1 − 2/n` again.
Three independent routes to the same number is why the threshold is treated here
as structural rather than as an artifact of one estimate.

**Historical coverage statement.** This partial theorem was silent only on an
annulus of width `2/n`: `|c| ≤ 1/3` is covered at `n = 3`, `|c| ≤ 0.8` at
`n = 10`, `|c| ≤ 0.98` at `n = 100`. So the unproved part of B1 is a vanishing
fraction of the disk as the degree grows, and it is exactly the part where a
critical point sits so close to the boundary that Gauss–Lucas crowds the roots
around it.

## What the numerics add

Direct maximisation of `d₁ + d₂` over root configurations — exact arithmetic, no
grid, hill-climbing from the two structured families and from random starts.

Degrees 2 through 14, 140 restarts each, 320 hill-climb steps: **no configuration
exceeds 2, and the maximum is exactly `2.000000000000`.** Where a degree reports
`1.9999999` instead of `2.0` the limit is `np.roots` on a degenerate derivative,
not the mathematics — see the artifact note below.

The case split is confirmed by the search, and this is the part worth reading:

| case | max `d₁ + d₂` observed | status |
|---|---|---|
| `c` at the origin | **2.000000000** | proved (F1 alone) |
| two or more roots on the c-side | 1.999999987 | proved, `≤ 2√(1−t²)` |
| none on the c-side | 1.999999999 | proved, `≤ 2√(1−t²)` |
| exactly one root on the c-side | **2.000000000** | the case the theorem is for |

**Equality is observed only in the two cases the proof singles out.** The two
cases that close in a line never reach the bound; the case that needs the whole
argument is the only one that attains it.

The upper envelope of `d₁ + d₂` against `|c|`, bucketed, is sharper still:

| `\|c\|` bucket | 0.0 | 0.1 | 0.2 | 0.3 | 0.4 | 0.5 | 0.6 | 0.7 | 0.8 | 0.9 |
|---|---|---|---|---|---|---|---|---|---|---|
| max `d₁+d₂` | **2.000** | 1.995 | 1.951 | **2.000** | 1.985 | **2.000** | **2.000** | **2.000** | **2.000** | **2.000** |

A bucket reaches exactly 2 precisely when it contains `1 − 2/n` for some integer
`n ≤ 14`: `0` (n=2), `1/3` (n=3), `1/2` (n=4), `3/5` (n=5), `2/3, 5/7` (n=6,7),
`4/5` (n=10), `6/7` (n=14). The three buckets that fall short — `0.1`, `0.2`,
`0.4` — are exactly the ones containing no `1 − 2/n` at all, since those would
need `n = 2.2`, `n = 2.5`, `n = 3.3`. **A search told nothing about the threshold
reproduces it, degree by degree, as the locus where the bound is attained.**

Outside the proved region the largest value found is `1.999995269`, at `n = 3` with
`|c| = 0.333338` — the spike family sitting `5×10⁻⁶` past `1 − 2/3`, re-verified at
60 decimal digits. So the uncovered region approaches 2 only by approaching the
threshold from outside, and no interior equality was found there.

**Two exact checks that the arithmetic is doing what it claims.** Over random
configurations at every degree, the worst relative residual of (ID) is `2.7×10⁻¹⁵`
and of the discriminant identity `8.7×10⁻¹⁴`.

**Artifact note, recorded rather than smoothed away.** The search reported critical
points with `|c|` up to `1.067`, which Gauss–Lucas forbids. The cause is
`np.roots` on a derivative with a near-multiple root: for `zⁿ − rⁿ` the derivative
is `n z^{n−1}`, whose `n−1`-fold zero at the origin is computed with spread about
`ε^{1/(n−1)}` — `0.062` at `n = 14`, which is what is seen. The same effect is why
`zⁿ − 1` reports `d₁ + d₂ = 1.8813` at `n = 14` instead of 2. Both push the
statistic **down**, so they cost sensitivity in a search for a violation rather
than manufacturing one; every configuration where the overshoot appeared had
budget below `0.53`. A dedicated re-run with no near-degenerate configurations
sees overshoot `0.000000`.

## A guard that was right for the wrong reason

While reading the existing machinery for this lab, `polyline_upper_bound` in
[erdos1041_geodesic.py](../../../probes/erdos1041_geodesic.py) turned out to
certify nothing. Its docstring said the polylines were "exactly verified" and
TrueGeodesicLab's claim boundary repeated it, but the check sampled 4000 points
and accepted the segment if `|f| < 1` at each. `|f|` can exceed 1 strictly between
samples, and admitting such a segment turns a claimed *upper* bound on the
geodesic into a number that may sit *below* the truth — which is exactly the
direction that would manufacture a false witness under 2.

The fix is exact rather than finer. Restricted to a segment `z(t) = a + t(b−a)`,
`f` is a complex polynomial `P(t)` of degree `n`, so `|f|²` is the real polynomial
`Q = P·P̄` of degree `2n`, and its maximum on `[0,1]` is attained at an endpoint or
at a real root of `Q'`. Those are computed, not sampled.

Checked against the old routine on all eight published configurations: **every
bound is unchanged to six decimals.** Against 200,001-point sampling on 340 random
segments the certified maximum agrees to `5.5×10⁻¹¹` and the interior/exterior
verdict never differs. So no number in TrueGeodesicLab moves; what changes is that
its guard now holds for a reason.

## The existence half: the two-segment mechanism, measured hard

[AllStraightSegmentsCounterexampleComputationalLab.md](AllStraightSegmentsCounterexampleComputationalLab.md)
kills the direct chord exactly — every chord of `z³ − r³` with `r³ > 8/9` leaves
the lemniscate at its midpoint, by the integer inequality `9·99³ > 8·100³` — and
in the same breath opens the replacement: on that same cubic the broken line
`r → 0 → rω` has length `2r < 2` and stays inside, because `|f| = r³(1−s³)` on
each radial spoke. It closes by asking for **"the existence and metric budget of
such hubs"**. The theorem above is the budget half. This is the existence half.

The mechanism, taken exactly as proposed: connect two roots by their direct
chord, or by a broken line through the origin or through a critical point. Every
segment is admitted only when the **exact** maximum of `|f|` along it is below 1,
so a reported length is a genuine upper bound on the geodesic.

**The instrument reproduces the lab's algebra before being trusted with anything
new.** On `z³ − (99/100)³` it finds no admissible chord and gives the critical hub
at `1.98`, which is `2r = 99/50` to the digit. Because the answer is a minimum,
candidates are sorted by length and the first that certifies wins — that is exact
and skips the expensive check on everything longer, and it was verified against
brute force on 300 random configurations with **zero mismatches**.

**A spurious-hub fault, caught by asking why a critical hub beat the origin.**
The first run of this reported a ceiling that fell with degree — `1.9677` at
`n = 10` — carried by a "critical" hub. But the `n = 10` maximiser is exactly
`z¹⁰ − r¹⁰` (derivative `[10, 0, …, 0]` to `10⁻¹⁴`), whose only critical point is
the origin, so no critical hub can beat it. `np.roots` cannot resolve a multiple
root: the ninefold zero of `f'` came back as nine points on a circle of radius
`0.017`, which is `ε^{1/9}`, and those spurious points were being used as hubs.

That is the same error class once more, in its most dangerous direction yet. An
extra hub can only **lower** the cheapest connection, so it biases toward
*satisfying* the conjecture: a configuration whose genuine constructions all cost
2 or more could have been reported as fine. The repair detects a multiple critical
point by `f''` vanishing there — well-conditioned even where the location is not —
and replaces the cluster by its centroid, which recovers a multiple root to full
precision because the elementary symmetric sum is well-conditioned. Collapsing too
eagerly removes a candidate and raises the reported minimum, so the error that
remains is in the safe direction.

Note the asymmetry with `polyline_upper_bound`: there the same spurious hubs are
harmless and in fact sound, because that claim is only that *some* interior path
exists, and a certified broken line through any point is a genuine path. The
difference is the claim, not the arithmetic.

With the hub set corrected, 30 restarts and 600 hill-climb steps per degree
gave the same maximum cheapest connection, `1.999999998`, for every tested
degree `n = 2, 3, ..., 10`.

**Exactly `2r` with `r = 1 − 10⁻⁹`, the modulus cap, at every degree — and nothing
above it.** Every maximiser is the roots-of-unity family, identified by a minimum
chord of exactly `2 sin(π/n)`. So the worst case of the mechanism is the same
`zⁿ − rⁿ` that the sharpness theorem calls extremal, at every degree, and it costs
exactly `2r < 2`. The mechanism is tight precisely where the problem is tight.

### What happens on that family, exactly

Working it out rather than measuring it: the midpoint of two roots `k` steps apart
is `m = r cos(πk/n) e^{iπk/n}`, so `mⁿ = ±rⁿcosⁿ(πk/n)` and the adjacent chord
escapes iff

`rⁿ (1 + cosⁿ(π/n)) > 1`.

At `n = 3` that is `r³ > 8/9` — exactly the condition
[AllStraightSegmentsCounterexampleComputationalLab.md](AllStraightSegmentsCounterexampleComputationalLab.md)
proves by the integer inequality `9·99³ > 8·100³`. So their cubic is the `n = 3`
case of a family covering every degree. Measured at `r = 1 − 10⁻⁹`:

| n | interior chords | what carries the connection |
|---|---|---|
| 3, 5, 7, 9 | **none at all** | the origin hub, length `2r` |
| 4, 6, 8, 10 | only the diameter, length `2r` | the diameter, which passes through the critical point anyway |

For odd degree the statement is stronger than the cubic result: not merely the
adjacent chords but **every** chord leaves the lemniscate. For even degree the one
surviving chord is the diameter, which is the origin hub with its two spokes
collinear. Either way the cheapest connection is exactly `2r`, and the two-radius
broken line through the origin realises it at every degree.

### Why the obvious containment argument cannot work

`|z − zᵢ|` is convex along a segment, so its maximum sits at an endpoint, giving
the natural containment test

`sup_{[z_a,c]} |f| ≤ |z_a − c| · ∏_{i≠a} max(|z_a − zᵢ|, |c − zᵢ|)`.

On the radial spoke of `zⁿ − rⁿ` the true supremum is `rⁿ`, attained at the origin.
The majorant is not close:

| n | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 10 | 12 |
|---|---|---|---|---|---|---|---|---|---|
| majorant / truth | 2.000 | 3.000 | 4.000 | 5.000 | 6.000 | 9.296 | 13.657 | 26.180 | 44.785 |

The factor is exactly `n` for `n ≤ 6`, because `∏_{k=1}^{n−1} 2 sin(πk/n) = n` and
every `2 sin(πk/n) ≥ 1` in that range; beyond it the truncation at `max(·, r)`
makes it grow faster. Since the true value approaches 1 as `r → 1`, a test that
overshoots by a factor of `n` **can never certify the spoke on the extremal family
at any degree ≥ 2**. Containment is the hard half, and this rules out the first
thing one would try.

### Attacking absence directly

Maximising the cheapest connection is a poor way to hunt for a configuration with
**no** construction at all, because a configuration that has one cannot see
absence unless it is adjacent. So a separate search minimises the *count* of
certified constructions of length below 2 — candidates of length 2 or more being
irrelevant to #1041, pruning them makes the count reaching zero exactly a
counterexample rather than merely a sparse configuration.

| n | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| fewest surviving constructions | **1** | 3 | 2 | 8 | 10 | 30 |

Nothing reaches zero. The tightest case is a cubic with all three roots on the
modulus cap, at angles `0.2623`, `0.5602`, `0.9397` of a full turn, where exactly
one construction survives:

| length | mechanism | max `\|f\|` on the path | |
|---|---|---|---|
| 1.610459 | chord | 1.029959 | fails |
| **1.692828** | **critical hub** | **0.954333** | **the sole survivor** |
| 1.697150 | chord | 1.095681 | fails |
| 1.796199 | critical hub | 1.001279 | fails by 0.13% |
| 1.858401 | chord | 1.182377 | fails |
| 2.000000 | origin hub | 1.000823 | fails by 0.08% |

The shape of this is worth stating, because it is not what "down to one option"
suggests. The **count** margin collapses to one, but the surviving path is not
itself close to failing: it has 4.6% of headroom in containment and sits 0.31
below the length bound. What is close to failing is everything *else* — two other
candidates miss by under a seventh of a percent. So the mechanism's fragility is
in how many routes work, not in how well the working route works.

Two instrument notes, both in the safe direction. Where a hub coincides with the
origin the same geometric path is counted twice, once under each name, so these
counts overstate the number of distinct paths — which makes reaching zero harder,
not easier. And reconstructing that cubic from six-decimal output pushed one root
to modulus `1.00000024`, outside the disk and so not an instance of the problem at
all; the table above is computed from the full-precision configuration.

> **Conjecture (two-segment mechanism).** For monic `f` with all roots in the open
> unit disk, some two roots are joined, inside `{|f| < 1}`, either by their direct
> chord or by a broken line through a critical point, of total length below 2.

This would settle #1041 outright, and it is a statement with no curves in it: a
finite search over root pairs and critical points, each candidate a two-segment
polyline. It is proved for `n = 2` and `n = 3`. The theorem above supplies the
length side of it at every degree for hubs with `|c| ≤ 1 − 2/n`; what it does not
supply is spoke containment, and the packet's quintic shows containment can fail
at a *prescribed* critical point. The conjecture asserts only that some hub works,
which is a strictly weaker and so far unrefuted demand.

## The descent path: containment is free, and what the budget theorem is really for

[InverseRayAggregateComputationalLab.md](InverseRayAggregateComputationalLab.md)
already makes the observation that reorganises this whole file. Along the curve of
constant `arg f` descending from a critical point, `|f|` falls monotonically from
`|f(c)| < 1` to 0, so the path lies inside `{|f| < 1}` **by construction**. Its
phrase is that both branches lie in the strict lemniscate "by their value-ray
parameterization".

That is the exact complement of the straight spoke. The spoke has free length
control and no containment — the section above shows the convexity majorant cannot
certify it at any degree. The descent path has free containment and no length
control. Every construction in this problem is one of the two, and the open
question is always the missing half.

For the descent path, then, the only question is length. Writing `L_c` for the
combined arc length of the two branches at an admissible simple critical point:

    MIN   min_c L_c < 2                     -- settles #1041 on its own, since the
                                               path is already contained
    AVG   sum_c L_c < 2 · (number of hubs)  -- the averaging mechanism that lab
                                               proposes, which implies MIN

**Instrument.** The arc lengths here come from `inverse_ray_aggregate_score` in
that lab's own checker rather than from a rival implementation, so the numbers are
comparable to its receipt: the balanced quintic scores `0.536025` against its
"about `0.536`". The integrator is adaptive — normalized aggregate, minimum edge
and maximum edge agree to six decimals across `flow_max_step` from `0.04` down to
`0.0025`, a sixteenfold range, on the quintic and on random configurations at
degrees 3, 5 and 8. That file is owned by a concurrent session; this probe imports
it and never writes to it.

### The budget theorem is the lower-bound skeleton of that construction

Arc length is at least straight-line distance, so at every hub

`L_c  ≥  |z_a − c| + |z_b − c|`  — the budget of the theorem above,

with equality exactly when both branches are straight. Checked on 598 hubs from
150 random configurations: **zero violations**, and on `z³ − r³` the ratio is
`1.000000000` — the branches there *are* the two radii, which is why that family
realises the bound exactly.

So the budget theorem is not a side result. It is the necessary condition for MIN:
if every hub had budget above 2, every arc would exceed 2 and MIN would fail. What
the theorem removes is the straight-line obstruction. What remains is the
**curvature inflation** `L_c / budget_c`, and the measurement of it is encouraging
in a specific way:

| budget bucket | 0.0 | 0.2 | 0.4 | 0.6 | 0.8 | 1.0 | 1.2 | 1.4 | 1.6 | 1.8 |
|---|---|---|---|---|---|---|---|---|---|---|
| mean inflation | 1.001 | 1.006 | 1.014 | 1.039 | 1.039 | 1.046 | 1.050 | 1.041 | 1.040 | 1.037 |
| max inflation | 1.023 | 1.147 | 1.230 | 1.355 | 1.287 | 1.352 | 1.363 | 1.250 | 1.122 | 1.121 |

Inflation **peaks in the middle and falls off at the dangerous end**. Where the
budget is small the branches curve freely and it does not matter; where the budget
approaches 2 the branches straighten, and on the extremal family they are exactly
straight. That is the behaviour a proof needs, and it is not obviously forced.

### The lemma that would finish it

The budget theorem gives a hub with budget **strictly** below 2, since the roots
lie in the open disk. MIN needs arc below 2 at some hub. Define, at a hub with
budget `< 2`,

`ρ  =  (2 − L_c) / (2 − budget_c)`.

If `ρ ≥ ρ₀ > 0` at the hub the budget theorem selects, then
`L_c ≤ 2 − ρ₀(2 − budget_c) < 2` and #1041 follows.

**Per hub this is false**, and the packet already knew the shape of why: 7 hubs out
of roughly 1400 sampled have budget below 2 and arc at or above 2, the balanced
quintic's long hub among them. But the statement is not about an arbitrary hub, and
at a selected one it looks quite different. Over 360 polynomials at degrees 3
through 7, half of them drawn with all roots above modulus `0.97`:

| hub selected by | ρ min | ρ median | ρ max |
|---|---|---|---|
| minimum budget | **0.9380** | 0.9998 | 1.0000 |
| minimum arc | **0.9380** | 0.9998 | 1.0000 |

Never near zero, and `ρ → 1` exactly where the budget approaches 2 — the extremal
family, where arc and budget coincide. The worst case in that sample is a cubic
with budget `1.6980` and arc `1.7167`.

**That is a random sample, which after this session's record is not evidence about
a floor.** Note first that `ρ ≤ 1` always, since arc `≥` budget; and `ρ > 0` is
exactly the statement `L_c < 2`. So a search that drives `ρ` down is searching for
a hub whose arc approaches 2 while its budget stays below it. Under adversarial
minimisation the floor does fall, and it has not converged: a deeper search reaches
`0.825` at `n = 3` and `0.525` at `n = 4`, while a shallower one over degrees 3 to 6
bottoms out at `0.912, 0.814, 0.804, 0.903`. The random sample's `0.938` was the
least informative of the three. **No floor here should be quoted as a constant**;
what is established is only that `ρ` stayed positive in every configuration
visited, and that more search buys a lower number.

Two things follow, and the second is the one that matters. The floor quoted from a
random sample is worthless — the same lesson as the rest of this file. And a
falling floor at the **minimum-budget** hub does **not** refute MIN: MIN is about
the minimum-**arc** hub, and choosing the hub by budget is once again selecting by
the wrong quantity. What a low `ρ` there says is that the budget theorem's hub is
not the right hub to run the finishing lemma at, not that no hub works.

### The flow in closed form, and a bound that had to be tried

Writing `S = f'/f = Σᵢ 1/(z − zᵢ)`, the branch equation `f'(z) z' = e^{iθ}` becomes

`z'(t) = 1 / (t · S(z))`,

with two exact companions along the branch: `∏ᵢ |z(t) − zᵢ| = t`, and
`L = ∫₀^T dt / |f'(z(t))|` where `T = |f(c)|`.

On both families where the integral can be done by hand it gives the same answer.
For `zⁿ − rⁿ` at `c = 0`: the branch solves `zⁿ = rⁿ − t`, so
`|f'| = n(T − t)^{(n−1)/n}` and

`L = ∫₀^T dt / (n (T−t)^{(n−1)/n}) = T^{1/n} = r`.

For `z² − a²`: `L = a = T^{1/2}`. Both are exactly `T^{1/n}`, and both are the
extremal families of this problem.

That is worth a conjecture, because it would finish the whole thing:

> If every descent branch satisfied `L ≤ |f(c)|^{1/n}`, then at any critical point
> with `|f(c)| < 1` — one exists by the discriminant/Fekete argument at the top of
> this lab — the two branches would total below 2, and the path is already
> contained. #1041 would follow.

**It is false.** Over 2230 branches at degrees 2 to 8, 150 violate it, the worst by
a factor of `1.678` at `n = 8` with `|f(c)| = 0.00347`.

### Why no bound from the critical value alone can work

The refutation has a clean structural reason rather than a numerical one.
`|f(c)| = ∏ᵢ |c − zᵢ|` is a **symmetric** function of the distances from `c` to all
the roots, so it does force the *nearest* root to lie within `|f(c)|^{1/n}`. But the
branch endpoint is not the nearest root — it is whichever root the merge topology
sends the branch to, and the branch is free to run straight past a near root to a
far one. Split the same 2230 branches by whether they land on the nearest root:

| branch lands on | count | ratio `L / |f(c)|^{1/n}` |
|---|---|---|
| the nearest root | — | median **1.000** |
| some other root | — | median **2.523**, max **5.95** |

The worst violator reaches a root at distance `0.802` while a root sits at `0.135`
— `5.95` times closer. A quantity blind to which root the branch reaches cannot
bound how far it travels.

**The salvaged conditional is very nearly true, and still false.** Restricting to
branches that do land on the nearest root, over a fresh sample: `1629` satisfy
`L ≤ |f(c)|^{1/n}` and **one** violates it, at ratio `1.038`; among branches landing
elsewhere, `13.1%` violate. So the nearest-root condition accounts for 215 of the
216 failures and still does not close.

What this rules out is a family, not a formula: **any branch-length bound whose
right-hand side is a symmetric function of the root positions relative to `c`.** A
working bound has to see the merge topology. That is a genuine constraint on the
remaining routes, and it is why the length half of the descent construction is
harder than the containment half is easy.

### The cone bound cannot be sharpened to the arc bound

`check_erdos1041_turning_inflation.py` uses `L ≤ chord / cos(α/2)` with
`α = TV(arg f')`. That looks improvable: if the turning were **monotone**, the
circular arc gives `L / chord = (α/2)/sin(α/2)`, which at `α = 112°` is `1.178`
against the cone's `1.789`. And the turning really is close to monotone — over 60
branches at the least-critical-value hub, `TV / |net turning|` has median and 90th
percentile both `1.0000` and maximum `1.1979`.

**The improvement does not exist.** The extremal monotone-turning curve is not the
circular arc but the **vee**: two straight segments meeting at angle `π − α` turn
monotonically, all at one point, and realise `L / chord = 1/cos(α/2)` exactly. So
the cone bound is already sharp for the class and monotonicity buys nothing.
Measured accordingly: the arc bound is violated by `81.7%` of branches, with median
actual inflation `1.0009` against a median arc bound of `1.0010` — they sit on top
of each other and the actual routinely edges past.

Recorded so the next reader does not try it. Two incidental facts from the same
sweep, both of which may be useful elsewhere. The branch's signed curvature is

`κ = |f'| · Im( e^{iθ} f'' / f'² )`,

verified against finite differences to a relative `5.8×10⁻⁷` with 100% sign
agreement; on `zⁿ − rⁿ` at `c = 0` the quantity `f''/f'² = (n−1)/(n zⁿ)` is real
along the branch because `zⁿ = rⁿ − t` and `θ = π`, so `κ ≡ 0` — that is the exact
reason those branches are straight. And `κ` does change sign on `30 of 60` branches,
so the turning is not literally monotone; the reversals are just small enough that
`TV` and `|net|` agree to four decimals.

### Maximising MIN and AVG directly

Both statements, taken as objectives and pushed:

| n | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|
| max of `min_c L_c` (MIN) | **1.999999986** | 1.852321 | 1.634226 | 1.592300 | — |
| max normalized aggregate (AVG) | **0.999999994** | 0.904177 | 0.822727 | 0.746591 | 0.680409 |

Neither is refuted. Both are **tight at `n = 3` and only there**: the extremal cubic
gives `min_c L_c = 2r` and aggregate `= r`, each sitting against its threshold from
below, and both ceilings fall monotonically with degree afterwards. That is the same
shape as every other formulation in this file.

The AVG row is worth separating out, because it is an adversarial strengthening of
somebody else's result rather than a new one of mine. The inverse-ray lab tested the
aggregate on three *deterministic* families and found them all below threshold, with
the near-regular cubic approaching it. Maximising the aggregate directly over root
configurations — the test it names as the one-way outcome it wants — still does not
reach 1. Its mechanism survives a harder attack than it was given.

### What controls the excess: the variation of arg f'

The excess length is not an opaque quantity. Along the descent curve
`f(z(t)) = t e^{iθ}`, differentiating gives `f'(z) z'(t) = e^{iθ}`, so

`|z'| = 1/|f'(z)|`   and   `arg z' = θ − arg f'(z)`.

The branch's tangent direction is therefore `θ − arg f'` and nothing else. If
`arg f'` varies by at most `α` along a branch, every tangent lies within `α/2` of
the mean direction, so the chord is at least `cos(α/2)` times the length:

`inflation  ≤  1 / cos(α/2)`,  `α` = total variation of `arg f'` along the branch.

Checked on random configurations at degrees 3 to 6, the bound holds in every case,
and it is the right mechanism rather than a coincidence: `α = 3.8°, 5.1°, 6.4°`
give inflations `1.00018, 1.00034, 1.00052`, while `α = 112°` gives `1.091`.

**On the extremal family the variation is exactly zero, by hand.** For
`f = zⁿ − rⁿ` at `c = 0` the descent solves `zⁿ = rⁿ − t` with `rⁿ − t` real and
positive, so `z` traces the radius `[0, r ω_k]` exactly; and
`arg f' = arg(n z^{n−1}) = (n−1) arg ω_k` is constant along it. So `α = 0`, the
branch is straight, and the inflation is exactly 1.

That is the whole reason the inflation collapses at the dangerous end of the budget
range, and it converts the finishing lemma into a statement with no arc lengths in
it at all:

> **Reformulation.** It suffices to bound the total variation of `arg f'` along the
> two descending branches at the hub of minimum budget, by a quantity that vanishes
> as the budget approaches 2.

`arg f'` is harmonic-conjugate data of `log|f'|`, and `f'` is a monic polynomial of
degree `n − 1` whose roots are the other critical points, so this is a statement
about how the *other* critical points are arranged relative to the branch — which
is at least the kind of object the Gauss–Lucas identity at the top of this lab
already speaks about.

> **Finishing lemma, in the form that would bridge to the budget theorem.** There
> is an absolute `ρ₀ > 0` with `2 − L_c ≥ ρ₀ (2 − budget_c)` at the hub of minimum
> budget.
>
> With the budget theorem this would give `L_c < 2` there, and the descent path is
> already contained, so it would settle #1041 wherever the theorem applies.

**As stated at that hub the bridge is weakening, and should be treated as
doubtful.** The adversarial floor falls with degree rather than settling, so `ρ₀`
absolute is not what the data suggests. The honest position is that the bridge
from the budget theorem to MIN is unproved and looks harder than the random sample
implied, while MIN itself — measured directly, at the minimum-arc hub, which is
the quantity #1041 actually needs — is untouched by any of it.

Equivalently: the curvature excess of the descending branches at the best hub is at
most a fixed fraction of the budget's own slack below 2. Both quantities vanish
together on `zⁿ − rⁿ` as `r → 1`, which is exactly the zero-slack behaviour the
sharpness theorem demands of any proof — and the reason this formulation is not
obviously circular is that the two vanish at the *same rate*, `ρ → 1`, rather than
one outrunning the other.

## Why the least-critical-value hub is the one that survives

The selector table above is empirical. There is a structural reason behind it, and
it is a theorem rather than a measurement.

> **Univalence lemma.** Let `f` be squarefree with `T* = minₖ |f(cₖ)| > 0`. Then
> `{|f| < T*}` has exactly `n` components, each containing exactly one root, and `f`
> is **univalent** on each of them. At the hub `c*` achieving `T*`, the two merging
> components are two such conformal cells.

*Proof.* The number of components of `{|f| < t}` is `n` minus the number of critical
points with `|f(c)| < t`. Below `T*` there are none, so there are `n` components;
each contains at least one root and there are `n` roots, so exactly one each, and it
is simple because a repeated root would itself be a critical point of value 0. A
component containing one simple root is a proper degree-one image of `D(0,T*)`, that
is, univalent. ∎

**No other hub has this property.** Above the first critical value the components
have merged and carry two or more roots, so `f` there is a genuine branched cover.
The least-critical-value hub is the unique one whose two descending branches both
run inside domains where `f` is conformal — which is exactly the structure
[CubicCriticalHub.md](CubicCriticalHub.md) exploits at `n = 3`, and the reason that
choice is not a degree-three convenience.

Numerically: over random configurations the component count below `T*` comes out at
`n` with one root each. One case out of eight disagreed at grid resolution `4.6×10⁻³`
with `T* = 4.9×10⁻⁴`; refining to `2000` and `4000` moved the count from `3` to `4`
toward the predicted `5`, while the smallest cell there has radius `1.3×10⁻⁴` —
still below the finest cell tried. Resolution, confirmed by refinement rather than
asserted.

**A quantitative corollary, and how loose it is.** Writing `ψ = (f|_Ω)^{-1}` with
`ψ(0) = z_a` and `ψ'(0) = 1/f'(z_a)`, Koebe's one-quarter theorem puts a disk of
radius `T*/(4|f'(z_a)|)` inside the cell, while Pólya's inequality bounds the area of
`{|f| ≤ T*}`, hence of any one cell, by `π (T*)^{2/n}`. Comparing areas:

`|f'(z_a)| ≥ (T*)^{(n−1)/n} / 4`.

Zero violations over 14 927 (root, polynomial) pairs at degrees 2 to 8 — and the
tightest ratio is `7.76`, so it is loose by nearly an order of magnitude. The
extremal family says why: on `zⁿ − rⁿ` the true relation is
`|f'(z_a)| = n (T*)^{(n−1)/n}` exactly, so the sharp constant is `n`, not `1/4`. The
`1/4` is Koebe's, and Koebe is attained by the Koebe function, which is nothing like
a lemniscate cell. Recorded as a valid but weak corollary rather than a tool.

## A conditional theorem: #1041 at the first-merge hub

The univalence lemma turns out to buy more than an explanation of the selector
table. Everything in this file assembles at `c*`, the hub of least critical value.

**The chain.**

1. *(proved)* Below `T* = min_k |f(c_k)|` there are no critical points, so
   `{|f| < T*}` has `n` components, one simple root each, and `f` is univalent on
   every one. The two cells merging at `c*` are conformal.
2. *(measured, 600/600)* The two roots the branches at `c*` reach are the two
   **nearest** roots to `c*`.
3. **FALSE.  Refuted 2026-08-23 on this file's own stored witnesses.** The claim
   was that each spoke `[z_a, c*]` stays inside `{|f| < 1}`; adversarial
   maximisation of the spoke maximum reached `0.986769` at `n = 3` and fell with
   degree — `0.884`, `0.696`, `0.363`, `0.458` — never 1. That search missed the
   exact witnesses. See "Claim 3 is false" below.
4. *(proved)* `T* < 1`, from `∏_k |f(c_k)| = ∏_{i<j}|zᵢ−zⱼ|²/nⁿ ≤ 1` by Fekete,
   strict for roots in the open disk.
5. *(proved)* The budget theorem: the two nearest roots to **every** critical
   point `c` satisfy `d₁ + d₂ ≤ 2`, with no restriction on `|c|`, and strictly
   `< 2` when the roots lie in the open disk.  This step was written against the
   superseded `|c| ≤ 1 − 2/n` form; see "B1 holds globally" at the top of this
   file.  Strictness: with roots in the open disk `P > 0`, so `n < (1−t²)S`, and
   the `δ + e = 2` boundary case closes by the same `x + (n−1)/x ≤ n` step.

By 3 and 4 the broken line `z_a → c* → z_b` would lie inside `{|f| < 1}`, touching
`|f| = T*` only at `c*` itself, and by 2 and 5 its length would be below 2. **The
chain does not close: step 3 is false.**

> **Retracted, 2026-08-23.** The conditional theorem as stated — "assume 2 and 3,
> then Erdős #1041 holds for every squarefree `f` with `|c*| ≤ 1 − 2/n`" — is
> withdrawn.  Step 5's hypothesis was already superseded and can simply be
> dropped, which would have *widened* the statement; but step 3 is refuted at
> this file's own stored witnesses, so the construction fails outright.

## Claim 3 is false at the stored degree-6 and degree-9 witnesses

`StraightSpokeHubCriterionLab.md` §3 and §5 already record that the
contained-spoke objective restricted to `c*` is **infinite** — fewer than two
contained spokes at `c*` — at degrees 6, 8, 9 and 12, and store the degree-6 and
degree-9 configurations as exact IEEE-754 hexadecimal literals precisely because
the margins are near `1e-5` and do not survive decimal rounding.

Re-reading those exact witnesses at 60 decimal digits and measuring `|f|` on the
segments from `c*` to its two nearest roots:

| degree | `T* = |f(c*)|` | `d₁+d₂` at `c*` | worst spoke `max |f|` | at `t` |
|---|---|---|---|---|
| 6 | `0.99995098599675816247` | `1.71657242316568` | **`1.0000093332434161438`** | `0.87625888` |
| 9 | `0.99994148349944226776` | `1.49778265439909` | **`1.0000103851845920825`** | `0.80548221` |

Both exceed 1, so at each witness a nearest-root spoke **leaves the target
lemniscate** and the broken line is not contained.  Note what does *not* fail:
`d₁ + d₂` is `1.717` and `1.498`, comfortably inside the budget theorem.  The
length half is fine; **containment is what breaks**, which is the packet's
existing "curvature is forced" conclusion arriving again by a new route.

The guard is
[`scripts/check_erdos1041_first_merge_hub_claims.py`](scripts/check_erdos1041_first_merge_hub_claims.py);
it reads the stored witnesses through the existing verifier module and exits
non-zero if they ever stop refuting claim 3.

**Why the adversarial attack missed it.** The attack on claim 3 topped out at
`0.986769` and fell with degree, which reads as comfortable survival.  The real
violations sit at `1.0000093` and `1.0000104` — excesses of about `9e-6` and
`1e-5`, in configurations with max root modulus `0.99999985`.  A float search
maximising the spoke maximum does not find a `1e-5` bulge in a `1e-7`-thin corner
of root space.  This is the sixth entry in this file's own list of occasions when
a clean search meant nothing, and the first where the counterexample was already
sitting in the adjacent file.

**A near-miss worth recording rather than rounding.** The spoke maximum looks like
it might be *exactly* `T*`, which would say `|f|` is monotone along the spoke and the
cell is starlike in that direction — a much prettier statement than "below 1". Over
1000 spokes the ratio to `T*` reads `1.000000000` to nine decimals with none above.
But the ratio is `≥ 1` identically, since `|f(c*)| = T*` puts the endpoint at `T*`,
so maximising it lands on its own lower bound and proves nothing by itself. At full
precision the adversarial maximiser returns excesses of `1.1e-11`, `7.8e-12` and
`2.6e-8` at `n = 3, 4, 5`. The last is three orders above the others, which is
neither clean float noise nor a convincing bulge. **Left unresolved at this
precision**, and the chain above deliberately uses only the operational form, which
does not depend on it.

**What actually survives.** Two things, and they are worth keeping separate from
the retraction:

* Step 5 is now *stronger* than the chain used. The budget theorem holds at every
  critical point with no `|c|` restriction and strictly below 2 on the open disk,
  so the `248 of 600` scope limitation recorded here earlier is gone. Any future
  hub argument inherits `d₁ + d₂ < 2` for free.
* Step 1 is untouched: below `T*` there are no critical points, the `n` cells are
  conformal, and `f` is univalent on each. The univalence lemma is not what failed.

**What is dead.** Straight spokes at `c*`, in every selector form. Section 5 of
`StraightSpokeHubCriterionLab.md` had already concluded that "no rule of the form
'pick the hub by critical value, then take the merging or the nearest pair' can
work", and the degree-6 and degree-9 witnesses above are that conclusion made
quantitative at the nearest pair specifically. Claim 2 — merge pair equals nearest
pair — is now moot for this construction, since the construction fails even when
the pair *is* the nearest pair; it remains unattacked and should not be leaned on
for anything else.

**Method note, sixth entry.** The pattern in this file is now unmistakable: every
time a hub statement has been supported by adversarial maximisation of its own
objective and the supremum came back pinned just below the threshold — `1.9999997`
against 2, `0.9868` against 1 — the statement has been false and the witness has
been found by a differently-seeded search or by an exact stored configuration. A
pinned supremum should from now on be read as evidence that the search is in one
basin, not as evidence for the claim. Check any new hub claim against the stored
`QC_REFUTATION_WITNESSES` before writing it down.

## Where this meets the degree-three theorem

[CubicCriticalHub.md](CubicCriticalHub.md) proves the cubic case of #1041 through
a critical hub, selecting the critical point of **smaller critical-value
modulus** and getting both the metric scale and straight-spoke containment from
it. That is the same hub family this lab measures, so the two lines meet, and
the meeting point is informative in one specific way.

**I previously claimed here that the selector does not extend, on the strength of
an `n = 4` hub with budget `2.0068`. That witness was a branch-tracking error and
the claim is withdrawn.** The correct values at that hub are budget `1.434839` and
arc `1.477065`, comfortably under the target.

The evidence now runs the other way, and the right test is not a random sample.
Five canonical rules, each measured by the combined branch length at the hub it
picks — first over 400 random polynomials at degrees 3 to 8, then under adversarial
maximisation of exactly that quantity:

| rule | worst on random sample | worst under attack | verdict |
|---|---|---|---|
| smallest `\|f(c)\|` | 1.682309 | **1.943820** | survives |
| largest `\|f''(c)\|` (sharpest saddle) | 1.871489 | **2.163302** | **refuted at every degree 3-5** |
| largest `\|f(c)\|` below 1 | 2.065079 | — | refuted on the sample already |
| critical point nearest 0 | 2.065079 | — | refuted on the sample already |
| smallest straight budget | 1.682309 | — | ties the oracle on the sample |

The sharpest-saddle row is the lesson again in miniature: clean at `1.871` on the
random sample, over the line at `2.100`, `2.090`, `2.163` for `n = 3, 4, 5` once the
search is pointed at it. A clean sample is not evidence in this problem.

The least-critical-value rule is the one that survives both. Under attack its worst
is `1.943820` at `n = 3`, falling with degree — `1.567`, `1.351`, `1.010` at
`n = 4, 5, 6` — against the sharpest-saddle rule's `2.100`, `2.090`, `2.163`,
`1.998`. So `CubicCriticalHub.md`'s selector looks like a plausible
degree-general rule rather than a degree-three accident, which is a considerably
more useful thing to be able to say about it than what I had written here before.

## (F) attacked adversarially, and why its zero is provable

[CriticalTreeLengthCharge.md](CriticalTreeLengthCharge.md) calls the componentwise
charge lemma

`Σ_{e⊂C} (D_e + K_e) ≥ 0`   (F)

"the smallest topology-aligned theorem still standing", and records that
**"Deterministic component grouping has not falsified (F)"**. Deterministic. Its
verifier
[`check_erdos1041_invariant_branch_length.py`](scripts/check_erdos1041_invariant_branch_length.py)
computes exactly the right quantity — `component_charge_rows → normalized_charge`,
with receipt `minimum_normalized_component_charge = 0.011149754772821974` and
`negative_component_charges = 0` — but only through `sampled_rows` at 110
configurations per degree, and its CLI exposes only `--output` and `--print-only`.
There is no adversarial mode.

By this corpus's own standard that is the weakest link in the priority-1 producer.
`negative_results` entry 19 says a pinned adversarial supremum is not evidence; this
file records six occasions where a clean sample meant nothing. Sampling-only support
is weaker than either.

Minimising `normalized_charge` directly — reusing that module's own
`circumcircle / hub_rows / tangent_support_terms / component_charge_rows` pipeline
rather than a rival implementation, so the number is the one its receipt reports:

| n | 3 | 4 | 5 |
|---|---|---|---|
| adversarial min normalized charge | `5.4×10⁻⁹` | `2.2×10⁻⁶` | `3.5×10⁻⁶` |

All non-negative, and all attained at the equality family rather than at some
unexplained corner.

**The zero is provable, not measured.** On `zⁿ − rⁿ` every hub-edge has `L(e) = 2r`
and the circumradius is `R = r`, so `2R − L(e) = 0` identically; by the exact
identity `2R − L(e) = D_e + K_e` that forces `D_e + K_e = 0` edge by edge, hence a
component sum of exactly zero. The same holds for monic quadratics, where `c` is the
midpoint and `L = |z₁ − z₂| = 2R`. So (F) is sharp, its infimum is `0`, and the
infimum is attained on the same affine models of `zⁿ − 1` that every other
formulation in this problem is tight on.

That distinction is the one the verifier's own docstring draws, and it cuts the
other way from the six false alarms recorded above: a supremum pinned just below a
threshold for no reason is worthless, whereas a bound attained by an identifiable
equality family is a different and much stronger situation. (F) now sits in the
second category with adversarial rather than sampled evidence behind it.

## Degree five: the MEC falsifier does not reach the critical hub

The bounded-degree ladder stands at four. Degree three is
[CubicCriticalHub.md](CubicCriticalHub.md); degree four is Pendyala,
[arXiv:2606.24875](../../../../annexes/arxiv-2606-24875-erdos1041-quartic-lemniscate-path/),
whose proof is exactly the two-segment mechanism — a chord when some pair is within
distance 1, and otherwise two radial arms from the origin, supplied by his
four-point radial lemma. The claim ceiling eliminates straight critical-hub paths
only **from degree six**, and `QC_REFUTATION_WITNESSES` holds only degrees 6 and 9.
So degree five is the last rung where the polygonal mechanism can still work.

[AdaptiveMecDichotomyLab.md](AdaptiveMecDichotomyLab.md) is the strongest thing
standing in its way. It builds an exact rational quintic — five roots
`z_k = r·u(s_k)` on `|z| = r = 9999/10000`, with `u` the rational unit-circle
parametrisation at `s = 0, 48031/76394, 347397/99299, −203651/55446, −67203/94835`
— and proves at fourteen rational waypoints that **no root chord is safe and at most
one radial arm through the minimum-enclosing-disk centre is safe**. That closes the
direct all-degree extension of the quartic proof, and the lab names the surviving
front as "a polynomial-adapted critical or curved hub".

**It does not reach the critical hub.** Running the certified two-segment check on
that exact configuration reproduces both of its claims — no safe chord, exactly one
safe radial arm, at root index 0 — and then finds:

| critical hub | `\|f(c)\|` | safe spokes to roots |
|---|---|---|
| `0.407806 + 0.325657i` | 0.956420 | **0, 1** |
| `−0.534407 + 0.027414i` | 0.964767 | **2, 3** |
| `0.257620 − 0.321199i` | 0.990677 | **0, 1, 4** |
| `−0.087914 − 0.048449i` | 1.001340 | none — inadmissible |

Three of the four critical points carry two or more safe spokes, and the cheapest
certified two-segment connection is **1.218210**, through a critical hub, against a
target of 2. The reproduction of their two exact claims is the validation that the
instrument is reading the same configuration they are.

So the witness that kills chord-plus-MEC-centre leaves the critical-hub mechanism
untouched on the very configuration built to be hardest for it — which is what that
lab predicted and had not measured. Degree five remains the live rung, and the
mechanism to prove it with is the critical hub, not the origin.

## Drop the criterion: test spoke containment exactly

[GeneralSpokeIdentity.md](GeneralSpokeIdentity.md) proves the identity

`G(tw) = (1 − t²) − t²(1 − t) Q(t)`

at every degree, and derives the sufficient criterion (SC): `(1 − t)|Q(t)| ≤ 1` on
`[0,1]` puts the whole spoke inside. It then records SC failing at `552` of `24540`
minimal-hub configurations at `n = 4` and `128` of `8098` at `n = 5`, while noting
that at the ones examined directly **two spokes were still contained** — SC is lossy
"by roughly 10 percent at the margin".

SC discards two separate margins, and both are recoverable.

* **Phase.** It applies `|A − B| ≤ |A| + |B|` to the identity, throwing away
  `Re Q` entirely. Exactly,
  `|G(tw)|² = (1−t²)² − 2(1−t²)t²(1−t)·Re Q + t⁴(1−t)²|Q|²`,
  and the middle term helps whenever `Re Q > 0`.
* **Threshold.** That note says "it suffices to keep `|G| ≤ 1`", but the target is
  `|f| < 1`, which after the normalisation is `|G| < 1/T` with `T = |f(c)| < 1`.
  The whole factor `1/T > 1` is discarded.

Neither needs a sharper criterion, because containment is directly computable:
`|G|²` restricted to the spoke `[0, w]` is a real polynomial of degree `2n`, so its
maximum is the larger of its endpoint values and its critical values. Test
`max_{t∈[0,1]} |G(tw)| ≤ 1/T` and there is no criterion loss at all.

**Result.** Over 1200 random configurations at degrees 3 to 6, taking the
minimal-critical-value hub, every one has two exactly-contained spokes — zero
failures — with worst total spoke length `1.450080` against a target of 2.

**Corrected immediately below: that random sample was not the right test, and a
near-Fekete one refutes the critical-hub-only form at degree five.**

**And it reproduces the known boundary rather than overrunning it.** On the stored
`QC_REFUTATION_WITNESSES` at degrees 6 and 9, which
[StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md) §3 exhibits as
configurations where no admissible hub carries two contained spokes, the exact test
finds **exactly one contained spoke at every admissible hub**, never two, at both.
So the mechanism genuinely dies at degree six, now confirmed with the exact criterion
rather than the lossy one.

**What this settles about the open question in that note.** It asks: "at the minimal
critical-value hub, what forces a *second root* of the normalised polynomial into the
closed unit disk?" On the evidence here that is the wrong quantity. `|wᵢ| ≤ 1` is not
what is needed — the note's own correction already observed the length condition is
`|w₁| + |w₂| ≤ 2` — and what is needed is a second *spoke* whose exact maximum clears
`1/T`. That second spoke is present in every configuration sampled up to degree six
and absent at exactly the pinned witnesses where the mechanism is known to fail.

### Correction: at degree five the critical hub alone is not enough

Re-running the same exact test at `n = 5` with two thirds of the seeds jittered off
the fifth roots of unity — the regime
[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) identifies as the hard one —
gives **1 failure in 1500**, worst passing two-spoke total `1.995354852`. The random
sample above missed it, which after this file's record is exactly what a random
sample should be expected to do; the mistake was committing the claim before running
the seeding this corpus already knows is the hard one.

The witness is a `10⁻⁵` angular perturbation of the fifth roots of unity at modulus
`1 − 10⁻⁹`, angles `0.99998979, 0.2, 0.4, 0.6, 0.8` of a turn. Its four critical
points sit at `|c| ≈ 0.05` with `|f''| ≈ 3×10⁻³` — the spread of the 4-fold critical
point that `z⁵ − r⁵` has at the origin — and **no critical hub carries two contained
spokes**: two have `|f(c)| > 1` and are inadmissible, and the other two contain
exactly one spoke each. What saves the configuration is the **origin**, which is not
a critical point here, giving a certified two-segment path of length `1.999999998`.

So the honest degree-five statement needs both hubs, and that is a sharper thing to
know than the version it replaces:

> For every monic quintic with roots in the open unit disk, some two roots are joined
> inside `{|f| < 1}` by their chord, or by a broken line through the **origin**, or by
> one through a **critical point**, of total length below 2.

Neither hub suffices alone at degree five, and the two failure modes are disjoint.
The exact rational MEC falsifier of
[AdaptiveMecDichotomyLab.md](AdaptiveMecDichotomyLab.md) kills chord-plus-origin and
is rescued by a critical hub at `1.218210`; this near-Fekete quintic kills the
critical hubs and is rescued by the origin at `1.999999998`. Pendyala's quartic proof
uses the origin route; the corpus's surviving front is the critical route; degree five
appears to need the union of the two.

## Claim boundary

Exact, with proof: the identity (ID) and its corollaries (STAR) and (NEAR); the
discriminant expression for the product of critical values; the theorem that
`d₁ + d₂ ≤ 2` at **every** critical point, with no restriction on `|c|`, together
with both equality families. The EHP existence argument is assembled from
classical facts and is not claimed as new. The EHP existence datum is source-pinned
to the primary PDF and exact Problem 5 locator above; that source does not
certify this lab's derivation or equality interpretation.

The `|c| ≤ 1 − 2/n` restriction was removed on 2026-08-23; see the "B1 holds
globally" section above and [GlobalCriticalTwoNearestBudget.md](GlobalCriticalTwoNearestBudget.md)
for the ordinary proof, whose algebraic core is checked in
`CriticalTwoRootProximity.lean` as `two_add_le_two_of_disk_inverse_balance`.
This paragraph previously listed the global form as conjectural; that was stale
against the same file's own result section.

Conjectural: B3′, the component budget, which coincides with B1
whenever every critical value is below 1 and needs the merge tree otherwise; the
two-segment mechanism, measured hard and unrefuted but proved only at `n = 2` and
`n = 3`; and MIN and AVG for the descent path, both unrefuted under direct
maximisation and both tight at the extremal cubic.

Explicitly NOT established: any floor for `ρ`. The adversarial minimum keeps
falling with search depth, so the bridge from the budget theorem to MIN via the
minimum-budget hub is a doubtful route, not a result.

Exact, and new here as far as this lab can tell: the adjacent-chord escape
condition `rⁿ(1 + cosⁿ(π/n)) > 1` for `zⁿ − rⁿ`, which reduces at `n = 3` to the
`r³ > 8/9` proved in the all-straight-segments lab; and the fact that the
convexity majorant overshoots the true supremum on that family's radial spoke by a
factor of exactly `n` for `n ≤ 6`.

**Withdrawn, not refuted:** the merge-pair budget "counterexamples" and the claim
that the least-critical-value selector fails. Both rested on a descent of mine that
mistracked branch identities; three independent instruments agree against it. The
retractions are recorded above rather than deleted, because the failure mode —
trusting a branch-identification routine that had already been observed returning an
impossible answer — is the most expensive mistake in this file.

Not addressed at all: **realisability.** A budget is a length target, not a path.
Even a proof of B3′ would leave the other half of #1041 — that some path inside
`{|f| < 1}` actually achieves that length — and the packet's `Form A′` result
already shows the obvious straight route is not always available. #1041 is open,
and separately contested by a public manuscript claiming the full result, which
argues through Pólya's area-capacity inequality and a coarea/critical-value
analysis; this lab does not assess that manuscript and does not overlap its
method.

## Replay

```sh
# identities, families and the B1 maximisation - seconds
./repo-python formal_math/probes/erdos1041_critical_budget.py --max-n 9 --restarts 14 --steps 260 --modes b1_max

# the B1 stress with the case split and the threshold check - a few minutes
./repo-python formal_math/probes/erdos1041_critical_budget.py --max-n 3 --restarts 2 --steps 5 \
    --stress-trials 140 --stress-steps 320 --stress-max-n 14 --seed 99991

# the B3' lane - the disconnected case runs a constant-arg descent per hub, so keep it small
./repo-python formal_math/probes/erdos1041_critical_budget.py --max-n 8 --restarts 14 --steps 180 --modes b3_prime

# the two-segment mechanism - certified segments, early exit, fast
./repo-python formal_math/probes/erdos1041_critical_budget.py --max-n 10 --restarts 30 --steps 600 --modes two_segment

# the descent path: MIN and AVG maximised.  Each objective call integrates two
# branches per hub, so keep the degree range and step count modest.
./repo-python formal_math/probes/erdos1041_descent_length.py --min-n 3 --max-n 7 --restarts 5 --steps 40
```
