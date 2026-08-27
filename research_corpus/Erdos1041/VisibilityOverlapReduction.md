# Erdős 1041: one contained path is enough — a reduction to a one-root statement

Status: one proved lemma, one proved reduction, one exact equality theorem, one
exact correction to a stored witness, and one measured statement that the
reduction leaves open. 2026-08-24. **Erdős #1041 remains open** and nothing below
claims otherwise.

## 1. The shape of every negative result on file

`research_packet.json` records thirty-seven negative results. Eight of them are
independent mechanism eliminations, and they all have the *same* logical shape:

| where | what is exhibited |
|---|---|
| `negative_results` 5 | the nearest/second-nearest pair at a critical hub: one spoke escapes |
| `negative_results` 8 / `exact_results` `two_safe_origin_spokes_counterexample` | **at most one** safe root-to-origin spoke |
| `negative_results` 9 | four unsafe root spokes at the first-merge hub |
| `negative_results` 11 / `exact_results` `adaptive_mec_chord_or_radial_counterexample` | **at most one** safe MEC radial arm |
| `negative_results` 14 | **at most one** sublevel-contained spoke at every admissible critical point |
| `negative_results` 18 | degree 6 and degree 9: every admissible hub carries **exactly one** contained spoke |
| `negative_results` 26 / `exact_results` `straight_spoke_hub_criterion_separation` | **at most one** open-contained spoke, at every admissible hub |
| `negative_results` 37 | degree three, minimal: no safe chord and **at most one** safe radial arm |

Every one of them kills a mechanism that has to produce **two** good objects at
the same place at the same time: two contained spokes, two safe arms, a chord
plus a hub. Not one of them exhibits a configuration where *no* good object
exists. The wall the corpus keeps hitting is not "zero"; it is "one".

This note records a reduction under which **one is enough**.

## 2. The lemma

> **Lemma (visibility overlap).** Let `Ω ⊆ ℂ` be compact, let `Γ ⊆ Ω` be compact
> and **connected**, let `a_1, …, a_k ∈ Γ` with `k ≥ 2`, and put
>
> ```text
> S_j  =  { h ∈ Γ : h is joined to a_j by a path in Ω of length ≤ 1 }.
> ```
>
> If `S_1 ∪ … ∪ S_k = Γ`, then `S_i ∩ S_j ≠ ∅` for some `i ≠ j`; consequently
> two of the `a_j` are joined by a path in `Ω` of length `≤ 2`.

*Proof.* Each `S_j` is nonempty (`a_j ∈ S_j`, constant path). Each `S_j` is
closed in `Γ`: if `h_m → h` with paths `γ_m ⊆ Ω` from `h_m` to `a_j` of length
`≤ 1`, parametrise each by constant speed on `[0,1]`, so the `γ_m` are
`1`-Lipschitz into the compact set `Ω`; Arzelà–Ascoli gives a uniformly
convergent subsequence with limit `γ ⊆ Ω` from `h` to `a_j`, and length is lower
semicontinuous under uniform convergence, so `len γ ≤ liminf len γ_m ≤ 1`. Hence
`h ∈ S_j`.

Suppose the `S_j` were pairwise disjoint. Then each `S_j` equals
`Γ ∖ ⋃_{i≠j} S_i`, a complement of a finite union of closed sets, hence open in
`Γ`. So `Γ` is partitioned into `k ≥ 2` nonempty clopen sets, contradicting
connectedness. Therefore some `h ∈ S_i ∩ S_j` with `i ≠ j`, and concatenating
its two paths joins `a_i` to `a_j` inside `Ω` with length `≤ 1 + 1 = 2`. ∎

**The two roles of `Γ` and `Ω` are separate, and that is where the slack is.**
`Ω` is where the *paths* may run, so it should be taken as large as possible —
the whole component of `{|g| ≤ 1}`. `Γ` is where the *covering* must hold, so it
should be taken as small as possible — any compact connected subset carrying two
roots. Taking `Γ = Ω` is the crudest admissible choice. The cheapest is
`Γ = ` the pair of descending Newton branches from the minimising critical point
`c*` to the two roots it merges, which is a compact connected arc containing
exactly two roots (`exact_results::newton_descent_root_convex_hull_invariance`
supplies its existence and containment). This is the form used from §5c on.

Two things are worth saying plainly about this. It is elementary — there is no
analysis in it beyond Arzelà–Ascoli. And it is exactly the converse of the
corpus's obstruction: it consumes a hypothesis of the form *"every point has at
least one"* and returns a conclusion of the form *"some point has two"*. The
quantifier order is the whole content.

## 3. The reduction

> **Theorem (reduction).** Suppose the following holds for every monic `g` of
> degree `n ≥ 2` with all roots in the **closed** unit disk:
>
> ```text
> (COVER)   there is a level λ ∈ [μ(g), 1] such that every point of the
>           first-merge component of {|g| ≤ λ} lies within intrinsic distance 1
>           of a root of g inside that component,
> ```
>
> where `μ(g) = min{|g(c)| : g'(c) = 0}`. Then Erdős #1041 holds.

*Proof.* Let `f` be monic with all roots in the **open** unit disk. If `f` has a
repeated root the problem is trivial (two roots coincide; the constant path has
length `0` and `|f| = 0 < 1` there). So take the roots distinct. Let `D(z_c, R)`
be their minimum enclosing disk; `0 < R ≤ max_i |z_i| < 1`. Put

```text
g(w) := R^{-n} f(z_c + R w),
```

monic of degree `n`, all roots in `D̄`. Four standard facts about `g`:

* **(a) `μ(g) ≤ 1`.** `|Res(g,g')| = n^n ∏_c |g(c)|` over the `n−1` critical
  points with multiplicity, and `|Res(g,g')| = |disc(g)| = ∏_{i<j}|w_i−w_j|^2`.
  Fekete's bound for the closed unit disk gives `∏_{i<j}|w_i−w_j|^2 ≤ n^n`, so
  `∏_c |g(c)| ≤ 1` and hence `μ^{n−1} ≤ 1`. (This is the sandwich already
  recorded at `negative_results` entry 23; no novelty is claimed for it.)
* **(b) every component of a sublevel set `{|g| ≤ λ}` contains a root.** On such
  a component with no root, `log|g|` is harmonic; its minimum is attained, and
  neither an interior minimum nor a boundary-only minimum is possible without
  `g` being constant.
* **(c) components of `{|g| < λ}` are simply connected.** A bounded
  complementary component `H` has `|g| ≤ λ` on `∂H`, hence on `H` by the maximum
  principle, so `H` is not complementary.
* **(d) crossing a critical level merges components.** By (c) no handle can
  appear, so at `λ = μ` the minimising critical point `c*` joins at least two
  components of `{|g| < μ}`, each of which carries exactly one root — for
  `{|g| < μ}` contains no critical point, so each component maps properly and
  unbranchedly onto the disk `D_μ`, hence bijectively. (This last step is the
  argument of `TwoSegmentLevelIdentity.md` Theorem 2; standard lemniscate
  topology, not claimed here.)

By (a) and (d), for any `λ ∈ [μ, 1]` the component `Ω_λ` of `{|g| ≤ λ}`
containing `c*` is compact, connected, and contains `k ≥ 2` roots. Apply
(COVER) at the level it supplies and then the Lemma with `Ω = Ω_λ`: two roots of
`g` are joined by a path in `Ω_λ ⊆ {|g| ≤ 1}` of length `≤ 2`.

Pull back along `w ↦ z_c + R w`, which carries paths to paths and scales length
by `R`:

```text
|f| = R^n |g| ≤ R^n < 1   on the path,        length ≤ 2R < 2.
```

Both strict inequalities Erdős #1041 asks for are produced by the
normalisation, from `R < 1`, and not by the hypothesis. ∎

**And the hypothesis may be weakened to a dense subclass.**
[GenericSufficiencyClosure.md](GenericSufficiencyClosure.md) Theorem L proves
that the two-root path length is lower semicontinuous on the closed-disk class,
so `{Lam <= 2}` is closed. (COVER) — or any other route that ends in an actual
path of length `<= 2` inside the closed lemniscate of the normalised
polynomial — therefore need only be proved for a set of `g` whose closure is
the whole class. Squarefree, roots-in-the-open-disk, and finite-exceptional
one-coefficient genericity are each dense and may be conjoined freely.

**What the reduction removes.** (COVER) asks for **one** root per point, by
**any** path. It therefore does not care that straight spokes fail
(`negative_results` 14, 18, 26, 37), that the nearest root is the wrong one
(`negative_results` 5), that the origin and MEC hubs are empty
(`negative_results` 8, 11), or that the descending inverse-ray branch pair is
too long (`negative_results` 17, 30, 31). Every one of those eliminations is an
elimination of a *two-object* mechanism, and (COVER) is a one-object statement.
It also carries **no separate length obligation**: the constant `2` is produced
by the Lemma from the constant `1`, so unlike
`critical_point_selection_with_inverse_ray_length_control` there is no residual
inequality between a path length and `2R` left to prove afterwards.

## 4. The reduced statement is sharp, and its equality stratum is forced

The constant `1` in (COVER) cannot be lowered, and the equality case is rigid.

> **Theorem (extremal family, exact).** Let `g = z^n − r^n` with `0 < r ≤ 1`.
> Its only critical point is `0`, with `μ = |g(0)| = r^n`, so `μ^{1/n} = r`. Each
> radial segment `[0, r ω^k]` satisfies `|g(t r ω^k)| = r^n(1 − t^n) ≤ r^n = μ`,
> so it lies in the first-merge component; and the distance from `0` to the
> nearest root is exactly `r`. Hence (COVER) holds with **equality** at `λ = μ`,
> at every degree, and the Lemma returns a pair path of length exactly `2r`.

At `r = 1` this is `1` and `2` exactly — the same degeneration
`TrueGeodesicLab.md` proves is extremal for the problem itself, and the same one
`TwoSegmentLevelIdentity.md` Theorem 3 isolates. So the reduction is tight in
precisely the place the problem is tight, which is the property
`StraightSpokeHubCriterionLab.md` §7 asks any candidate to have.

The Euclidean half of (COVER) is free, and it pins the equality stratum:

> **Rigidity.** For any `h`, `min_k |h − z_k| ≤ |g(h)|^{1/n}`, since the
> geometric mean of the distances is `|g(h)|^{1/n}` and the minimum is at most
> the geometric mean. Equality forces **every** root to be equidistant from `h`.

So the *only* way (COVER) can be tight at a point `h` with `|g(h)| ≤ 1` is that
all roots lie on a circle of radius `≤ 1` centred at `h`. Substituting
`w_k = z_k − h` and rescaling, the equality stratum of the reduction is exactly
the following, with no polynomial left in it:

> **(ONE-SPOKE).** For any `w_1, …, w_n` on the unit circle there is a `j` with
> `∏_k |t w_j − w_k| ≤ 1` for every `t ∈ [0,1]`.
>
> Equivalently, writing `p_m = Σ_k w_k^m`, some `j` has
> `Σ_{m≥1} (t^m/m) Re(w_j^m \bar p_m) ≥ 0` on `[0,1]`.

The sum over `j` of those series is `Σ_m (t^m/m)|p_m|^2 ≥ 0`, which gives *"for
each `t`, some `j`"* immediately — this is the radial product identity of
`TwoSegmentLevelIdentity.md` §4b. What (ONE-SPOKE) needs is *"some `j`, for each
`t`"*, and that exchange is not supplied by the identity.

### (ONE-SPOKE) is FALSE, at `n = 5`, and the falsifier was already on file

A concurrent line (`codex_root`, commit `9fede2b363`, checker
`formal_math/probes/erdos1041_one_spoke_countermodel.py`) exhibits an exact
Gaussian-rational countermodel. **Independently re-verified here** in `Fraction`
arithmetic and again by exact segment maxima. The five points

```text
1,      (−20 ± 99i)/101,      (−28 ± 195i)/197
```

have squared moduli exactly `1`, and at the parameters
`t = 339/1000, 1/1000, 1/1000, 1/500, 1/500` respectively every one of the five
products exceeds one:

| `j` | `t_j` | `∏_k \|t_j w_j − w_k\|^2` | exact max over `[0,1]` of `∏_k \|t w_j − w_k\|` |
|---|---|---|---|
| 0 | `339/1000` | `1.000335336109477` | `1.010340874179` |
| 1, 2 | `1/1000` | `1.000124073322536` | `1.000778858212` |
| 3, 4 | `1/500` | `1.000171161469739` | `1.000387427136` |

So **no direction is safe** and (ONE-SPOKE) fails already at degree five.

Two things about this are worth recording rather than tidying away.

**The falsifier is this directory's own witness.** Those five directions are
exactly the ones of `exact_results::two_safe_origin_spokes_counterexample`, whose
roots are `r` times them at `r = 99999/100000`; §6 above reports `0` safe spokes
there. The refutation was in hand and was not connected to the statement it
refutes.

**Sampling could not have found it.** At `n = 3` the configuration space is
two-dimensional after fixing the rotation, so it was swept rather than searched —
`519 841` configurations on a `721 × 721` grid, objective never positive, so the
failure is genuinely invisible at degree three. And `20 000` randomised
configurations at degrees `3`–`12` (uniform, near-regular at three perturbation
scales, two-cluster) produced **no** configuration without a safe spoke, mean
safe-spoke count `4.409`, minimum `1`. `negative_results` entry 19 applies, and it
applies to this file: a search that reports no violation is evidence about the
basins it drew from. The margins here are `10^{-4}` in a set the sampler never
visited.

The one thing that survives from the search is a negative: **no simple selector
is exact.** Four natural crowding statistics, scored against the true safe set on
those `20 000` configurations, pick a safe spoke `99.19%` (`argmin_j Σ_k|w_j−w_k|`),
`98.87%` (`argmax_j Re(w_j \bar p_1)`), `93.02%` (`argmin_j |V'(w_j)|`) and
`89.41%` (`argmin_j` of the two adjacent gaps) of the time. Even where a safe
spoke exists it is not named by any of them.

At `n = 2` the statement does hold, and reduces to one parameter: with
`c = cos φ` the condition is `t·(t^3 − At^2 + Bt − A) ≤ 0` on `[0,1]` with
`A = 2+2c`, `B = 2+4c`.

**What this does and does not cost.** It costs the equality-stratum stress
statement, and nothing else. (ONE-SPOKE) is the equality case of the *Euclidean*
bound, which needs `|g(h)| = 1` and therefore `λ = 1`; §5b shows that at `λ = μ`
that stratum is empty except at the exact regular `n`-gon. The countermodel
configuration has `μ = 0.00477`, so its first-merge component is a small
neighbourhood of the two roots that are `3.2°` apart and does not contain the
centre at all — the `covermu` and `path` arms both pass on it. **The lemma of §2,
the reduction of §3, and (COVER) are untouched**, which is also the claim boundary
the concurrent adjudication records.

**What (ONE-SPOKE) is and is not.** It is the equality stratum of the *Euclidean*
bound, which is reached only when `|g(h)| = 1`. Since a point of `Ω_λ` has
`|g(h)| ≤ λ`, that can happen only at `λ = 1`. So (ONE-SPOKE) is a stress test of
the mechanism at its most degenerate, **not** a necessary condition for (COVER)
at `λ = μ` — §5b shows that stratum is empty there except at the regular `n`-gon,
where §4 already proves all `n` spokes safe. It is stated because it is the
sharpest polynomial-free question the reduction produces, and because a
counterexample to it would settle where the level in (COVER) must be taken.

### 5c. On the cheapest `Γ`, the covering holds in its strongest form

§2 only needs the covering on a compact connected `Γ ⊆ Ω` carrying two roots.
Taking `Γ` to be the pair of descending Newton branches from `c*` — an arc, not a
region — the hypothesis was tested in the **strongest** form the lemma can
consume: every point of the arc must see one of the two roots by a **straight
segment** inside `{|f| ≤ 1}`, which is far more than "some path of length `≤ 1`".

Over the corpus, `283` sampled points per arc:

| | |
|---|---|
| rows scored | `26` |
| points of an arc seeing **neither** root | **`0`** |
| fewest points per row seeing **both** roots | `155` of `283` |
| largest `|h−a| + |h−b|` over all overlap points | `1.91208` (budget `2`) |

So on this `Γ` the covering is not marginal, the overlap set is large rather than
a single point, and **the length budget is met with room and never has to be
imposed separately** — which is the property §3 predicts, since the constant `2`
is produced by the lemma rather than assumed.

**A fifth reproduction of the instrument-defect class.** Twelve rows are excluded
and receipted rather than dropped: two are below degree three, and ten have a
**degenerate minimising hub** — the extremal family `z^n − r^n`, whose critical
point has multiplicity `n − 1`. There the two-branch square-root model is the
wrong local model, exactly as `negative_results` entry 24 records. On
`z^8 − 0.999^8` the sevenfold point at the origin resolves numerically into a
cloud of radius `5.1 × 10^{-3}`, the tracer starts from a spurious hub, and the
"branches" it returns contain points with `|f| = 1.166 > 1`. Those rows first
read as two uncovered points; they are nothing of the kind.

The general rule this yields is worth stating on its own, because it is not the
one entry 24 states: **a traced curve must be verified to lie in the region
before any containment statement is scored on it.** An arc that has left the
lemniscate will report the covering as failing at exactly the configurations
where the covering is provable in closed form. Both guards are now in the arm —
reject a degenerate minimising hub, and validate `max_Γ |f| ≤ 1` before
scoring — and the excluded family is settled by the `extremal` arm instead.

## 5b. The reduction is strictly slack except at one configuration

Take `λ = μ` and normalise `R = 1`. For `h ∈ Ω_μ` the rigidity bound gives a root
within **Euclidean** distance `|g(h)|^{1/n} ≤ μ^{1/n}`, while (COVER) allows
length `1`. So the budget available for a detour off the straight segment is

```text
1 − μ^{1/n}   ≥   1 − D^{1/(n(n−1))},        D := |disc(g)| / n^n ≤ 1,
```

using `μ^{n−1} ≤ ∏_c |g(c)| = D` from §3(a). This is zero exactly when `D = 1`,
which by Fekete's equality case means the roots are the `n`-th roots of unity up
to rotation — and there §4 proves (COVER) outright, with equality, at every
degree. **So (COVER) carries a strictly positive detour budget at every
configuration except the single one where it is a theorem.**

Two readings, and the second is the load-bearing one. First, the reduction does
not invent a new hard regime: its budget is governed by the Fekete deficit, so
the difficulty sits exactly where `HardRegimeIsNearFekete.md` puts it. Second,
the price of passing through the discriminant is the exponent `1/(n(n−1))`: a
deficit `1 − D = δ` yields budget only of order `δ/(n(n−1))`, so this route
cannot be closed by a bound that spends more than that near the extremal. That
is the same exponent arithmetic `TwoSegmentLevelIdentity.md` §5b performs for the
two-segment mechanism, and it is a constraint on any proof of (COVER), not an
obstruction to (COVER) itself.

## 5. Measurement of (COVER)

Distances are measured by multi-source Dijkstra from the root set over a grid of
the first-merge component, with a 16-neighbour stencil and every intermediate
cell of a move required to be interior. **A grid path is a genuine path in the
region, so every number reported is an upper bound on the true intrinsic
distance**: a value at or below `1` is a sound confirmation, and only a value
above `1` would need follow-up. The validated cases fix the residual
discretisation error at about `1.2%` (`z^2 − 0.9^2` returns `0.92093` where the
closed form gives `0.9`; `z^8 − 0.9^8` returns `0.90000`).

Thirty-eight configurations — the extremal family at two radii and six degrees,
the `3°`-from-hexagon witness of `TwoSegmentLevelIdentity.md` §4b, the stored
origin-spoke, minimal-cubic and balanced-quintic witnesses, ten random and twelve
near-Fekete configurations at three perturbation scales:

| quantity | worst over the corpus |
|---|---|
| `sup_Ω dist(·, roots)` — the (COVER) constant | `1.00578` |
| the scale-free ratio `sup_Ω dist / μ^{1/n}` | `1.00678` |
| resulting best pair geodesic (target `< 2`) | `1.99800` at `z^2 − 0.999^2`, which is its closed form `2r` exactly |

Those are the level-scanned numbers of §5a. Measured at the single fixed level
`1.01 μ` instead, the same corpus returns `1.01886`, `1.02325` and `2.00400` —
the last of which exceeds `2` and is pure discretisation, since the closed form
at that row is `1.998`. Scanning the level removes it.

The same corpus checks the reduction's own hypotheses: `max μ = 0.999972` and
`max |disc|/n^n = 0.999998` across all thirty-eight rows, both below one as
§3(a) requires. The Euclidean half of §4 was separately stressed on 4000 random
`(configuration, h)` pairs: worst `min_k|h−z_k| / |g(h)|^{1/n} = 0.999446`,
never above one.

Every excess sits inside the measured `1.2%`–`3%` grid band, and the rows where
the scale-free ratio reads exactly `1.0000` are `z^4 − 0.9^4`, `z^8 − 0.9^8` and
a near-Fekete octic — the extremal family, where §4 proves equality. So the
measurement is consistent with (COVER) holding with the constant exactly `1` and
tight only where §4 says it is.

Two rows deserve naming. At the `3°`-from-hexagon witness — the configuration on
which the centre hub fails — the first-merge component gives `0.771` against a
budget of `1`, slack `0.23`. At the stored five-root origin-spoke witness the
first-merge component gives `0.029`: its two nearest roots are `3.2°` apart, the
observation `TrueGeodesicLab.md` already records.

### 5a. The level in (COVER) is not free, and the existential is what survives

The first version of this measurement fixed the level at `λ = 1.01 μ`. Adversarial
hill-climbing on the resulting objective, roots capped at modulus one, broke it:
at degree three the leader

```text
z ≈ −0.044684909847 + 0.962379872660 i,
    −0.866609339080 − 0.498987227711 i,
     0.864151412519 − 0.503231891122 i          (two roots exactly on |z| = 1)
```

with `μ = 0.9577745241` reads `1.0349` — above `1`, and **stable under grid
refinement**, from `1.0365` at step `0.0174` through `1.0306`, `1.0348` and
`1.0333` at step `0.0035`, while on the same runs the pair geodesic converges
cleanly (`1.7945 → 1.7682`). So it is not a discretisation artefact.

It is a refutation of the *fixed-level* reading only. Scanning the level:

| `λ` | `1.0005 μ` | `1.002 μ` | `1.01 μ` | `1.03 μ` | `1` |
|---|---|---|---|---|---|
| `sup_Ω dist(·, roots)` | `0.9427` | `0.9543` | **`1.0349`** | `0.9950` | `0.9937` |
| roots in the component | 2 | 2 | 2 | 3 | 3 |

Three of the five levels satisfy (COVER), so the hypothesis as stated — *there
is* a level `λ ∈ [μ, 1]` — holds at this configuration with `0.057` to spare.

**The mechanism of the non-monotonicity is visible in the last row.** Raising the
level both adds points that must be covered and adds shortcuts; at a further
merge the shortcuts win discontinuously, which is why the constant drops from
`1.0349` to `0.9950` exactly when the third root joins the component. So the
level must be chosen, and choosing it near `μ` is not automatically right. The
measurement above therefore scans levels and keeps the best, and the receipt
carries this configuration as a dedicated arm so that the behaviour is pinned
rather than rediscovered.

## 6. Exact correction to a stored witness

`exact_results::two_safe_origin_spokes_counterexample` records that the five-root
configuration `r`, `r(−20±99i)/101`, `r(−28±195i)/197` with `r = 99999/100000`
leaves **at most one** safe root-to-origin spoke, having checked four of the
five. Exact Gaussian-rational evaluation of the fifth shows the true count is

> **zero** safe root-to-origin spokes.

Each of the five spokes carries a rational waypoint `t ∈ (0,1)` with
`|f(t z_j)|^2 > 1`, verified in exact `Fraction` arithmetic; the receipt stores
the five waypoints. The witness is therefore sharper than recorded.

It is also the row that *forces* the reduction to be stated on the first-merge
component rather than on the component of the origin. All five roots sit at
modulus `r`, so a path from `0` to any root has Euclidean length `≥ 0.99999` and
a budget of `1` — about `10^{-5}` of slack — while every straight spoke is
excluded. The corridor of admissible detours around the least-bad spoke costs
about `7.7 × 10^{-5}`, which exceeds that budget. Whether the *true* geodesic
from `0` to a root is below `1` there is not settled by that computation, and it
does not need to be: `μ = 0.00477` at this configuration, the first-merge
component is a small neighbourhood of the two roots that are `3.2°` apart, and
the origin is not in it.

**Consequence for how (COVER) must be used.** The level is not free. Taking
`λ = 1` and the component of the origin can put a point at intrinsic distance
above `1` from every root; taking `λ = μ` and the first-merge component does not,
on any row measured here. That is why the reduction quantifies over
`λ ∈ [μ, 1]` and why the measurement is run at `λ` just above `μ`.

## 7. What this does and does not settle

* The Lemma of §2 and the reduction of §3 are **proved**. The extremal-family
  equality of §4 and the rigidity statement are **proved**, by closed form.
  The correction of §6 is **exact**, in rational arithmetic.
* (COVER) is **measured, not proved**, on 38 configurations, by an engine whose
  error runs in the safe direction. Adversarial hill-climbing **has** been run
  against it at degrees 3 to 6, and §5a records what it found: it breaks the
  fixed-level reading at degree three by `3.5%`, stably under refinement, and
  does not break the existential-level statement, which retains `0.057` of slack
  there. `negative_results` entry 19 still applies to everything below the
  refutation: the surviving rows are pinned values, evidence about the basins
  searched, not a proof.
* The level in (COVER) is load-bearing and the constant is **not** monotone in
  it. Any future measurement that fixes a level will report false violations.
* (ONE-SPOKE) — the equality-stratum stress statement — is **FALSE**, refuted at
  `n = 5` by an exact Gaussian-rational countermodel (§4), verified here
  independently in rational arithmetic. It is *not* a necessary condition for
  (COVER): §5b shows its stratum is empty at `λ = μ` away from the regular
  `n`-gon, and both grid arms pass on the countermodel configuration. It is
  retired as a producer, and the retirement removes a stress statement, not a
  step of the reduction.
* Nothing here bears on the descent route `min_c L(c) ≤ 2R`, on the componentwise
  combined-charge lemma of `CriticalTreeLengthCharge.md`, on the near-Fekete
  cusp half of `NearFeketeCuspLaw.md`, or on the two-segment level identity
  `V_E = μ` of `TwoSegmentLevelIdentity.md` — all of which remain as recorded.
* **Novelty is not claimed** for: Fekete's bound or the `μ ≤ R^n` sandwich
  (entry 23); the properness/covering topology of §3(b)–(d), which is standard
  lemniscate material and is already used by `TwoSegmentLevelIdentity.md`
  Theorem 2; the minimum-enclosing-disk normalisation, which is that file's
  Theorem 1; or the sharpness of the extremal family, which `TrueGeodesicLab.md`
  proves. What is new here is the composition: the visibility-overlap lemma, and
  the observation that it converts the corpus's uniform "at most one" wall into a
  sufficient one-root statement carrying no separate length obligation.

**Erdős #1041 remains open.**

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_visibility_overlap.py --part all
```

Arms: `topology`, `covermu`, `extremal`, `amgm`, `e16`. Receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1041_visibility_overlap_receipt.json`.
