# Erdős 1041: the length bound is a capacity bound, and it is sharp at every scale

Status: one reformulation, four proved statements, one rigorous elimination, and
an audited measurement. 2026-08-27. **Erdős #1041 remains open** and nothing
below claims otherwise.

## Current source-generation boundary

The capacity input consumed by (C), namely
`LemniscateCapacityBudget.md` (B), is source-current at commit
`a71e4b11681bcaf1c9ccdfa6551422be479fa619` (27 August 2026). The tracked
source has SHA-256
`177496a687b9c5987705f689f5f1d78204315b5ebad21efe8e9441cdfb290286`.
This is a consumer-generation pin: it makes the exact capacity identity and
its area/source boundary replayable, but it does not promote the ordinary
proof of (C), the finite measurements, or the unresolved componentwise path
bound into Lean or external proof authority.

The reformulation moves the target off the level `1` and onto the level `μ`,
where the constant `2` stops being a number about the unit disk and becomes
`2·cap`. What that buys is the three properties every statement in this
directory has lacked: it is **affine-invariant**, it carries **no unit-disk
hypothesis**, and it is an **equality on a two-parameter family at every degree**
rather than in a limit.

## 1. The conjecture

Throughout `f` is monic of degree `n ≥ 2` and `K_t = {z : |f(z)| ≤ t}`.
[LemniscateCapacityBudget.md](LemniscateCapacityBudget.md) (B) proves
`cap(K_t) = t^{1/n}` exactly.

> **Conjecture (C).** If a connected component of `K_t` contains two roots of
> `f`, then two of them are joined **inside that component** by a path of length
> at most
>
> ```text
> 2 t^{1/n}  =  2 cap(K_t).
> ```

There is no hypothesis on where the roots lie.

**It is enough to check (C) at merge levels.** If `τ < t` and the component
`C_τ` already holds two roots, then `C_τ ⊆ C_t` and `2τ^{1/n} ≤ 2t^{1/n}`, so
(C) at `τ` gives (C) at `t`. The binding levels are therefore the critical
values at which components first meet, and the tightest of them is
`μ = min_c |f(c)|`.

**Scale-freeness.** For `σ > 0` and `τ ∈ ℂ` the affine map `z = τ + σζ` carries
`f` to the monic `g(ζ) = σ^{-n} f(τ + σζ)`, carries `K_t(f)` onto
`K_{tσ^{-n}}(g)`, and multiplies lengths by `σ^{-1}`. Both sides of (C) scale by
`σ^{-1}`, so the ratio `geo / (2 t^{1/n})` is an affine invariant of the pair
`(f, t)`. That is why (C) needs no disk: the disk is a normalisation, not a
hypothesis.

## 2. (C) implies Erdős #1041

> **Theorem 1.** (C) implies Erdős #1041.

*Proof.* Let `f` be monic with all roots in the open unit disk. If two roots
coincide the constant path has length `0` and `|f| = 0 < 1` there, so assume
`f` squarefree. Let `R` be the circumradius of the root set, `R < 1`. The
resultant identity and Fekete's bound — the chain already recorded at
[TwoSegmentLevelIdentity.md](TwoSegmentLevelIdentity.md) §4 — give

```text
μ^{n-1}  ≤  prod_c |f(c)|  =  prod_{i<j} |z_i − z_j|^2 / n^n  ≤  R^{n(n−1)},
```

hence `μ ≤ R^n < 1`. Below the level `μ` every component of `{|f| < μ}` holds
exactly one root, because that set contains no critical point and a proper
unbranched cover of a disk by a connected set is a homeomorphism
([TwoSegmentLevelIdentity.md](TwoSegmentLevelIdentity.md) Theorem 2). At the
level `μ` components meet at `c*`; they cannot meet themselves, since
`{|f| > μ}` has no bounded component ([LemniscateCapacityBudget.md](LemniscateCapacityBudget.md) (A)),
so the component of `K_μ` containing `c*` holds at least two roots. Apply (C)
at `t = μ`: two of them are joined inside `K_μ` by a path of length at most

```text
2 μ^{1/n}  ≤  2R  <  2,
```

and `K_μ ⊆ {|f| < 1}` because `μ < 1`. ∎

**Only one inequality is imported, and it is classical.** Everything specific to
the unit disk is carried by `μ ≤ R^n`; (C) itself never sees the disk.

## 3. The equality family, exactly — not in a limit

> **Theorem 2.** Let `f(z) = (z − τ)^n − λ` with `λ ≠ 0`. Then `μ = |λ|`,
> `ρ := μ^{1/n} = |λ|^{1/n}` is the common distance from `τ` to the roots, and
> the geodesic in `K_μ` between any two distinct roots is **exactly** `2ρ`. So
> (C) is an equality for every `n ≥ 2` and every `λ`. Since every monic
> quadratic has this form, (C) is an equality for **every quadratic**.

*Proof.* Take `τ = 0` and write `λ = r^n e^{iα}`, so the roots are
`z_j = r e^{i(α + 2πj)/n}` and `f'(z) = n z^{n−1}` has its only critical point at
`0`, with `|f(0)| = |λ|`; hence `μ = |λ|` and `ρ = r`.

`K_μ = {z : z^n ∈ D̄(λ, |λ|)}`. For `w ∈ D̄(λ,|λ|)`, expanding
`|w − λ|^2 ≤ |λ|^2` gives `Re(w conj(λ)) ≥ |w|^2/2 ≥ 0`, so that disk lies in the
closed half plane `|arg(w/λ)| ≤ π/2`. Its preimage under `z ↦ z^n` therefore lies
in `n` closed sectors of half-angle `π/(2n)` whose centres are `2π/n` apart —
pairwise disjoint away from the origin, since `π/n < 2π/n`. So `K_μ ∖ {0}` has
exactly `n` components, one containing each root, and `0 ∈ K_μ` because
`|f(0)| = |λ| = μ`.

A path in `K_μ` joining two distinct roots is connected and meets two different
components of `K_μ ∖ {0}`, so it contains `0`; its length is then at least
`|a − 0| + |0 − b| = 2r`. The two radii attain it: on `[0, z_j]` we have
`f(s z_j) = λ(s^n − 1)`, so `|f| = μ(1 − s^n) ≤ μ`, and each radius has length
`r`. ∎

This is the property [StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md)
§7 asks any candidate to have, in a stronger form than the directory has seen.
The corresponding statement at level `1`
([TrueGeodesicLab.md](TrueGeodesicLab.md)) is tight only as `r → 1⁻`; here the
equality holds at **every** `r`, so the extremal set of (C) is a full
two-complex-parameter family `{(z−τ)^n − λ}` and not a degeneration. The
"no polynomial-independent slack" findings of `negative_results` entry 0 are
statements about that degeneration; they say nothing against a bound whose
equality case is a whole family, because such a bound is *supposed* to have zero
slack there.

## 4. Where (C) sits: strictly between what is refuted and the target

Two comparisons, both in the directory's own terms.

**Below the refuted statement.** Let `L(c*)` be the total length of the two
descending inverse-ray branches at the minimum-critical hub. Every such branch
lies in `K_μ`, so `geo ≤ L(c*)` always, and therefore

```text
L(c*) ≤ 2μ^{1/n}   ⟹   (C) at t = μ.
```

`negative_results` entry 28 **refutes** the left-hand statement — the STRONG
completion — at degree four, with ratio `1.004246913`. (C) replaces the branch
by the geodesic, so it survives exactly the step that killed its predecessor.
The gap is not a technicality: measured across every row of §6 below, the
branch ratio exceeds the geodesic ratio everywhere except on the equality
family, where both are `1`.

**Above the level-1 statement.** [TrueGeodesicLab.md](TrueGeodesicLab.md)
conjectures the *radius bound* `geo_{{|f|<1}} ≤ 2 max_i |z_i|`. Since
`geo_{K_1} ≤ geo_{K_μ}` and `2μ^{1/n} ≤ 2R ≤ 2 max_i |z_i|`, (C) implies it. It
is also sharper where it counts: that file's own table gives the radius-bound
ratio as `0.95193` on `z³ − r³` and `0.86525` on `z⁴ − r⁴`, whereas (C) is an
equality on both. And the radius bound measures from the origin, so it is not
affine-invariant; (C) is.

## 5. The bound is a pair budget: the per-lobe halving dies with the hub selector

> **Theorem 3 (the split).** At `t = μ` the two merging lobes `U_a`, `U_b`
> satisfy `Ū_a ∩ Ū_b = {c*}`, so every admissible path passes through `c*` and
>
> ```text
> geo_{K_μ}(a,b)  =  geo_{Ū_a}(a, c*) + geo_{Ū_b}(b, c*).
> ```

That invites halving the budget: `geo_{Ū_a}(a, c*) ≤ ρ` on each lobe, which
would decompose (C) into a statement about **one** lobe, one root and one
critical point — with `f` conformal from the lobe onto a disk. It is an equality
on both extremal families. **It fails at the minimum-critical hub**, and the
failure is exact rather than numerical, because the obstruction is metric:
`geo_{Ū_a}(a, c*) ≥ |a − c*| = d_a`, and `d_a` is a distance between two computed
points, not a relaxation output.

At the degree-four configuration

```text
("0x1.faaa57c9eead2p-1",  "0x1.af062077d3174p-6")
("-0x1.4fab831c004a1p-6", "0x1.ff147e739f661p-1")
("-0x1.f82dc814b0a54p-1", "-0x1.2ba561a3f287ap-6")
("0x1.9fc10c16eb808p-6",  "-0x1.fb6edf63d6e1dp-1")
```

(all four moduli in `0.98489 … 0.99841`, so all roots are in the open unit disk)
the merging pair has

```text
d/ρ  =  (0.99329376, 1.00039121),      (d_a + d_b)/(2ρ)  =  0.996842486,
```

so one merging root is strictly **farther** from `c*` than the geometric mean
`ρ = μ^{1/n}`, while the pair budget still holds with room. The measured
geodesic ratio there is `0.9973`.

**What this does and does not eliminate. The caveat is load-bearing and it was
checked, not assumed.**

The two smallest critical values of this configuration agree to `1.55e−6`
relative, so it sits in exactly the near-tie class of `negative_results` entry
28's own caveat. Both checks that entry demands were run, and both come back the
same way:

| hub | `\|f(c)\|` | merging pair `d/ρ` | max | pair sum `/2ρ` |
|---|---|---|---|---|
| minimum-critical | `0.965045863214` | `0.9932938`, `1.0003912` | **`1.0003912`** | `0.9968425` |
| runner-up | `0.965047363773` | `0.9395988`, `0.9924758` | `0.9924758` | `0.9660373` |
| third | `0.965196524015` | `0.9047364`, `0.9988951` | `0.9988951` | `0.9518157` |

and a tie-guarded adversarial climb — same objective, same budget, but rejecting
any configuration whose two smallest critical values agree to better than
`1.001` — tops out at `0.9192125` at degree four, with the merging pair equal to
the nearest pair.

So the honest reading is narrower than the raw witness suggests, and it is the
one entry 28 arrived at for its own statement:

* **Eliminated:** the per-lobe halving *under the minimum-critical-value hub
  selector*. Whatever else is true, one cannot select `c*` by least critical
  value and then bound each lobe by `ρ` separately. (C) has to be spent across
  the two lobes together — the pair budget survives at every hub above, with
  `0.9968`, `0.9660`, `0.9518`.
* **Not eliminated:** the per-lobe form under a **min-over-admissible-hubs**
  selector. At the runner-up hub the ratio is `0.9925`, and away from ties the
  searcher cannot get past `0.92`. That form is untouched here.
* **Not established:** that the merging pair differs from the nearest pair away
  from ties. At the min-critical hub of this witness it does — merging indices
  sit at `d/ρ = 0.99329, 1.00039` while the two nearest are `0.96831, 0.99329` —
  but that is inside the same `1.55e−6` tie, and over `440` bulk draws across
  six families, plus the tie-guarded climb, the merging pair was the nearest pair
  every time. Gap 1 of [FirstMergeReductionState.md](FirstMergeReductionState.md)
  is therefore **still open in the direction that matters**: no tie-free
  configuration with merging ≠ nearest is on file here.

## 6. The measurement

Instrument, and why its errors run the safe way.

* At level exactly `μ` the path is **pinned through `c*`** and each half is
  relaxed with `c*` as a fixed endpoint. So the neck-cutting artefact — a path
  slipping past the saddle through a tolerance-opened neck of radius
  `μ^{1/n} η^{1/n}`, which is `0.32ρ` at `n = 8` for `η = 10^{-4}` and biases the
  ratio **down**, towards false confirmation — cannot occur at all.
* Descent branches are traced **upward from each root** along `f(z) = s f(c*)`,
  `s : 0 → 1`. No local model at the saddle is used, so an exactly degenerate
  saddle (`negative_results` entry 23) is handled identically to a simple one;
  and since no critical value has modulus below `μ`, no branch meets a critical
  point before `s = 1`.
* Every reported path is **audited for containment** by an independent, denser
  sampler than the one the relaxation uses to admit moves. A contained path of
  length `L` proves `geo ≤ L`, so a ratio below `1` is a genuine confirmation. A
  ratio above `1` would be **inconclusive**, because the relaxation returns an
  upper bound. Only the exact `(d_a + d_b)/(2ρ)` arm can refute.
  Containment is certified to finite sampling resolution, not exactly; see the
  leak disclosure below the witness table.

**On this directory's stored hard witnesses** — the configurations that refute
every explicit path family:

| witness | `n` | geodesic ratio | branch ratio | audit `max\|f\|/μ` |
|---|---|---|---|---|
| QC degree-6, no critical hub carries two spokes | 6 | `0.8610866` | `0.881951` | `1 + 1.4e−9` |
| QC degree-9, no critical hub carries two spokes | 9 | `0.7529590` | `0.779444` | `1 + 9.3e−10` |
| exact cubic, no safe chord and at most one origin spoke | 3 | `0.8523585` | `0.862624` | `1.0` |
| `z³ − (99/100)³`, kills every root chord | 3 | **`0.9999999935`** | `1.000000` | `1.0` |
| quintic, `0` of `5` origin spokes contained | 5 | `0.0826093` | `0.082614` | `1.0` |
| quartic straight-spoke witness | 4 | `0.8970902` | `0.912685` | `1.0` |

The row at `1` is the equality family of Theorem 2, where the value is exact
rather than measured; the relaxation reproduces it to `6.5e−9`.

**Two rows leak, and the leak is disclosed rather than tuned away.** The
relaxation admits a move using a fixed number of samples per segment, so between
samples `|f|` can rise slightly above the level, and the independent denser audit
reports it: `1.4e−9` relative on the QC degree-6 row and `9.3e−10` on QC
degree-9. Such a path is not *literally* inside `K_μ`, so it is not by itself a
legal witness. It becomes one because shrinking it back inside costs `O(leak)` in
length, and those two rows carry margins of `0.139` and `0.247` below the bound —
eight orders of magnitude more. The receipt gates on exactly that coupling: a row
may audit above `1` only if its margin exceeds `1e−3`. The four rows that matter
most for sharpness — the equality family and the two smallest-margin ones — audit
at exactly `1.0`.

**In the near-Fekete shell**, where [HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md)
locates the hard configurations and where the corpus records six suprema pinned
by searches that never entered the shell. Angular perturbation `ε` of the
regular `n`-gon at radius `1 − 10^{-7}`:

| `n` \ `ε` | `1e-2` | `1e-4` | `1e-6` | `1e-8` | `1e-10` |
|---|---|---|---|---|---|
| 3 | `0.9513848` | `0.9912700` | `0.9992153` | `0.9999501` | `0.9999899` |
| 4 | `0.7564370` | `0.9584863` | `0.9923845` | `0.9983442` | `0.9995562` |
| 5 | `0.7232865` | `0.8999125` | `0.9685653` | `0.9899194` | `0.9964003` |
| 6 | `0.6033656` | `0.8498403` | `0.9256115` | `0.9713918` | `0.9914674` |
| 8 | `0.4417561` | `0.7407635` | `0.8575711` | `0.9323031` | `0.9592033` |

The ratio **rises to `1` from below**, monotonically, at every degree. That is
the signature Theorem 2 predicts and the one a sharp bound must show; it is not
a supremum pinned below a threshold by a search that cannot reach the extremum,
because the extremum here is known in closed form and is `1`.

**Adversarial search** on the geodesic ratio, six seeded and random restarts per
degree with local refinement, winners re-scored at high budget:

| `n` | 3 | 4 | 5 | 6 |
|---|---|---|---|---|
| `sup` geodesic ratio | `0.9973558` | `0.9972090` | `0.9390079` | `0.7898749` |

Nothing exceeded `1`, and — unlike the six pinned suprema the corpus warns
about — these are **not** pinned just under the threshold; the searcher simply
lives in a different basin from the extremal family, whose value is `1` by
Theorem 2.

## 7. The margin opens linearly in the critical radius — the cusp is a coordinate

[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) records the obstruction
that has blocked every perturbative attack at the extremum: it is a **cusp**,
not a smooth maximum, and "any perturbative attack there must handle a
fractional-power response, which is a materially harder object than a Hessian."

For (C)'s objective the response is not merely fractional-power; it is **linear
in the one variable that the cusp law already supplies**, and the slope is
explicit.

> **Proposition 4.** Let `f_ε(z) = z^n − m + ε h(z)` with `deg h ≤ n−1`,
> `h'(0) ≠ 0`, `m = R^n > 0`, and let
> `ρ_crit = (ε|h'(0)|/n)^{1/(n−1)}` be the radius of the critical `(n−1)`-gon of
> `exact_results::near_fekete_cusp_law_and_strict_local_maximality`. Let `c*` be
> the selected hub and `a, b` the two roots merging there, at angular offsets
> `θ_a, θ_b ≥ 0` from the direction of `c*`, with `θ_a + θ_b = 2π/n`. Then as
> `ε → 0`
>
> ```text
> 2ρ − (d_a + d_b)  =  ρ_crit ( cos θ_a + cos θ_b ) + O(ρ_crit^2)
>                   ≥  2 cos^2(π/n) · ρ_crit · (1 + o(1))   >   0.
> ```

*Proof.* At a critical point of modulus `ρ_crit` the term `z^n` contributes
`O(ρ_crit^n)` and `ε h` contributes `O(ε)`, so `μ = |f_ε(c*)| = m + O(ε)` and
`ρ = μ^{1/n} = R + O(ε)`. Since `ε = (n/|h'(0)|) ρ_crit^{n−1}` and `n ≥ 3`, that
error is `O(ρ_crit^{n−1}) = o(ρ_crit)`. The roots are `R e^{iφ_j} + O(ε)` with
`φ_j` equally spaced, and `|c*| = ρ_crit ≪ R`, so

```text
d_a = |a − c*| = R − ρ_crit cos θ_a + O(ρ_crit^2 / R),
```

and likewise for `b`. Subtracting from `2ρ = 2R + o(ρ_crit)` gives the identity.
The merging pair is the pair whose root directions bracket the direction of
`c*`, so `θ_a + θ_b = 2π/n` with both non-negative; on that segment
`cos θ_a + cos θ_b = 2 cos(π/n) cos((θ_a−θ_b)/2)` is minimised at an endpoint,
where it equals `1 + cos(2π/n) = 2cos^2(π/n)`. ∎

So the **metric slack** — the whole budget (C) has to spend — is positive and
first order in `ρ_crit`, with a slope bounded below by `2cos²(π/n)`. What (C)
then needs near the extremal is exactly that the **geodesic deficit**
`geo − (d_a + d_b)`, which is `0` on the extremal family itself, is `o(ρ_crit)`.

That is what the measurement says. Fixing the perturbation direction `h` (so the
constant is fixed) and sweeping `ε` over seven decades from `1e-2` to `1e-8`:

| `n` | slope vs `log ε` | predicted `1/(n−1)` | slope vs `log ρ_crit` | `(1−ratio)/ρ_crit` | band `[cos²(π/n), cos(π/n)]` |
|---|---|---|---|---|---|
| 3 | `0.4989` | `0.5000` | `0.9981` | `0.463 … 0.469` | `[0.250, 0.500]` |
| 4 | `0.3248` | `0.3333` | `0.9747` | `0.626 … 0.706` | `[0.500, 0.707]` |
| 5 | `0.2412` | `0.2500` | `0.9645` | `0.702 … 0.799` | `[0.655, 0.809]` |
| 6 | `0.2021` | `0.2000` | `1.0067` | `0.864 … 0.884` | `[0.750, 0.866]` |

The exponent in `ρ_crit` is `1` at every degree, and the constant lands in the
band Proposition 4 predicts — which it could not do if the geodesic deficit were
also first order in `ρ_crit`. (The degree-6 top, `0.884` against `0.866`,
overshoots the band by 2%; the band is a leading-order prediction and the coarse
end of that sweep sits at `ε = 1e-2`, so this is the expected size of the
next-order term rather than a conflict.)

The consequence for method is the point. `1 − geo/(2ρ) ≍ ρ_crit ≍ ε^{1/(n−1)}`,
and eliminating `ε` through the smooth Fekete maximum (`1 − D ≍ ε²`) gives the
intrinsic form

```text
1 − geo/(2 μ^{1/n})   ≍   (1 − D)^{1/(2(n−1))},        D = prod_{i<j}|z_i−z_j|^2 / n^n,
```

so the margin in (C) is a **power of the discriminant deficit**. That is the
shape of the quantitative Fekete-stability estimate
`exact_results::quantitative_fekete_stability_hadamard_defect` names as the
object joining the two halves of the hard-regime split, now with the exponent
attached. The cusp does not have to be defeated; it has to be entered in the
coordinate `ρ_crit`, in which the response is affine.

## 8. What is open, and what would decide it

The whole of (C) is open. What §5 fixes is the *shape* a proof may take: it must
be a two-lobe argument, because the one-lobe halving is false.

Three sub-questions, in increasing order of strength.

1. **The metric floor**, which reduces to one clean statement.

   > **Claim L.** At the minimum-critical hub `c*`, the two merging roots are the
   > two roots nearest `c*`.

   `geo ≥ d_a + d_b`, so (C) needs `d_a + d_b ≤ 2ρ` for the **merging** pair.
   `exact_results::critical_pair_metric_scale` proves exactly that for the two
   **nearest** roots, so **Claim L closes the metric floor of (C) and gap 1 of
   [FirstMergeReductionState.md](FirstMergeReductionState.md) at the same
   time** — that file's gap 1 is precisely the assertion that Claim L may fail.
   The receipt's own arm gives worst `(d_a+d_b)/(2ρ) = 0.999946` over `72`
   configurations at `n = 3 … 10`, with the merging pair equal to the nearest
   pair in `72/72`; a wider sweep over the same six families gave worst
   `0.999767` over `440` draws, also `440/440`.

   A dedicated adversarial sweep on the violation ratio
   `(max over merging roots of d) / (second-smallest d)` returned exactly
   `1.0000000` at `n = 3, 4, 5, 6`, with critical-value separations `2.06`,
   `3.18`, `4.86`, `4.33` — no tie anywhere near. **At `n = 8`, with the guard
   disabled, it broke Claim L outright, returning `1.6893509`** — not a marginal
   violation. That winner has `critsep = 1.00000`: the two smallest critical
   values equal to five decimals, so the searcher had climbed into the
   ambiguous-hub regime, where "which two lobes merge" stops being well posed.

   **Every tie-free retest comes back clean, and this time with the diagnostic
   that settles it.** A second, independently seeded search at `n = 8`, run at
   four guard levels and reporting how many branches actually arrive at `c*`:

   | guard on `\|f(c₂)\|/\|f(c₁)\|` | `sup` violation ratio | arrivals at `c*` | `critsep` at winner |
   |---|---|---|---|
   | none (`1.0`) | `1.0000000` | `2` | `1.006369` |
   | `1.001` | `1.0000000` | `2` | `1.998404` |
   | `1.05` | `1.0000000` | `2` | `4.380695` |
   | `1.2` | `1.0000000` | `2` | `1.601602` |

   The arrival count is `2` in every row, so the merging pair is well posed at
   each winner and the ratio is measuring what it claims to.

   The first sweep, run to completion, agrees at every one of its ten guarded
   rows — `1.0000000` at `n = 3, 4, 5, 6, 8` under guard `1.001`, and again at
   all five degrees under guard `1.05`, at separations ranging from `1.10` to
   `115.5`. **Its `n = 8` row, the one that violated with the guard off, returns
   `1.0000000` the moment the guard is switched on** (`1.001`, at
   `critsep = 1.10170`).

   So **the only violation of Claim L on file sits at a critical-value tie** —
   the same class as §5 and as `negative_results` entry 28's own caveat, and a
   statement about the min-critical-hub *selector* rather than about the
   problem. Claim L is not refuted.

   **It is also not established, and the reason is the instrument, not luck.**
   The objective is *flat*: it equals `1` identically on
   the whole set where the merging pair is the nearest pair, so a hill-climber
   has no gradient and only the random seeding can discover a violation. This is
   the same degeneracy [TwoSegmentLevelIdentity.md](TwoSegmentLevelIdentity.md)
   §3b had to excise for (SPOKE≥1). Anyone testing Claim L seriously should first
   build a proxy with a gradient — for instance how far the third-nearest root's
   lobe is from reaching `c*` — rather than reuse this one.

   One structural remark in its favour, since
   the obvious counterexample shape is "a root Euclidean-close to `c*` whose
   lobe is too small to reach it": that shape is blocked, because the critical
   equation `Σ_k 1/(c − z_k) = 0` gives
   `1/d_j ≤ Σ_{k≠j} 1/d_k`, so a root close to `c*` forces another root close to
   `c*`. What is missing is the step from there to which two lobes actually
   touch. Tracked as `cap_quick_erdos1041_decide_merging_pair_nearest_pa_20d69b8f9d6d`.
   *A proof of the nearest-pair case, for the record, since the directory cites
   it without a proof sketch:* normalise `ρ = 1`, so `prod_k d_k = 1`, and
   suppose `d_(1) + d_(2) > 2`. Then `d_(2) > 1`, and `d_k ≥ d_(2)` for `k ≥ 2`
   gives `d_(1) ≤ d_(2)^{−(n−1)}`. The critical-point identity
   `Σ_k 1/(c − z_k) = 0` gives `1/d_(1) ≤ Σ_{k≥2} 1/d_k ≤ (n−1)/d_(2)`, hence
   `d_(2)^n ≤ n − 1`. On `(1, (n−1)^{1/n}]` the function `x ↦ x^{−(n−1)} + x` is
   strictly decreasing, so `d_(1) + d_(2) ≤ d_(2)^{−(n−1)} + d_(2) < 2` —
   a contradiction. At `n = 2` the identity forces `d_1 = d_2 = 1` and the sum
   is exactly `2`.
2. **The chord deficit against the metric slack.** (C) says the geodesic deficit
   `geo − (d_a + d_b)` is at most the metric slack `2ρ − (d_a + d_b)`. Both
   vanish together, and only on the family of Theorem 2 — which is why no
   uniform margin can exist and why an `L^∞` turning bound cannot work, exactly
   as [TurningFloorRefutation.md](TurningFloorRefutation.md) found for the
   branch version. The geodesic version is strictly weaker at every point, and
   that is the whole gain.
3. **(C) itself.**

One structural remark worth recording, because it explains the constant's
appearance.
Both lobes lie inside `K_μ`, whose boundary is a lemniscate; a construction that
leaves each root along an inverse ray to a common level, hops along that level
curve, and descends again gives, for a component of `K_t` covering the value
circle `k` times,

```text
geo  ≤  ( length(∂C)  +  2 · Σ_i length(lift_i) ) / k,
```

with the hop taken along the shortest of the `k` boundary arcs cut out by the
`k` lift endpoints. On `z^n − λ` the first term tends to `2 t^{1/n}` from above
as `n → ∞` and the second is `O(1/n)` — so this construction is asymptotically
critical and always loses. The same polynomial family is also the conjectured
extremal in the classical global lemniscate-length problem, which explains the
near-miss analogy; it does not turn the two open problems into the same theorem.
Recorded as a near-miss rather than a route: the construction never reaches `2`,
and the inspected global bound is degree-dependent.

## Source and authority boundary

Theorems 1–3 and Proposition 4 are repository-authored ordinary mathematics;
their proofs use the displayed identities, metric inequalities, and finite
audits in this note. The only external comparison used in §8 is Alexandre
Eremenko and Walter Hayman's *On the length of lemniscates*, Michigan
Mathematical Journal 46 (1999), 409–415, whose official arXiv representation is
archived at
`state/arxiv_cache/0805.2295/0805.2295.pdf` (SHA-256
`49518f120caa1f477521a0bc7edd36e7ac44f1227116fc3ab30d5371bb6d5677`, official
arXiv record `https://arxiv.org/abs/0805.2295`). In the
rendered primary text, the opening/abstract on printed p. 1 records the
historical extremal conjecture, while Theorem 1 on printed p. 1 gives the
degree-dependent global estimate `|E(p)| ≤ α₀ d < 9.173d` for monic degree-`d`
polynomials; Lemmas 1–2 and the corollary on printed p. 2 give the proper-map
intersection and projection-length context. That source does not state (C),
the componentwise winding/coarea estimate, the `K_μ` pair path, or the
assembled constant-factor theorem. No priority or novelty claim is made here,
and the finite computations in §6 remain measurement rather than proof.

## Concurrent work in this directory, not assimilated here

A sibling session landed `formal_math/probes/erdos1041_newton_flow_transport.py`
while this note was being written. Its stated mechanism is that the Newton flow
`f(N_t z) = e^{−t} f(z)` fixes every root, so **any** curve joining two roots can
be transported into `{|f| < 1}` and containment costs nothing — leaving only the
length of the transported curve. If that holds it bears directly on (C), because
(C) is a pure length statement once containment is free.

It is **not** used anywhere above, and nothing here depends on it. A concurrent
lab is reported, not verified: this directory has retracted a same-day sibling
result before. Whoever reconciles the two should check the transport's behaviour
where the flow meets a critical point, which is the step (C) buys outright by
working at the level `μ` where the two lobes touch at exactly one point.

## Claim boundary

Theorems 1, 2 and 3 are proved above; Theorem 2's equality is asserted from its
closed form, not from the integrator, per this directory's rule for equality
families. The per-lobe elimination of §5 is exact, being a comparison of two
computed distances, and carries the stated near-tie caveat. Everything in §6 is
measurement: each reported geodesic is the length of an explicitly audited
contained path, hence an upper bound on the truth, so ratios below `1` are
witnesses and a ratio above `1` would decide nothing. Erdős #1041 is open, (C)
is open, and (C) has not been shown to be necessary — it could fail while #1041
is true.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_capacity_geodesic.py
```

**Receipt, 2026-08-24: `verdict pass`, exit `0`**, with all ten gates green —

```text
equality_family_exact=True   fekete_chain=True        per_lobe_entry28_pattern=True
cusp_law_first_order=True    worst_ratio_le_1=True    worst_audit_le_1=True
leaky_rows_have_margin=True  worst_floor_le_1=True    branch_ge_geodesic=True
near_fekete_rising=True
worst ratio 0.9999999934824331   worst audit 1.0000000014302808
worst floor 0.999946424032415    min branch-geo 3.0586644328423063e-13
```

**The first run of this script returned `FAIL`, and the correction is recorded
rather than hidden.** It gated the audit at `1 + 1e-9`, below what a
finitely-sampled containment test can certify: the QC degree-6 path audits at
`1 + 1.4e-9`. The fix was to set the tolerance to the measured resolution
(`1e-7`), add the coupled `leaky_rows_have_margin` gate above, densify the audit
to a fixed 320 samples per segment, and — the actual defect — make the script
print its gate breakdown, since the first run reported every arm as passing and
then a bare `FAIL`. Nothing in §1–§7 changed; §6's leak disclosure was added
because of it.
