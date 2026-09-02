# Erdős 1041: the sublevel sets have capacity exactly `t^{1/n}`, and what that buys

Status: four unconditional facts about `K_t = {|f| ≤ t}`, proved here, plus a
value-plane reformulation of the path problem and one certified construction that
is **not** a hub-and-spoke path. Current through 2026-08-27 source audit. None
of this proves Erdős #1041. What it adds is an *a priori* layer keyed to the **level** `t` rather than to a selected
hub: `cap`, `Area` and `diam` of `{|f| ≤ t}` all scale as powers of `t^{1/n}`, with
no branch tracking and no hub selection anywhere in the statements. One tempting
consequence — a metric bound for the merge pair — is shown below to be subsumed by
Gauss–Lucas and is recorded as a dead end rather than a gain.

Throughout `f` is monic of degree `n ≥ 2` with roots `z_1,…,z_n`, `R` is the
circumradius of the root set, and `K_t = {z : |f(z)| ≤ t}`.

## The four facts

> **(A) Fullness.** `{|f| > t}` has no bounded component, so `Ĉ ∖ K_t` is
> connected and `K_t` is full.
>
> **(B) Capacity.** `cap(K_t) = t^{1/n}` exactly. The Green's function of
> `Ĉ ∖ K_t` with pole at `∞` is `g(z) = (1/n)·log(|f(z)|/t)`.
>
> **(C) Area.** `Area(K_t) ≤ π·t^{2/n}`, with equality **iff** `f = (z−a)^n`.
>
> **(D) Diameter.** Every connected component `C` of `K_t` satisfies
> `diam(C) ≤ 4·t^{1/n}`.

*Proof of (A).* On a bounded component `U` of `{|f| > t}` we would have `|f| = t`
on `∂U` and `|f| > t` inside, contradicting the maximum principle for `|f|`. ∎

*Proof of (B).* By (A) the complement is connected. `g = (1/n)log(|f|/t)` is
harmonic and positive there, extends continuously by `0` to `∂K_t`, and since `f`
is monic `g(z) = log|z| − log t^{1/n} + o(1)` as `z → ∞`. So the Robin constant is
`log t^{1/n}` and `cap = t^{1/n}`. ∎

*Proof of (C).* The isoperimetric inequality for logarithmic capacity,
`cap(E) ≥ (Area(E)/π)^{1/2}` with equality exactly for closed disks, applied to
(B). `K_t` is a disk iff all roots coincide. ∎

*Proof of (D).* `C` is a continuum with `cap(C) ≤ cap(K_t) = t^{1/n}`, and
`cap(E) ≥ diam(E)/4` for every continuum. ∎

> **(D′) The constant `4` in (D) is sharp**, and the extremal family is the
> **Chebyshev** one, not `z^n − t`.

*Proof.* Let `T_n` be the monic Chebyshev polynomial of `[−2,2]`, so that
`T_n(2cos φ) = 2cos nφ`. Then `|T_n| ≤ 2` on `[−2,2]`, hence
`[−2,2] ⊆ K_2` and `diam(K_2) ≥ 4`, while (B) gives `cap(K_2) = 2^{1/n}`. So

```text
diam(K_2) / (4·cap(K_2))  ≥  2^{−1/n}  →  1     as n → ∞. ∎
```

`K_2` is in fact a lens of width `O(1/n)` about the segment — for `z = 2cos(α+iβ)`
one has `|T_n| ≈ e^{n|β|}` — so the extremal degeneration is the **interval**
lemniscate, exactly the case a segment makes `cap = diam/4` an equality. Measured:
the ratio tracks `2^{−1/n}` to grid error for `n ≤ 20` (`n=2`: `0.70688` against
`0.70711`; `n=20`: `0.96563` against `0.96594`). Beyond `n ≈ 20` the coefficient
form of `T_n` loses all precision to cancellation — `sup_{[−2,2]}|T_n|` returns
`605` at `n=40` and `2.4·10²²` at `n=80` instead of `2` — so the large-`n` rows are
numerical garbage and are not used; the proof above needs no numerics.

This kills the natural guess. `z^n − t` gives only
`2^{1/n}sin(π⌊n/2⌋/n)/2 ≤ √2/2`, so `2√2·t^{1/n}` looked like the sharp constant
and is not: the diameter-extremal lemniscates are thin ones around a segment, and
the roots-of-unity family is nowhere near extremal for this quantity.

**Receipt.** [`scripts/check_erdos1041_capacity_budget.py`](scripts/check_erdos1041_capacity_budget.py),
grid `1200`, 22 configurations, exit `0`. Worst `Area/(π t^{2/n}) = 0.99991`,
attained on `f = z^n` — the equality case of (C), the residual being grid error.
Worst `diam/(4t^{1/n}) = 0.70711`.

That diameter number is **not** the grid's; the grid returns `0.63204` and is
wrong low. A single-point touching is invisible to any grid: the two lobes of
`{|z²−1| ≤ 1}` meet only at `z = 0`, which no grid samples, so the components are
reported separately and the diameter is understated. The script therefore carries
a second, grid-independent arm — the exact diameter of `K_t` for `f = z^n − t`,

```text
diam = 2·(2t)^{1/n}·sin(π⌊n/2⌋/n),      ratio to 4t^{1/n} = 2^{1/n}sin(π⌊n/2⌋/n)/2
```

whose worst value is `√2/2 = 0.70711` at `n = 2`. For `n ≥ 4` the lobes overlap
enough that the grid does connect them, and it then agrees with the closed form
(`n = 4`: grid `0.59328` against exact `0.59460`). Both arms must pass.

## What this gives the standing obligation

One thing, and one non-thing that is worth recording so it is not re-derived.

**The merge-pair diameter bound is subsumed by Gauss–Lucas — do not use it.**
Applying (D) at the first-merge level `t = μ = min_k|f(c_k)|` gives
`|a − b| ≤ 4μ^{1/n}` and `d_a, d_b ≤ 4μ^{1/n}` for the merge pair, with no hub
selection and no branch tracking. That looks like it fills gap 1 of
[FirstMergeReductionState.md](FirstMergeReductionState.md) — the merge pair has no
metric bound, only the *nearest* pair does. **It does not.** Gauss–Lucas puts every
critical point in the convex hull of the roots, so centring at the circumcentre
already gives `|c*| ≤ R` and `|a| ≤ R`, hence

```text
d_a ≤ 2R,   d_b ≤ 2R,   |a − b| ≤ 2R      (free, for every pair and every hub)
```

and (D) improves on this only when `μ^{1/n} < R/2`. The hard regime is the
near-Fekete one where `μ = R^n` exactly, i.e. `μ^{1/n} = R`, so (D) is weakest
precisely where the problem is. Recorded as a dead end because it is an attractive
one: the bound is genuinely unconditional and genuinely about the right pair, and
it is still worth nothing here.

What survives is that (D) scales with the **level** `t^{1/n}` rather than with `R`,
which is the correct currency for any statement that must degenerate as the pinch
closes. Nothing in this directory used that before.

**The missing quantitative input for (H).** `CriticalTreeLengthCharge.md` reduces
the componentwise charge lemma (F) to the trace estimate

```text
∫_{Γ_B} |φ'(w)| |dw| ≤ 2R(k−1),        φ : D → Ω  the Riemann map,
```

and says the next step "must construct a multiplicity-weighted measure on `Γ_B`
whose `|φ'|` trace is controlled". Any such argument is an area or extremal-length
argument, and area is exactly what (C) supplies:

```text
∫_D |φ'|² dA = Area(Ω) ≤ π t^{2/n}.
```

The one clean consequence I can prove from it, by Cauchy–Schwarz on the radii of
`D` with the singular part cut at radius `δ`:

```text
min over α of  ∫_δ^s |φ'(u e^{iα})| du   ≤   t^{1/n} · √(½ ln(s/δ)),
```

so some radius of `D` has image of length `O(R·√log)` — an unconditional bound of
the right *shape* on a root-to-boundary path. It does not close (H): joining two
roots needs two such radii plus a boundary hop, and the constant is not `2`.

## The value plane: the admissible path family is larger than inverse rays

Every path in this directory so far is an inverse ray — a lift of a radial segment
`[0, f(c)]` in the value plane. That is one point of a much larger family.

> **Reformulation.** Let `γ` be any loop in the open unit value-disk based at `0`.
> Each of its `n` lifts is a path in `{|f| < 1}` joining a root to the root given
> by the monodromy of `γ`, of length `∫_γ |dv| / |f'(z(v))|`. The descent arc at a
> critical point `c` is exactly the degenerate loop `0 → f(c) → 0`, whose monodromy
> is the transposition of the two merging roots.

Two exact identities on this plane, both verified:

```text
(V1)   Σ_{f(z)=v} 1/f'(z) = 0        for every n ≥ 2 and every regular value v
(V2)   ∫_{|v|=ρ} S(v)|dv| = Len({|f| = ρ}),      S(v) = Σ_{f(z)=v} 1/|f'(z)|
```

**(V2) is not new in integrated form.** Integrating it over `ρ` gives
`∫_0^1 Len({|f|=ρ})/ρ dρ = ∫_{|f|<1}|f'/f|dA`, which is exactly the coarea identity
already proved in [RadialLiftCoareaGapLab.md](RadialLiftCoareaGapLab.md)
(`∫_0^{2π}R(θ)dθ = ∫_U |f'/f| dA`). What the fixed-`ρ` form adds is only that the
angular integrand at a single level **equals a lemniscate length**, which is what
lets a bound on `Len({|f|=ρ})` enter at all.

(V1) says the `n` lifts of any value path move with velocities summing to zero —
their centroid is pinned at `−a_{n−1}/n`, which is the trivial statement that the
roots of `f − v` have `v`-independent sum, in the form that bears on path length.
(V2) makes the total lift length over a value circle **equal** to a lemniscate
length, which is the object of the Erdős–Herzog–Piranian problem — so a bound on
the length of a lemniscate enters this problem here, and nowhere else in this
directory. Integrating (V2), `∫_0^1 Len({|f|=ρ})/ρ dρ = ∫_{|f|<1} |f'/f| dA`.

*Source status.* The linear bound `Len({|f|=1}) ≤ Cn` with `C ≈ 9.17` and
the Eremenko–Hayman comparison are now checked against the downloaded primary
text `state/arxiv_cache/0805.2295/0805.2295.pdf` (SHA-256
`49518f120caa1f477521a0bc7edd36e7ac44f1227116fc3ab30d5371bb6d5677`, official
record `https://arxiv.org/abs/0805.2295`). The opening/abstract on printed p. 1
records the historical extremal comparison with `z^n − 1`, and Theorem 1 on
printed p. 1 gives the degree-dependent estimate `|E(p)| ≤ α₀ d < 9.173d`;
the proper-map/projection context is in Lemmas 1–2 and the corollary on
printed p. 2. This source does not establish the local componentwise
coarea estimate, the proposed `K_μ` path, or the unrestricted Erdős theorem.
The qualitative conclusion below (that unweighted averaging costs a factor
`n`) does not depend on the constant, but any quantitative use of (V2) must
retain this degree-dependent source boundary. The source acquisition and page
mapping are recorded in
`docs/formal_math/observatory_source_reaudit/erdos1041_constant_factor_primary_source_read_20260826.json`.

The Pólya attribution for the global area--capacity input is separately bound
to the downloaded primary scan recorded in
`docs/formal_math/observatory_source_reaudit/erdos1041_constant_factor_polya_primary_text_read_20260827d.json`.
The relevant second communication is at printed pp. 280--282 (scan pp.
312--314), with PDF SHA-256
`2de0cd74d07f02ff08be81e1eaac35b5529e1c60e35e1c5c9b4c4ca0602fd205` and
official PDF
`https://archive.org/download/sitzungsbericht1928preu/sitzungsbericht1928preu.pdf`.
Those pages support the global filled-lemniscate area--capacity inequality;
they do not establish the local componentwise coarea estimate, any proposed
`K_μ` path, or the unrestricted Erdős theorem. The local arguments and the
source-specific route boundary remain conservative, with no priority claim.

Measured: (V1) to `3.3e−14` over 400 fibres at `n = 2…11`; (V2) to `5e−5`
(quadrature-limited) at `n = 2,3,5,7` and `ρ = 0.3, 0.8, 1.5`.

**Why the obvious averaging does not close it, stated so it is not retried.**
Bounding the `k`-cycle average of the lift lengths over a level circle costs a
factor `n`: any bound of the form `Len({|f|=ρ}) ≤ Cnρ^{1/n}` makes the radial term
integrate to `Θ(Cn²)`, against a target of `2k ≤ 2n`. This is the same `n` that
`negative_results` entry 31 records as unbounded for the summed merge-topology
bound, and it is not repaired by choosing the value argument.

## A certified path that is not a hub-and-spoke path

The level-circle route, taken on the extremal family `f = z^n − r^n`: lift the
value path `0 → ρ`, then once around `|v| = ρ` with `r^n < ρ < 1` (where the
monodromy is an `n`-cycle), then back down. `|f|` equals `|v| ≤ ρ < 1` along the
whole path by construction, and the endpoints are adjacent roots.

| `n` | 3 | 6 | 8 | 10 | 12 | 15 | 20 | 30 | 50 |
|---|---|---|---|---|---|---|---|---|---|
| path length at `r = 1−10⁻⁹` | 3.566 | 2.565 | 2.223 | **1.965** | 1.762 | 1.524 | 1.242 | 0.905 | 0.585 |

**This does not beat the descent path where the problem is hard.** At `r = 0.999`
it returns `4.485` at `n = 2` against a true geodesic of `1.998`, and it only
falls below `2r` from `n ≈ 10`. Against `TrueGeodesicLab.md`'s proved lower bound
`2(r − (1−r^n)^{1/n})` it runs at ratio `1.19` to `2.27` for `n = 2…40`. So it is
a certified explicit construction inside the band that lab measured on a grid —
a certificate where there was an estimate — and nothing more. Recording it because
it is the first path in this directory built from the value-plane monodromy rather
than from a hub, and because its degree dependence runs the *opposite* way to every
hub route: hub routes are tight at small `n` and this is tight at large `n`.

## The L² currency dies too, and for the opposite reason to the L¹ one

The natural thing to do with (C) is to make **area** the currency, replacing the
L¹ coarea currency `∫_U|f'/f|dA` that
[RadialLiftCoareaGapLab.md](RadialLiftCoareaGapLab.md) eliminates. It is a real
change of currency: the L¹ total grows like `n²`, whereas `Area({|f|<t}) ≤ πt^{2/n}`
is bounded by `πR²` **independently of the degree**. The candidate is

```text
L(c) ≤ C·√( Area(Ω_a) + Area(Ω_b) ),        Ω_a, Ω_b the one-root components,
```

which via `Area(Ω_a)+Area(Ω_b) ≤ Area({|f|<μ}) ≤ πμ^{2/n} ≤ πR²` would give
`L(c) ≤ C√(2π)·R`, and hence the target provided `C ≤ 2/√(2π) = 0.7979`.

**It fails on `z^n − r^n`, by a factor `√n`.** At its own critical level `μ = r^n`
the components are thin spikes: the change of variables `w = z^n` gives the petal
area exactly as `n^{-2}∫_{D(r^n,r^n)}|w|^{2/n−2}dA(w)`, and the whole flower has
area `→ πr²/2`, so one petal has area `~ πr²/(2n)` while its spoke has length `r`.
Measured at `r = 1`:

| `n` | 3 | 4 | 6 | 10 | 20 | 40 |
|---|---|---|---|---|---|---|
| petal area | 0.5928 | 0.4236 | 0.2716 | 0.1594 | 0.0788 | 0.0393 |
| `2r/√(2·area)` | 1.837 | 2.173 | 2.713 | 3.543 | 5.037 | 7.133 |

against the required `0.7979`. The ratio grows like `√(2n/π)`.

So both isotropic currencies are eliminated by the **same family**, for opposite
structural reasons: the L¹ one because that family concentrates all `n−1`
critical-value arguments on a single ray, so one angular spike is charged with
multiplicity `n−1`; the L² one because that family's components are thin spikes,
with length `R` and area `~R²/n`. Concentration in the value plane and thinness in
the `z`-plane are the two faces of the same degeneration, and any charge that is
isotropic in either plane pays a degree-dependent penalty — `n` in L¹, `√n` in L².
This is a positive reading of that lab's "what remains live": the charge must be
localised on the descending edge, not integrated against a rotation-invariant
measure in either plane.

## The component depth, and the gradient inequality that would have proved it

> **REFUTED, 2026-08-24 — see [ComponentDepthRefutation.md](ComponentDepthRefutation.md).**
> DEPTH-ALL is false at degree three. Three Gaussian rationals over `1000`, all
> strictly inside the open unit disk, with an acute triangle so `R^2` is an exact
> rational: at `theta = arg f(c*)` one of the two MERGING branches reaches
> `Delta/R >= 1.0071292`, as a rigorous inscribed-polygon lower bound at 60 dps,
> and the violation is robust (24/24 perturbations at `1e-4`, 18/24 at `1e-3`).
> The pair bound survives at that same witness — `L(c*)/2R = 0.98532` — so the two
> branches compensate and **the length budget does not split per branch**. That is
> `negative_results` entry 21 one level up, now about length rather than charge.
> Everything below is kept as written so the order of discovery stays legible;
> nothing else in this note depends on DEPTH-ALL, and `min_c L(c) <= 2R` is
> untouched.


At the first-merge level `μ = min_k|f(c_k)|` every component of `{|f| < μ}` holds
exactly one root, and `f` is a conformal bijection from it onto the disk `D_μ`.
Define the **depth** of a component, with no hub and no pair selection anywhere:

```text
Δ_j  =  max over θ of  length{ z : f(z) = t e^{iθ}, t ∈ [0,μ] }  ending at z_j.
```

Since the two branches at `c*` are two such curves, `L(c*) ≤ Δ_a + Δ_b`, so

> **`Δ_j ≤ R` for every `j`  ⟹  `L(c*) ≤ 2R < 2`  ⟹  Erdős #1041.**

It is *exactly* tight on both equality families. For **every** quadratic,
centring at the critical point gives `f = z² − h²`, `R = h`, `μ = h²`, and
`|h² + te^{iθ}| ≥ h² − t` shows the maximum is at `θ = π`, where

```text
Δ = ∫_0^{h²} dt / (2(h²−t)^{1/2}) = h = R      exactly, for every quadratic.
```

On `z^n − r^n` the same computation at `θ = π` gives `Δ = r = R` exactly.

**The inequality that would prove it, and why it fails.** Both equality
computations are one identity: `f − f(c) = (z−c)²` for a monic quadratic and
`f − f(c) = z^n` for `z^n − r^n`, so in both cases

```text
(GRAD-μ)     |f'(z)|  ≥  n·|f(z) − f(c)|^{(n−1)/n}       holds with EQUALITY.
```

Given (GRAD-μ), the branch has `|f(z)| = t ≤ μ` hence `|f(z) − f(c)| ≥ μ − t`, and

```text
Δ  ≤  ∫_0^μ dt / (n(μ−t)^{(n−1)/n})  =  μ^{1/n}  ≤  R,
```

which is the whole problem. **(GRAD-μ) is false.** Globally it fails at any other
critical point (`g = z²(z−M)` has `g' = 0` at `z = 2M/3` where `g ≠ 0`), and that
much is expected — the branch avoids other critical points, since they all carry
`|f| ≥ μ`. But it fails *on the sublevel set* too, from degree three:

| `n` | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|
| min `\|f'\| / (n\|f−f(c)\|^{(n−1)/n})` over `{\|f\| ≤ μ}` | **1.000000000** | 0.132745 | 0.104458 | 0.153498 | 0.136871 | 0.037069 |

Exactly `1` at every quadratic and on every `z^n − r^n`; as low as `0.037` at
degree seven. The failure mode is **clustered roots**: at a root `z_j` itself the
left side is `|f'(z_j)|`, which vanishes as two roots merge, while the right side
is `n μ^{(n−1)/n}` and does not. That does not endanger the depth — `μ` shrinks
with the cluster too, and `Δ_j ≈ μ/|f'(z_j)|` stays small — it only shows the
pointwise gradient bound is the wrong vehicle.

This is `negative_results` entry 17's lesson for the third time in one session:
**equality on `z^n − r^n` is exactly what makes a bound look canonical, and is not
evidence.** The other two instances today are the resolved local scale `κ` and the
`L²` area currency, both below.

**Status of `Δ_j ≤ R`, and the instrument check that makes the numbers mean
something.** Random sampling at `n = 2…6`, 270 configurations over uniform,
boundary-clustered and near-polygon families, found **no violation**: worst
`Δ/R = 1.000000`, attained at `n = 2` where equality is proved, with the
near-polygon rows climbing to `0.999245` at `n = 3` and `0.983982` at `n = 4`.

That is worth nothing on its own — entry 19 is exactly the lesson that a
supremum pinned just under a threshold is one basin. So the instrument was first
required to **reproduce a known refutation**: the strong form `Δ_j ≤ μ^{1/n}`
must fail, because entry 29 refutes `L(c*) ≤ 2μ^{1/n}` and `Δ_a + Δ_b ≥ L(c*)`.
A hill-climb drives `Δ/μ^{1/n}` to `1.012841837` at `n = 3` and `1.034203484` at
`n = 4`, so the instrument does detect violations of a bound of this shape and is
not silently under-reporting.

The receipt is [`scripts/check_erdos1041_component_depth.py`](scripts/check_erdos1041_component_depth.py),
and it **fails closed**: the validation is a *pinned* configuration
(`n = 3`, ratio `1.008092641`), not a search, because a hill-climb that finds no
violation cannot distinguish "the conjecture holds" from "the search budget was
too small" — which is exactly what happened on the first attempt at a light
budget, and the script correctly refused to report its DEPTH-ALL rows.

Two earlier versions of the instrument **were** under-reporting: a uniform θ
grid misses `θ = arg f(c)`, where the maximum sits, and returned `0.943664` for a
random quadratic against the proved exact value `1`. `z^n − r^n` concealed that
fault, because its `θ_c = π` lands on any symmetric grid.

Why the weak form can survive when the strong one does not: `μ^{1/n} = R` exactly
at the Fekete configuration and for *every* quadratic, so `Δ ≤ μ^{1/n}` has zero
slack wherever `z^n − r^n` lives, while `Δ ≤ R` carries the Fekete deficit
`R − μ^{1/n}` as its budget. Entry 35 records that the strong form is *not*
refuted near Fekete — it rises to `1` from below — so its refutations sit where
that deficit is strictly positive. Whether the excess is always inside the deficit
is precisely the open coupling, and it is the same "no uniform slack" phenomenon
entry 1 records.

**Reformulation, for whoever takes this next.** Writing `w = z − z_j` and
`δ_i = z_i − z_j`, the branch solves `w·∏_{i≠j}(w − δ_i) = t e^{iθ}` from `w = 0`,
so the depth is a statement about one polynomial with `n−1` prescribed offsets, all
of modulus `≤ 2R`, with no reference to `f` or to critical points at all.

## Two eliminations

**The resolved local scale is dead on arrival.** For a hub `c` of multiplicity `m`
the resolved coordinate `f(Z(ξ)) = f(c)(1 − ξ^m)` has `|Z'(0)| = κ(c)`,
`κ(c) = (m!|f(c)|/|f^{(m)}(c)|)^{1/m}`, and `Z(ξ) = rξ` is **linear** on both
equality families (`n = 2`, and `z^n − r^n` with `m = n`), where `κ = r` exactly
and `L(c) = 2κ(c)`. That makes `L(c) ≤ 2κ(c)` look canonical. It is refuted
without computation: writing `b_k = f^{(k)}(c)/k!`, the scale-robust form is
`κ(c) = min_{k≥2}(|f(c)|/|b_k|)^{1/k}`, and `b_n = 1` because `f` is monic, so

```text
κ(c) ≤ |f(c)|^{1/n},
```

hence `L(c) ≤ 2κ(c)` is strictly stronger than `L(c*) ≤ 2μ^{1/n}`, which
`negative_results` entry 29 refutes at degree four at ratio `1.004246913`. This is
entry 17's lesson again — equality on `z^n − r^n` is what makes a bound look
canonical, and is not evidence.

**A new member of the branch-tracking defect class, caught by certification.**
Lifting `z = (r^n + ρe^{iθ})^{1/n}` with a principal-branch `n`-th root is
discontinuous wherever the value circle passes near the origin, which is exactly
the regime of interest; the argument must be unwrapped continuously. Two errors,
compounding, both in the *safe-looking* direction:

* the principal branch **understated** the length — at `n = 20` it returned
  `1.18866` where the continuously unwrapped lift at the same `ρ` gives `1.33705`;
* `ρ = r^n(1+10⁻⁷)` **exceeds 1** when `r = 1−10⁻⁹`, so the path left the target
  lemniscate altogether. The admissible window is `r^n < ρ < 1`, whose width at
  that modulus cap is about `1.5·10⁻⁸`.

Both were caught by the same check — evaluate `f` directly at every sample and
require `max|f| < 1` together with distinct endpoint roots — which failed loudly
before any of it was written down. The corrected value at `n = 20` is `1.24249`.
**A construction is not a path until `f` has been evaluated on it.**

## Claim boundary

Proved: (A), (B), (C), (D), the Cauchy–Schwarz radial-trace consequence, (V1),
(V2), the reformulation, and `κ(c) ≤ |f(c)|^{1/n}`. (C) and (D) carry the
numerical receipt above; (A), (B), (V1), (V2) are ordinary arguments and the
numbers are checks, not the authority.

Not established: no length bound for the
descent arc, no
progress on (E) or (F), and nothing that touches the claim ceiling. Erdős #1041
remains open, and the obligation is still the componentwise combined-charge lemma.
