# Erdős 1041: the capacity of a lemniscate component is exact, and the defect is a sum of Green's functions at the roots it excludes

Status: one exact theorem with an ordinary proof, one corollary that tightens a
landed theorem in this directory by two to five orders of magnitude on measured
configurations, one audited measurement, and one rediscovery reported against
myself. Current through 2026-08-27 replay. **Erdős #1041 remains open** and
nothing below claims otherwise. The near-Fekete shell is untouched.

## 1. What was being used, and what is true

[LemniscateCapacityBudget.md](LemniscateCapacityBudget.md) (B) proves
`cap(K_t) = t^{1/n}` exactly, and its (D) bounds a *component* only by
monotonicity:

> `C` is a continuum with `cap(C) ≤ cap(K_t) = t^{1/n}`

Every downstream use — (D)'s diameter bound, and the Pólya step
`Area(Ω) ≤ π t^{2/n}` that closes Theorem C of
[BergmanSegmentLengthBound.md](BergmanSegmentLengthBound.md) — spends that
inequality. It is an equality only when `{|f| < t}` is connected, and the
merge components the argument actually uses are never that. The exact value is
available, and it costs one maximum-principle argument.

> **Theorem 1 (component capacity).** Let `f` be monic of degree `n`, `t > 0`,
> `C` a connected component of `{|f| < t}`, and `Ω = Ĉ ∖ closure(C)`. Then
>
> ```text
> n log cap(closure C)  =  log t  −  Σ ,      Σ  :=  sum_{z_j not in C} g_Ω(z_j, ∞),
> ```
>
> the sum over the roots of `f` outside `C`, **with multiplicity**. Equivalently
>
> ```text
> cap(closure C)  =  t^{1/n} exp(−Σ/n) ,        Σ ≥ 0.
> ```
>
> `Σ = 0` exactly when `C` contains every root, i.e. exactly when `{|f| < t}` is
> connected — which recovers `cap(K_t) = t^{1/n}`.

*Proof.* Every component of `{|f| < t}` contains a root, and roots have
`|f| = 0 ≠ t`, so no root lies on `∂C`; the roots outside `C` lie in the open
set `Ω`. By (A) of `LemniscateCapacityBudget.md`, `{|f| > t}` has no bounded
component, so `Ω` is a connected domain containing `∞`, and `∂Ω = ∂C` is
contained in the analytic set `{|f| = t}`, hence regular for the Dirichlet
problem. Put

```text
u(z)  :=  log( |f(z)| / t )  +  sum_{z_j not in C} g_Ω(z, z_j) ,      z in Ω.
```

Near a root `z_j ∉ C` the two terms have singularities `log|z − z_j|` and
`−log|z − z_j|`, which cancel, so `u` is harmonic on `Ω ∖ {∞}`. On `∂Ω` both
terms vanish, so `u = 0` there. As `z → ∞`, `f` monic gives
`log(|f|/t) = n log|z| − log t + o(1)`, and each `g_Ω(z, z_j) → g_Ω(∞, z_j)`, so

```text
u(z)  =  n log|z|  −  log t  +  Σ  +  o(1).
```

The Green's function of `Ω` with pole at `∞` satisfies
`n g_Ω(z, ∞) = n log|z| − n log cap(closure C) + o(1)` and also vanishes on
`∂Ω`. Hence `h := u − n g_Ω(·, ∞)` is harmonic on `Ω ∖ {∞}`, bounded near `∞`
— so harmonic on all of `Ω` after removing the singularity — and zero on `∂Ω`.
By the maximum principle `h ≡ 0`. Reading `h(∞) = 0` gives

```text
−log t + Σ  =  −n log cap(closure C) ,
```

which is the statement, using `g_Ω(∞, z_j) = g_Ω(z_j, ∞)`. Positivity of `Σ` is
positivity of the Green's function on `Ω`. ∎

Nothing here is deep: it is the same maximum-principle move that proves
`cap(K_t) = t^{1/n}`, run without discarding the roots that sit outside. What it
buys is that the **loss is named**. `Σ` is large exactly when the excluded roots
are far from `C` in the conformal sense — which is the regime every merge
argument in this directory operates in.

## 2. What it tightens

`BergmanSegmentLengthBound.md` Theorem C bounds the descent arc at a critical
point `c`, with `v = |f(c)|` and `Ω_t` the level-`t` component at `c` holding
exactly two roots:

```text
L(c)  <=  sqrt( (2 Area(Ω_t)/π) · log((t+v)/(t−v)) )   <=   t^{1/n} sqrt( 2 log((t+v)/(t−v)) ),
```

the last step being Pólya. Its Theorem E turns that into: conjecture (C) of
[CapacityGeodesicConjecture.md](CapacityGeodesicConjecture.md) holds whenever
`t ≥ coth(1) v`, leaving one window per critical point of **relative width
`coth(1) − 1 = 31.30%`**. Corollary D likewise settles Erdős #1041 for `f` when
`v/t < tanh(1) = 0.7615942`.

Write

```text
kappa  :=  cap(Ω_t) / t^{1/n}  =  exp(−Σ/n)   ∈ (0, 1] .
```

`Area ≤ π cap²` for every compact set, with equality only for closed disks
(the isoperimetric inequality for capacity, already cited as the first half of
`LemniscateCapacityBudget.md` (D)). So `Area(Ω_t) ≤ π kappa² t^{2/n}` and:

> **Corollary 2.** In Theorem C's hypotheses,
>
> ```text
> L(c)  <=  kappa · t^{1/n} · sqrt( 2 log((t+v)/(t−v)) ) .
> ```
>
> Consequently (C) holds for `Ω_t` as soon as `v/t ≤ tanh(1/kappa²)`, and the
> Theorem E window at `c` has relative width `coth(1/kappa²) − 1` rather than
> `coth(1) − 1`. Corollary D's threshold for Erdős #1041 likewise moves from
> `tanh(1)` to `tanh(1/kappa²)`.

Both statements are affine-invariant for the same reason Theorem C is: `kappa`
is a ratio of two lengths that scale identically.

**This strictly dominates the Cassini sharpening** already in
`BergmanSegmentLengthBound.md` §3 ("an explicit area bound, when the other roots
are far", giving `Area ≤ π t / q_Ω` and `v/t < tanh(q_Ω/t)`). That bound is
capacity monotonicity applied to a Cassini oval containing `Ω_t`; Theorem 1 is
the capacity of `Ω_t` itself, so `cap(Ω_t) ≤ sqrt(t/q_Ω)` always and the two
agree only when the containing oval is `Ω_t`. Theorem 1 is optimal among all
capacity-based area bounds, because it is not a bound.

## 3. The measurement

Receipt: [`scripts/check_erdos1041_component_capacity.py`](scripts/check_erdos1041_component_capacity.py),
**`verdict pass`, exit `0`**, five gates green.

The receipt was replayed on 2026-08-27 against the current script and note.
The checker remains the authority for the numerical rows; it does not turn the
ordinary proof above into a Lean theorem or establish a bound on the open
Erdős problem.

The instrument is an equilibrium-measure solver: the boundary `∂C` is traced by
continuing `f(z) = t e^{iθ}` over `θ ∈ [0, 2πk)` for a `k`-sheeted component,
and the discretised Symm equation on that polygon returns `cap = e^{−λ}` and
`g_Ω(z, ∞) = λ − ∫ log(1/|z−w|) dσ(w)`. **Its resolution is measured, not
assumed**: arm `CAL` runs it on four sets of known capacity and every tolerance
below is set to ten times what `CAL` reports.

| arm | result |
|---|---|
| `CAL` | worst relative error `1.21e−04` (unit circle, `r = 0.37` circle, two ellipses) |
| `FORMULA` | worst `\|lhs − rhs\|` = `1.45e−04` over six configurations, one- and two-root components, against tolerance `1.21e−03` |
| `CONNECT` | `Σ = 0` reproduces `cap(K_t) = t^{1/n}` to `7.24e−05` at `n = 3,4,5` |

The `FORMULA` residual is `7.24e−05` on every one-root row and `1.45e−04` on the
two-root row — flat in the configuration and proportional to the sheet count.
That is the signature of the discretisation offset `CAL` already measured, not
of a defect in the identity.

Arm `KAPPA`, `12` first-merge two-root components at `t/v ∈ {1.05, 1.25}`:

| statistic | value |
|---|---|
| `kappa` median | `0.3891` |
| `kappa` max | `0.5811` |
| window width, median | `0.0006%` |
| window width, worst | `0.5370%` |
| against Pólya's | `31.30%` |

so on these rows Corollary 2 tightens the Theorem E window by between `58×` and
(at `kappa = 0.215`, `n = 5`) more than `10^14`.

**Disclosure, and it is the load-bearing one.** *Every surviving `KAPPA` row is
a bulk configuration.* The near-Fekete seeds in that arm produced no rows: at
`ε = 3e−2` and `3e−3` the merging-set classifier did not return exactly two
roots, or the level curve did not close on two sheets at the tested ratios. So
the measured `kappa ≈ 0.39` is **not** evidence about the near-Fekete shell,
which is where [HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) locates
the difficulty and where `kappa → 1` is exactly what the equality family
`z^n − λ` forces: there `{|f| < t}` is connected for `t > v`, so `Σ = 0`,
`kappa = 1`, and Corollary 2 degenerates to Theorem E. **The corollary is empty
precisely on the extremal family, which is correct — no bound may fire there —
and it is unmeasured on the shell around it.** Measuring it there needs a
classifier that survives the pinch, and is the obvious next step.

## 4. A rediscovery, reported against myself

Before finding `BergmanSegmentLengthBound.md`, this session derived the
level-`t` conformal normalisation (`Ω_t` is a disk, the degree-2 Blaschke
product has antipodal zeros of modulus `q = sqrt(v/t)`) and then bounded the
descent arc by Cauchy–Schwarz on the Taylor coefficients of `ψ'`, getting

```text
L(c)  <=  2 t^{1/n} sqrt( log( t/(t−v) ) ) ,     usable when v/t < 1 − 1/e = 0.6321 .
```

That is the same theorem with a worse constant: Lemma A of
`BergmanSegmentLengthBound.md` replaces the coefficient Cauchy–Schwarz by
Cauchy–Schwarz against the **Bergman reproducing kernel**, which is sharp, and
gets `tanh(1) = 0.7616` where the coefficient route gets `0.6321`. The two agree
to leading order as `q → 0` and the Bergman constant is better by a factor
approaching `2` in `Λ(q)` as `q → 1`.

This is the failure mode `AGENTS.md` item 4 warns about — a session re-deriving
landed entries because it read names rather than bodies — and it is recorded
here rather than quietly dropped. What survived the collision is Theorem 1,
which is upstream of both routes: it improves the *area input* they share, and
`BergmanSegmentLengthBound.md` reaches for exactly that improvement in its
Cassini paragraph.

## 5. Claim boundary

**Primary-source boundary (read 2026-08-27).** The only external attribution
used by this note for the area input is George Pólya, *Beitrag zur
Verallgemeinerung des Verzerrungssatzes auf mehrfach zusammenhängende Gebiete*,
Sitzungsberichte der Preussischen Akademie der Wissenschaften (1928), printed
pp. 280--282 (scan pp. 312--314), in the downloaded primary scan recorded at
[`erdos1041_constant_factor_polya_primary_text_read_20260827d.json`](../../../../docs/formal_math/observatory_source_reaudit/erdos1041_constant_factor_polya_primary_text_read_20260827d.json).
Its SHA-256 is
`2de0cd74d07f02ff08be81e1eaac35b5529e1c60e35e1c5c9b4c4ca0602fd205` and its
official archive PDF is
[`sitzungsbericht1928preu.pdf`](https://archive.org/download/sitzungsbericht1928preu/sitzungsbericht1928preu.pdf).
Those pages support the global area--capacity inequality for a polynomial
sublevel set. They do **not** state this note's componentwise Green-function
decomposition, local coarea--perimeter synthesis, or any length-below-two
conclusion. Theorem 1 and Corollary 2 therefore remain ordinary,
repository-authored arguments; no priority or novelty claim is made.

Theorem 1 is proved above by an ordinary maximum-principle argument and is
independent of every measurement. Novelty is not claimed against the potential
theory literature: it is the standard Green's-function decomposition of
`log|f|` on the complement of a sublevel component, and should be assumed known
until a priority search says otherwise. What is new **to this directory** is its
use: `LemniscateCapacityBudget.md` (D) and every consumer of Pólya spend
`cap(C) ≤ t^{1/n}`, and the deficit is nameable and large.

Corollary 2 is an implication from Theorem 1 into Theorem C of
`BergmanSegmentLengthBound.md` as read on 2026-08-24; that theorem's own proof
is not re-derived here and nothing above depends on it beyond its statement.

Everything in §3 is float measurement at a disclosed resolution. The `KAPPA`
rows are bulk configurations only. No claim is made about the near-Fekete shell,
about the merge level `t = v` itself (where Theorem C diverges and (C) is
tightest), or about the geodesic as against the descent arc. Erdős #1041 is
open; conjecture (C) is open.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_component_capacity.py
```
