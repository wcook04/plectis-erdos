# Erdős 1041: the capacity of a merging component is pinned at its merge level — an exact last-lobe law

Status: one new exact theorem with an ordinary proof, a multiplicity
generalization with an exact closed-form witness family, an audited measurement
at degrees 2–5, and two decision-changing consequences for the admissible-product
lane. 2026-08-28. **Erdős #1041 remains open** and nothing below claims
otherwise.

## 1. The statement

Throughout `f` is monic of degree `n ≥ 2`. Suppose there is a level `b > 0` and
a simple critical point `c_g` with `|f(c_g)| = b` such that, for `t < b` near
`b`, the set `{|f| < t}` has exactly two components: `U_t`, containing every
root of `f` except one, and `V_t`, a singleton lobe containing the remaining
root `z_n` with multiplicity `m ≥ 1`, and `Ū ∩ V̄ = {c_g}` where
`Ū = closure(∪_{t<b} U_t)`. (This is the generic "last merge hangs a single
lobe" configuration; `m = 1` is the squarefree case.)

> **Theorem (last-lobe law).** Under these hypotheses, with
> `Ω = Ĉ ∖ Ū` and `Φ : Ω → {|ζ| > C}` the exterior Riemann map tangent to the
> identity at infinity (`C = cap(Ū)`):
>
> ```text
> (i)   |Φ(z_n)| = C · (n+m)/(n−m),
> (ii)  g_Ω(z_n, ∞) = log((n+m)/(n−m))   ( = 2 artanh(m/n) · (1/m) · m … i.e.
>       for m = 1 exactly 2 artanh(1/n) ),
> (iii) cap(Ū)^n = b · ((n−m)/(n+m))^m,
> ```
>
> **independent of the configuration of the roots.** For the squarefree case
> `m = 1`:
>
> ```text
> cap(Ū)^n = b · (n−1)/(n+1),      g_Ω(z_n, ∞) = 2 artanh(1/n).
> ```
>
> Moreover the merge prevertex satisfies `Φ(c_g) = C · Φ(z_n)/|Φ(z_n)|`: the
> merge point sits on the exterior circle exactly aligned with the hanging
> root.

The striking content is the rigidity: the capacity of the big component at its
merge level is a universal multiple of the level, no matter where the `n−m`
enclosed roots sit. Contrast every prior capacity surface in this directory:
`LemniscateCapacityBudget.md` (D) gives only `cap ≤ t^{1/n}`, and
[ComponentCapacityFormula.md](ComponentCapacityFormula.md) Theorem 1 names the
deficit `Σ` but leaves it configuration-dependent. At the merge level, for a
single hanging lobe, the deficit is a **constant**.

## 2. The proof

Normalize `C = 1` by scaling the `ζ`-plane, and rotate so that
`ζ_n := Φ(z_n)` is real, `ζ_n = σ > 1` (strict since `z_n ∈ Ω` is open and
`|f(z_n)| = 0 ≠ b` keeps it off `∂Ω`).

**Step 1 (modulus identity).** On `Ω` put `u = log(|f|/b)`. It is harmonic on
`Ω ∖ {z_n, ∞}`, vanishes on `∂Ω ⊂ {|f| = b}`, grows like `n log|z| − log b`
at infinity, and has the singularity `m log|z − z_n| + O(1)` at `z_n`. The
function `n g_Ω(·, ∞) − m g_Ω(·, z_n)` has the same boundary values,
singularities and growth, so by the maximum principle they are equal.
(Reading the constant term at infinity re-derives
`n log cap(Ū) = log b − m g_Ω(z_n, ∞)`, which is
`ComponentCapacityFormula.md` Theorem 1 for this component; it is not new.)

**Step 2 (analytic completion).** Transporting through `Φ` and using the
exterior-disk Green's functions
`g(ζ, ∞) = log|ζ|`, `g(ζ, σ) = log|(ζσ − 1)/(ζ − σ)|`, the identity of Step 1
says that the holomorphic function `W := f ∘ Φ^{-1}` on `Δ* = {|ζ| > 1}`
satisfies

```text
|W(ζ)|  =  b |ζ|^n · ( |ζ − σ| / |ζσ − 1| )^m        on all of Δ*.
```

The right side is the modulus of the rational function
`T(ζ) = b ζ^n (ζ − σ)^m/(ζσ − 1)^m`, which is holomorphic on `Δ*` (its pole
`1/σ` lies inside the disk). Two holomorphic functions with equal modulus on a
domain differ by a unimodular constant, so `W = e^{iα} T` **exactly**. (At
infinity both grow like `ζ^n` after the tangent normalization, so the ratio is
also removable there.)

**Step 3 (the two critical points multiply to one).** `W` vanishes on `Δ̄*`
only at `ζ = σ`, so zeros of `W'` away from `σ` are zeros of

```text
W'/W  =  n/ζ + m/(ζ − σ) − m/(ζ − 1/σ),
```

i.e. of the quadratic

```text
P(ζ)  =  n ζ² − [ n(σ + 1/σ) − m(σ − 1/σ) ] ζ + n .
```

`P(0) = n ≠ 0`, `P(σ) = m(σ² − 1) ≠ 0`, `P(1/σ) = m(1 − 1/σ²) ≠ 0`, so no
spurious cancellation occurs, and — the load-bearing feature — **the product of
the two roots of `P` is `1`**.

**Step 4 (a merge forces a boundary double zero).** `|W| = b` on the unit
circle (boundary values of `Φ^{-1}` land on `∂Ω ⊂ {|f| = b}`), so `W` extends
meromorphically across the circle by Schwarz reflection, and the reflection
maps the level set `{|W| = b}` to itself. Let `ζ_g` be the prevertex of `c_g`
and let `k ≥ 1` be the vanishing order of `W − f(c_g)` at `ζ_g`. Near a point
of order `k`, the level set `{|W| = b}` consists of `k` analytic curves
crossing at equal angles, one of which is the unit circle, and by the
reflection symmetry the exterior half-neighborhood is cut into exactly `k`
sectors on which `|W| − b` alternates in sign.

Count those sectors in the `z`-plane. Near the simple saddle `c_g`, the level
set `{|f| = b}` is two curves crossing at right angles, giving four sectors:
two sublevel (one approached by `U`, the opposite by `V`) and two superlevel.
The set `Ω` contains three of the four — the `V` sector and both superlevel
sectors — and `Φ^{-1}` is a homeomorphism of boundary neighborhoods, so the
exterior side of the circle at `ζ_g` must show **three** alternating sectors:
superlevel, sublevel (the `V` lobe), superlevel. Hence `k = 3` and `W'`
vanishes at `ζ_g` **to order exactly 2**.

**Step 5 (rigidity).** A double zero of `P` on the unit circle with root
product `1` forces `ζ_g² = 1`. `ζ_g = −1` makes the bracket
`n(σ+1/σ) − m(σ−1/σ) = −2n` impossible for `σ > 1`, so `ζ_g = 1` and the
discriminant condition reads

```text
n(σ + 1/σ) − m(σ − 1/σ) = 2n    ⟺    n(σ − 1)² = m(σ² − 1)
                                ⟺    n(σ − 1) = m(σ + 1),
```

whose only root above `1` is `σ = (n+m)/(n−m)`. Conversely, if `P` had no
double zero on the circle its roots would be `ζ₀, 1/ζ̄₀`-type with one strictly
inside the disk, leaving at most one simple zero of `W'` on `|ζ| ≥ 1`; a
simple boundary zero of `W'` is impossible for a polynomial level
configuration (it would put a level-crossing at a smooth boundary point), and
no boundary zero at all contradicts the merge at `c_g`. This forces the double
zero, hence `σ = (n+m)/(n−m)`.

Then `g_Ω(z_n, ∞) = log σ` and `n log cap = log b − m log σ` give (ii), (iii).
∎

**Where each hypothesis is spent.** "Single hanging lobe" makes `u` have
exactly one finite pole, which is what collapses `W` to a three-parameter
rational function; a hanging component with two or more distinct roots
contributes one Blaschke-type factor per root, and the same argument then
yields one real **constraint** (the boundary double-zero condition) rather
than full rigidity — that constraint is an exact identity on every generic
merge and is recorded as an open tool in §5. "Simple `c_g`" fixes the sector
count `k = 3`; the coalesced limit (e.g. the rose below) is recovered by
continuity of capacity, not covered by the proof as written.

## 3. Exact witnesses and the measurement

**Closed-form family.** `f = (z² − 1)^m`, degree `n = 2m`: the top merge is at
`c_g = 0`, `b = |f(0)| = 1`, and `Ū` is the closed right petal of the
Bernoulli lemniscate `{|z² − 1| ≤ 1}` for every `m`. The law predicts
`cap^{2m} = ((2m−m)/(2m+m))^m = 3^{−m}`, i.e.

```text
cap( one petal of the Bernoulli lemniscate )  =  1/√3  =  0.577350… ,
```

consistently for every `m` — a nontrivial internal consistency check, since
`m` varies while the set does not.

**Measurement** (equilibrium-measure solver of
[ComponentCapacityFormula.md](ComponentCapacityFormula.md), calibrated
resolution `1.2e-4`; components at `t` just below `b`, so the measured values
sit slightly **below** the limit, as they must):

| configuration | prediction `cap^n/b` | measured |
|---|---|---|
| Bernoulli petal, exact boundary (`n=2`) | `1/3 = 0.33333` | `0.33175` |
| rose `z³−1`, 2 petals (coalesced limit) | `1/2` | `0.49905` |
| rose `z⁴−1`, 3 petals (coalesced limit) | `3/5` | `0.60023` |
| 3 random cubics, top merge, `t/b ≈ 0.9997` | `1/2` | `0.49836, 0.49831, 0.49791` |
| 3 random quartics, `(3)+(1)` top merge | `3/5 = 0.60000` | `0.59823, 0.59854, 0.59804` |
| 2 random quintics, `(4)+(1)` top merge | `2/3 = 0.66667` | `0.66498, 0.66558` |

The quartic row is the discriminating one: the exterior-Blaschke-style
alternative "the capacity gap is attained", i.e. `cap^n/b = 1/(n−1)`, predicts
`1/3 = 0.333` there and is off by a factor of `1.8`. The two laws agree only
at `n = 3`, which is why the phenomenon was first misread (see §4).

## 4. Consequence 1: the parent-aware capacity budget cannot repay the cubic graft

[AdmissibleCriticalArcProductLab.md](AdmissibleCriticalArcProductLab.md)
records the hybrid-graft falsifier: on a stress cubic, the proof template
"replace each certified cherry factor by its rigorous Bergman–Pólya bound
`sqrt(B_v)` and multiply" fails (`1.0755 > 1`), and the lab names the repair
target: "couple the cherry estimate to its parent component, or recover at
least one source of slack discarded by the separate Bergman,
exterior-capacity, and Pólya steps. A parent-aware area/capacity budget is now
a sharper target."

The last-lobe law closes that door for cubics, exactly. For any cubic, the
cherry's parent cut `b` is the top merge and the hanging set is the single
remaining root, so as `t ↑ b` the cherry component's capacity ratio is pinned:

```text
kappa := cap(U_t)/t^{1/3}  →  (1/2)^{1/3}  =  0.79370…  =  (n−1)^{−1/n} at n=3.
```

So at cubic graft levels the exterior-Blaschke gap `(n−1)^{−1/n}` that the
lab's `(CB1)` already spends is not an inequality with slack — it is the
**exact limit value**. The optimal area input (the exact component capacity,
"optimal among all capacity-based area bounds, because it is not a bound") can
therefore recover **nothing** at the parent cut. Measured on the falsifier:
the κ-coupled certificate `h_v ≤ κ_t · t^{1/n} sqrt(artanh(β/t)) / r^{1/n}`
reaches `0.51416` against the lab's `0.51413`, where repaying the graft needs
`0.47805` — a `7%` gap that is now known to be structural, not numerical.
Receipt: [scripts/check_erdos1041_parent_aware_capacity_budget.py](scripts/check_erdos1041_parent_aware_capacity_budget.py).

**What survives.** The Bergman pairing step is now the only lossy step left in
the cherry chain at parent-adjacent levels (`28%` overshoot on the falsifier
against the actual factor). A repair must either sharpen the Bergman
`L²`-pairing itself using the degree-2 Blaschke structure of the cherry
component, or abandon the multiplicative hybrid for the additive `PGLS`
slack currency, which this note does not touch.

## 5. Consequence 2: a boundary rigidity tool for merge configurations

The proof mechanism — modulus identity, analytic completion to an explicit
rational exterior model, and the forced boundary double zero — yields one real
exact constraint at **every** generic two-component merge, rigid or not: with
`Ω` the complement of one merging half and `ζ_j = Φ(z_j)` the exterior
coordinates of the roots outside it,

```text
W(ζ) = e^{iα} b (ζ/C)^n ∏_j [ C(ζ − ζ_j) / (ζ ζ̄_j − C²) ],
```

and `W'` must have a **double** zero at some `|ζ| = C`. For a single outside
root this pins `|ζ_n|/C = (n+1)/(n−1)` (the theorem). For several outside
roots it is an exact polynomial identity coupling their exterior positions —
a "polynomial-coupled boundary-access" relation of exactly the kind the
2026-08-28 assimilation names as the missing ingredient
(`TypeBReturnAssimilation20260828.md`, "Cross-return composition and updated
residual"). Whether the first-merge (singleton+singleton) version of this
constraint can be spent against the two-lobe boundary-access residual is open
and is the natural next question for this lane.

Two immediate quantitative corollaries of the theorem worth recording:

* **Capacity jump at a last merge is universal:** crossing the merge level,
  `cap` jumps from `(b(n−1)/(n+1))^{1/n}` to `b^{1/n}` when the merged set is
  all of `K_b` — a factor `((n+1)/(n−1))^{1/n}`, independent of everything.
* **The hanging root's conformal distance is pinned:** `|Φ(z_n)| = C(n+1)/(n−1)`,
  so in Green's metric the last root sits at distance exactly `2 artanh(1/n)`
  from infinity's normalization — for large `n` this decays like `2/n`, the
  same scale as the adjacent-root gap in the near-Fekete regime.

## 6. Claim boundary

The theorem and its multiplicity generalization are repository-authored
ordinary mathematics proved in §2; the proof uses only the maximum principle,
the exterior Riemann map, boundary reflection, and the local structure of
level sets at a simple saddle. **No novelty is claimed against the potential
theory literature**: the modulus-identity and reflection techniques are
classical, and the statement should be assumed known until a priority search
says otherwise. What is new **to this directory** is the statement itself, the
rigidity reading, and both consequences in §4–§5.

The measurement in §3 is float at the solver's calibrated resolution and is
consistency evidence, not part of the proof. The rose rows sit outside the
theorem's simple-saddle hypothesis (coalesced limit) and are reported as
continuity evidence only.

Nothing here proves `(AP)`, `(MS)`, `(CAQ)`, `PGLS`, `(C)`, COVER, or the
parent theorem. **Erdős #1041 remains open.**

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_last_lobe_capacity_law.py
python3 research_corpus/Erdos1041/scripts/check_erdos1041_parent_aware_capacity_budget.py
```
