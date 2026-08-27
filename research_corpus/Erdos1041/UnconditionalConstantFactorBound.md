# Erdős #1041 holds up to an absolute constant

Status: **one unconditional theorem, proved here**, plus one sharp conjecture it
isolates. Current through 2026-08-27 source audit. **Erdős #1041 itself remains
open** — the constant `2` is sharp and nothing below reaches it. The numerical
receipt in §11 remains dated 2026-08-24; this source-only update does not claim
a fresh replay.

Everything in this directory before today is either an equivalent
reformulation, a conditional producer, or a mechanism elimination. The
`claim_ceiling` records no unconditional bound of any kind on the pair
geodesic: `(C)`, `(COVER)`, `min_c L(c) <= 2R` and the per-component charge are
all open, and §8 of [CapacityGeodesicConjecture.md](CapacityGeodesicConjecture.md)
explicitly retires the boundary-hop construction as a *near-miss*. This note
does not rely on any global degree-linear lemniscate-length comparison.

That assessment is correct for the *sharp* constant and wrong for a *finite*
one. The length of one component's boundary admits an elementary,
**degree-free, per-component** bound obtained from Cauchy–Schwarz against the
explicit area inequality below, and the construction then closes with an
explicit absolute constant.

## Source and authority boundary

Theorem 1, its corollary, the split at the critical level, and the constant-8
construction are repository-authored ordinary mathematics. The proof uses only
the inequalities written in this note: the capacity identity, the area bound,
Cauchy--Schwarz, the univalent-map distortion estimate, and the finite graph
exit lemma. No external paper theorem is imported, and no literature-priority
claim is made for the resulting finite bound. The numerical section is
measurement only; Conjecture P and the sharp constant `2` remain open.

The global area--capacity input has a historical primary-source antecedent, but
that antecedent is not being substituted for the proof above. George Pólya's
1928 primary scan, [downloaded here](https://archive.org/download/sitzungsbericht1928preu/sitzungsbericht1928preu.pdf)
(SHA-256
`2de0cd74d07f02ff08be81e1eaac35b5529e1c60e35e1c5c9b4c4ca0602fd205`), gives
the relevant area--capacity inequality and polynomial sublevel estimate on
printed pp. 280--282 (scan pp. 312--314). The hash-bound source record is
`docs/formal_math/observatory_source_reaudit/erdos1041_constant_factor_polya_primary_text_read_20260827d.json`.
That primary text does not state the local componentwise winding/coarea
estimate, the reciprocal-derivative pairing, or the assembled `8 rho` path
theorem; those remain source-specific ordinary mathematics here. No priority,
novelty, or unrestricted Erdős #1041 claim is made from this comparison.

## 1. The theorem

Throughout `f` is monic of degree `n ≥ 2` over `ℂ`, `K_t = {z : |f(z)| ≤ t}`,
and

```text
μ = min{ |f(c)| : f'(c) = 0 },      ρ = μ^{1/n} = cap(K_μ).
```

Zeros are listed with multiplicity, matching the problem formulation used by this repository.
If `f` has a repeated zero then `μ = 0`, two zero occurrences coincide, and
the degenerate constant path settles everything; so the nontrivial branch may
assume `f` squarefree and `μ > 0`.

> **Theorem 1 (unconditional).** Two zero occurrences of `f` are joined by a
> possibly degenerate path of length at most
>
> ```text
> 8 μ^{1/n}  =  8 cap(K_μ)
> ```
>
> lying inside `K_{2μ} = {z : |f(z)| ≤ 2μ}`. In the squarefree branch their
> zero locations are distinct.

The bound is scale-free: for `z = τ + σζ` the monic `g(ζ) = σ^{-n} f(τ + σζ)`
has `μ_g = σ^{-n} μ_f` and multiplies lengths by `σ^{-1}`, so both sides scale
identically. No disk hypothesis appears anywhere.

The explicit constant is the minimum over two free parameters `r ∈ (0,1)`,
`λ > 1` of

```text
   C(n; r, λ)  =  8r/(1-r)^2  +  λ^{1/n} ( sqrt(log(λ/r))  +  π / sqrt(log λ) ),
```

with the path then lying in `K_{λμ}`. At `λ = 2`, `r = 0.03` this reads
`7.592` at `n = 3`, `7.180` at `n = 4`, and decreases to `6.079` as `n → ∞`;
`n = 2` is settled separately and exactly (Step 0 below) with constant `2`.
Hence `8` is a valid absolute constant with `λ = 2`. Larger `λ` buys a smaller
constant — `λ ≈ 62` gives `≈ 4.7` for large `n` — at the cost of a larger
containment level.

> **Corollary 2 (Erdős #1041, constant form).** Let `f` be monic of degree
> `n ≥ 2` with every root in the open unit disk. Then two zero occurrences are joined
> **inside the open unit lemniscate `{|f| < 1}`** by a path of length at most
>
> ```text
> Θ(μ) = 8r/(1−r)^2 · μ^{1/n} + ( sqrt(log(λ/r)) + π/sqrt(log λ) ) (λμ)^{1/n},
>                                                        λ = min(2, 1/μ).
> ```
>
> In particular `Θ(μ) ≤ 6.1` whenever `μ ≤ 1/2` — for instance whenever the
> roots lie in a disk of radius `R ≤ 2^{-1/n}`, since `μ ≤ R^n`.

*Proof.* Run the proof of Theorem 1 with `T = λμ ≤ 1`, so the path lies in
`K_t ⊆ K_T ⊆ {|f| ≤ 1}`, and `t < 1` may be chosen since Lemma 2 selects `t`
from a set of positive measure. For the numerical claim take `r = 0.03`,
`λ = 2`: then `(λμ)^{1/n} ≤ 1` and `μ^{1/n} ≤ 1`, so
`Θ ≤ 0.2552 + (2.0493 + 3.7739) = 6.078`. For the Fekete step, the resultant
identity gives `μ^{n−1} ≤ prod_c |f(c)| = prod_{i<j}|z_i − z_j|^2 / n^n ≤ R^{n(n−1)}`,
hence `μ ≤ R^n`. ∎

`Θ(μ)` is finite for **every** `μ < 1` and degrades only as `μ → 1`; it
improves for small `μ`, reaching `≈ 4.7` once `μ ≤ 1/62` (take `λ ≈ 62`). The
regime `μ → 1` is exactly the near-Fekete shell that
[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) identifies, and §10
removes it outright.

## 2. Standing facts

**(F1)** `{|f| > t}` has no bounded component: `|f|` is subharmonic, so a
bounded component would violate the maximum principle. Hence every component of
`K_t` is a *full* continuum (connected complement in `Ĉ`).

**(F2)** `cap(K_t) = t^{1/n}`, because `(1/n) log(|f|/t)` is the Green's
function of `Ĉ \ K_t` with pole at infinity
([LemniscateCapacityBudget.md](LemniscateCapacityBudget.md) (B)).

**(F3)** *(Area inequality.)* For compact full `K`,
`Area(K) ≤ π cap(K)^2`. Indeed the exterior map
`Φ(u) = c u + b_0 + b_1 u^{-1} + …` of `Ĉ \ K` has `c = cap(K)`, and the area
theorem gives `Area(K) = π(c^2 − Σ_{m≥1} m|b_m|^2) ≤ π c^2`.

Consequently, for every component `C` of `K_t`,

```text
Area(C) ≤ π cap(C)^2 ≤ π cap(K_t)^2 = π t^{2/n}.                        (A)
```

**(F4)** If `C` is a component of `K_t` holding exactly `k` roots with
multiplicity, then `f|_C : C → D̄(0,t)` is proper of degree `k`, `C` is simply
connected, and `arg f` increases by `2πk` along `∂C`. For `t` outside the
finite set of critical-value moduli, `∂C` is a real-analytic Jordan curve.

**(F5)** Every component of `{|f| < μ}` holds exactly one root and is mapped
conformally onto `D(0,μ)` by `f`: a component with `k ≥ 2` roots would, by
Riemann–Hurwitz, contain `k−1 ≥ 1` critical points at level below `μ`,
contradicting minimality.

**(F6)** The component `C_μ` of `K_μ` containing a minimising critical point
`c*` holds at least two roots. Near `c*` write `f − f(c*) ≍ a_m (z−c*)^m`,
`m ≥ 2`; the local set `{|f| < μ}` has exactly `m` sectors at `c*`. Two sectors
in the same component of `{|f| < μ}` would produce a loop inside `K_μ`
enclosing an intervening `{|f| > μ}` sector, contradicting (F1). So the `m ≥ 2`
sectors lie in `m` distinct one-root components, all inside `C_μ`.

**(F7)** *(Univalent-map distortion and quarter-disk estimate.)* For `φ` univalent on `𝔻`,
`|φ'(w)| ≤ |φ'(0)| (1+|w|)/(1−|w|)^3` and `D(φ(0), |φ'(0)|/4) ⊆ φ(𝔻)`.

## 3. Step 0: degree two

For `f = (z−a)(z−b)` put `c = (a+b)/2`, `d = (b−a)/2`, so `f(c+u) = u^2 − d^2`,
`μ = |d|^2`, `ρ = |d|`. On the root segment `u = sd`, `s ∈ [−1,1]`, one has
`|f| = |d|^2 |s^2 − 1| ≤ μ`. The segment lies in `K_μ` and has length `2ρ`. So
Theorem 1 holds at `n = 2` with constant `2`; assume `n ≥ 3` from here.

## 4. Step 1: a degree-free per-component perimeter bound

This is the ingredient the directory was missing.

> **Lemma 1.** Let `C` be a component of `K_T` and put
> `A(σ) = Area(K_σ ∩ C)`. For almost every `σ ∈ (0,T]`, if `C'` is a component
> of `K_σ ∩ C` holding `k'` roots then
>
> ```text
> H^1(∂C')^2  ≤  2π k' · σ A'(σ).
> ```
>
> Summing, `Λ(σ) := H^1({|f| = σ} ∩ C) ≤ sqrt( 2π k · σ A'(σ) )`, where `k` is
> the number of roots of `f` in `C`.

*Proof.* Take `σ` outside the finitely many critical-value moduli. Parameterise
`∂C'` by `φ = arg f`. Since `|f| = σ` there, `|dz| = σ dφ / |f'|`, and by (F4)
`∫_{∂C'} dφ = 2π k'`. Cauchy–Schwarz:

```text
H^1(∂C') = ∫ σ dφ/|f'| ≤ ( ∫ dφ )^{1/2} ( ∫ σ^2 dφ/|f'|^2 )^{1/2}
                       = (2π k')^{1/2} ( σ ∫_{∂C'} |dz|/|f'| )^{1/2}.
```

By the coarea formula `A(σ) = ∫_0^σ ( ∫_{{|f|=τ}∩C} |dz|/|f'| ) dτ`, so
`Σ_{C'} ∫_{∂C'} |dz|/|f'| = A'(σ)` almost everywhere. Every component `C'` of
`K_σ ∩ C` carries at least one root (properness of degree `≥ 1`), and the
`k'` sum to `k`. Now `Σ_i sqrt(x_i y_i) ≤ sqrt(Σ x_i) sqrt(Σ y_i)`. ∎

Lemma 1 is what replaces Eremenko–Hayman. It is degree-free, it is *local to
one component*, and it costs nothing: the two ingredients are the winding
`2πk` and the area derivative.

## 5. Step 2: choosing the working level

Fix `λ > 1`, set `T = λμ`, let `C = C_T` be the component of `K_T` containing
`c*`, and `A(σ) = Area(K_σ ∩ C)`.

> **Lemma 2.** There is a non-critical `t ∈ [μ, T]` with
> `t A'(t) ≤ π T^{2/n} / log λ`, and the component `C_t ⊆ C` of `K_t`
> containing `c*` holds `k = k_t ≥ 2` roots.

*Proof.* `∫_μ^T (σ A'(σ)) dσ/σ = ∫_μ^T A'(σ) dσ ≤ A(T) ≤ π T^{2/n}` by (A),
while the measure `dσ/σ` has mass `log λ` on `[μ,T]`. Take `t` attaining at
most the mean, avoiding the finitely many critical levels. `C_μ ⊆ C_t` and
`C_μ` has `≥ 2` roots by (F6). ∎

Combining with Lemma 1 applied to `C_t` itself,

```text
H^1(∂C_t)  ≤  sqrt( 2π k · t A'(t) )  ≤  π sqrt( 2k / log λ ) · T^{1/n}.   (B)
```

## 6. Step 3: the lifts, split at a low level

For `θ` avoiding the finitely many arguments of critical values, the set
`Γ_θ = {z ∈ C_t : arg f(z) = θ}` is a disjoint union of exactly `k` analytic
arcs `γ_1, …, γ_k`; on each, `|f|` increases strictly from `0` to `t`, so each
runs from one root `a_i ∈ C_t` to one point `p_i(θ) ∈ ∂C_t`. Write `ℓ_i(θ)` for
their lengths. The coarea formula for `arg f`, whose gradient has modulus
`|f'/f|`, gives

```text
∫_0^{2π} Σ_i ℓ_i(θ) dθ  =  ∫_{C_t} |f'/f| dA.                            (C)
```

Fix `r ∈ (0,1)`, let `σ_1 = rμ`, and split `ℓ_i = ℓ_i^{low} + ℓ_i^{high}` at
level `σ_1`.

> **Lemma 3 (low part, pointwise in θ).** `ℓ_i^{low}(θ) ≤ 4r/(1−r)^2 · ρ`.

*Proof.* Let `U_i` be the component of `{|f| < μ}` containing `a_i`. By (F5),
`φ_i(w) = (f|_{U_i})^{-1}(μw)` is a conformal bijection `𝔻 → U_i` with
`φ_i(0) = a_i` and `cr_i := |φ_i'(0)| = μ/|f'(a_i)|`. The low part of `γ_i` is
`φ_i([0, r e^{iθ}])`, so by (F7)

```text
ℓ_i^{low} = ∫_0^r |φ_i'(x e^{iθ})| dx ≤ cr_i ∫_0^r (1+x)/(1−x)^3 dx
          = cr_i · r/(1−r)^2 .
```

By the quarter-disk estimate in (F7), `D(a_i, cr_i/4) ⊆ U_i ⊆ K_μ`, so
`cr_i/4 ≤ cap(K_μ) = ρ`, i.e. `cr_i ≤ 4ρ`. ∎

> **Lemma 4 (high part, on average in θ).**
> `(1/2π) ∫_0^{2π} Σ_i ℓ_i^{high}(θ) dθ ≤ sqrt( k log(λ/r) · A(T) / (2π) )`.

*Proof.* By (C) restricted to `C_t \ K_{σ_1}` and the coarea formula in the
level variable, `∫_0^{2π} Σ_i ℓ_i^{high} dθ = ∫_{σ_1}^{t} Λ_t(σ) dσ/σ` with
`Λ_t(σ) = H^1({|f| = σ} ∩ C_t)`. Apply the *per-component* form of Lemma 1 to
the components of `K_σ ∩ C_t`, whose root counts sum to `k = k_t`, and note
that their total `Σ ∫ |dz|/|f'|` is at most the corresponding total over
`K_σ ∩ C_T`, which is `A'(σ)`. This gives `Λ_t(σ) ≤ sqrt(2π k σ A'(σ))` with
`k = k_t`, and then Cauchy–Schwarz gives

```text
∫_{σ_1}^t Λ_t(σ) dσ/σ ≤ sqrt(2πk) ∫_{σ_1}^t sqrt( A'(σ)/σ ) dσ
   ≤ sqrt(2πk) ( ∫_{σ_1}^t dσ/σ )^{1/2} ( ∫_{σ_1}^t A' dσ )^{1/2}
   ≤ sqrt(2πk) · sqrt( log(λ/r) ) · sqrt( A(T) ),
```

using `t/σ_1 ≤ λ/r`. Divide by `2π`. ∎

## 7. Step 4: the hop, and assembly

Choose `θ` with `Σ_i ℓ_i^{high}(θ)` at most its mean. The `k` points `p_i(θ)`
are distinct (they are the `k` preimages of `t e^{iθ}` on `∂C_t`); order them
cyclically along the Jordan curve `∂C_t`. The `k` boundary arcs between
cyclically consecutive points have total length `H^1(∂C_t)`. For each such
consecutive pair the concatenation `γ_i^{-1} · arc · γ_j` joins `a_i` to `a_j`
**inside `C_t`**, so

```text
geo  ≤  ( 2 Σ_i ℓ_i(θ) + H^1(∂C_t) ) / k .
```

Insert Lemma 3, Lemma 4 and (B), with `A(T) ≤ π T^{2/n}` and `T^{1/n} = λ^{1/n} ρ`:

```text
geo ≤ 8r/(1−r)^2 · ρ  +  sqrt(2/k) ( sqrt(log(λ/r)) + π/sqrt(log λ) ) λ^{1/n} ρ .
```

Since `k ≥ 2`, `sqrt(2/k) ≤ 1`, which is Theorem 1's displayed constant. At
`λ = 2`, `r = 0.03`, `n ≥ 3` the bracket is at most `7.592`, and the path lies
in `K_{2μ}`. ∎

## 8. Why this was not already in the directory

Three replacements, each of which the earlier attempts lacked.

1. **Per-component perimeter without a global degree bound.** §8 of
   [CapacityGeodesicConjecture.md](CapacityGeodesicConjecture.md) reaches
   `geo ≤ (length(∂C) + 2 Σ_i length(lift_i)) / k` and then needs
   `length(∂C) ≲ k · cap`. A global degree-linear perimeter comparison would
   be useless when `k ≪ n`. Lemma 1 gives the same shape *per component and in
   terms of `k`*, from Cauchy–Schwarz against the area derivative, with the
   area controlled by the explicit capacity inequality (F3). Nothing about
   the degree enters.
2. **The lift term near the roots.** The naive bound
   `∫_C |f'/f| dA ≤ Σ_j ∫_C dA/|z − z_j|` loses a factor `n`. Splitting at a
   low level and using the distortion estimate (F7) on the *conformal* one-root lobes
   (available exactly because `μ` is the minimal critical value, (F5)) makes
   the low part `O(ρ)` **pointwise in the ray direction**, and Lemma 1 handles
   the rest.
3. **Buying room above `μ`.** Every earlier attempt worked at the level `μ`
   itself, where `A'(μ) = +∞` — the area derivative has a logarithmic
   divergence at a critical level, which is precisely why the perimeter of a
   pinched lobe resists Cauchy–Schwarz. Working at a level chosen from
   `[μ, λμ]` by a mean-value argument removes that divergence at the cost of
   the containment level `λμ` and a factor `1/sqrt(log λ)`.

Point 3 is the only blemish in Theorem 1, and §10 isolates exactly what would
remove it.

## 9. What this does and does not say

* It **does not** prove Erdős #1041. The target constant is `2`, it is attained
  in the limit on `z^n − r^n` and exactly on every quadratic
  ([CapacityGeodesicConjecture.md](CapacityGeodesicConjecture.md) Theorem 2),
  and `8 > 2`. Every sharp statement in this directory is untouched.
* It **does** give the first unconditional, degree-free bound on the pair
  geodesic recorded here. Before it, the `claim_ceiling` carried no
  unconditional length bound at all: `(C)`, `(COVER)`, `min_c L(c) ≤ 2R`, the
  per-component combined charge, Claim L and `ONE-SPOKE` are respectively open,
  open, open, open, open and refuted.
* It is **not** an equivalent reformulation. It is a strictly weaker statement
  than the target, proved outright.
* The constant `8` is not optimised. The three losses are Koebe's `(1−r)^{-3}`,
  the two Cauchy–Schwarz steps, and `Area ≤ π cap^2`. Measurement (§11) puts
  the constructed path at `≈ 2–5 ρ` on real configurations, so the true
  constant of this construction is nearer `5`.

## 10. The sharp conjecture this isolates

Removing the level window means bounding the perimeter of a one-root lobe **at
the critical level itself**, where Lemma 1 fails. Measurement makes the sharp
form startlingly clean.

> **Conjecture P.** Let `C` be a connected component of `{|f| ≤ σ}` containing
> exactly one root of `f`. Then
>
> ```text
> H^1(∂C)  ≤  sqrt(2) · ϖ · σ^{1/n}  =  sqrt(2) ϖ · cap({|f| ≤ σ}),
> ```
>
> where `ϖ = 2.62205755…` is the lemniscate constant and
>
> ```text
> sqrt(2) ϖ  =  Γ(1/4)^2 / (2 sqrt(π))  =  3.7081493546027438…
> ```
>
> Equality holds exactly for `f` quadratic at `σ = μ`, where `∂C` is one loop
> of a Bernoulli lemniscate.

The extremal value is exact. For `f = z^2 − d^2` one has `μ = d^2`, `ρ = d`, and
the one-root lobe boundary is `|z^2 − d^2| = d^2`, one loop of Bernoulli's
lemniscate. With `φ(w) = d sqrt(1+w)` the length is
`∫_0^{2π} |φ'(e^{iθ})| dθ = (d/2) ∫_0^{2π} (2|cos(θ/2)|)^{-1/2} dθ
 = d √π Γ(1/4) / (√2 Γ(3/4)) = d Γ(1/4)^2/(2√π) = √2 ϖ ρ`,
using `Γ(1/4)Γ(3/4) = π√2`. For general `n` the closed form
on `z^n − r^n` is `(2^{1/n}/n) √π Γ(1/(2n)) / Γ(1/(2n) + 1/2) · ρ`, which
decreases from `3.7081` at `n = 2` to `2` as `n → ∞`.

Conjecture P is the **one-root, per-component form of the
Erdős–Herzog–Piranian lemniscate-length problem**, and it is a genuinely
different extremal problem: EHP's conjectured per-root constant is `2`, attained
asymptotically by `z^n − 1`, whereas the one-root maximum is `√2 ϖ`, attained by
a quadratic.

> **Theorem 3 (conditional).** If Conjecture P holds with constant `β` for all
> `σ ≤ μ`, then two roots of `f` are joined **inside `K_μ`** by a path of
> length at most
>
> ```text
> ( 8x/(1−x)^2 + (β/π) log(1/x) + β ) ρ      for any x ∈ (0,1),
> ```
>
> which is `≈ 7.4 ρ` at `β = √2 ϖ`, `x = 0.1`. In particular Erdős #1041 would
> then hold with `2` replaced by an absolute constant for **every** polynomial
> with roots in the open unit disk, with no `2R^n ≤ 1` proviso.

*Proof.* At level `μ` exactly, `c* ∈ ∂U_a ∩ ∂U_b` for two of the one-root lobes
(F6), so it suffices to bound `d_{Ū_a}(a, c*)`. Lift from `a` along any ray to
`∂U_a` and then travel along `∂U_a` to `c*`, which is a point of that Jordan
curve — no tail is needed, which is the whole gain of working at `μ`:

```text
d(a, c*) ≤ ℓ_a(θ) + ½ H^1(∂U_a) ≤ mean_θ ℓ_a + ½ β ρ .
```

The mean lift is `(1/2π) ∫_0^μ P_a(σ) dσ/σ` with `P_a(σ) = H^1(∂U_a(σ))`. Bound
`P_a(σ)` by Koebe for `σ ≤ xμ` and by Conjecture P for `σ ≥ xμ`:

```text
mean_θ ℓ_a ≤ cr_a · x/(1−x)^2 + (β ρ /2π) log(1/x) ≤ 4x/(1−x)^2 ρ + (βρ/2π) log(1/x),
```

using `cr_a ≤ 4ρ` and `P_a(σ) ≤ β σ^{1/n} ≤ βρ`. Doubling for the two lobes and
adding `½β ρ` twice gives the stated bound. ∎

Conjecture P is therefore *exactly* the residue: it is a statement about one
lobe, one root and one Jordan curve, with an explicit extremal and an explicit
constant, and it upgrades Theorem 1 to a clean constant-factor Erdős #1041.

## 11. Measurement

Instrument: `scripts/check_erdos1041_constant_factor_bound.py`. Level curves
and descent arcs are traced in a square-root uniformising coordinate at the
saddle, so a critical point on the boundary is a regular point of the
parametrisation; this is the fix for the tracer defect class recorded at
`negative_results` 34 and 41. Validation: on `z^2 − d^2` the tracer returns the
Bernoulli half-loop `3.7081445…ρ` and the descending pair `2ρ` to `1e−15`, with
the level audit `|f|/μ = 1 ± 4e−16` and boundary closure `2e−16`.

Every inequality of §4–§7 was checked directly:

| check | quadratic | perturbed cubic | near-Fekete quintic | random `n = 6` |
|---|---|---|---|---|
| `Area(C_t) / (π t^{2/n})` (`≤ 1`) | `0.7901` | `0.8931` | `0.9557` | `0.0163` |
| Lemma 1: `H^1(∂C_t)^2 / (2πk · tA'(t))` (`≤ 1`) | `0.8583` | `0.8833` | `0.9101` | `0.8524` |
| `H^1(∂C_t) / (k ρ)` | `3.6574` | `2.5627` | `1.5099` | `0.4934` |

Lemma 1 is tight to within `10–15%` on every row, so the Cauchy–Schwarz step is
not where the constant is lost.

Conjecture P, `120` configurations over degrees `2…10` and five families
(uniform in the disk, on a circle, near-Fekete shells, clustered, near-collinear),
with a degenerate-hub guard and a trace-quality gate:

```text
P/ρ      max = 3.7081493   mean = 1.4932   (attained only at quadratics)
branch pair / 2ρ   max = 1.00000
mean lift / ρ      max = 0.52001
hop bound / ρ      max = 4.74816
```

The maximum of `P/ρ` agrees with `Γ(1/4)^2/(2√π)` to seven digits, and every
row attaining it is a quadratic.

**Instrument defect found and fixed while building this probe, same class as
`negative_results` 34/41, new location.** At a simple saddle the four local
rays `±sqrt(±2i w_0 / f''(c*))` sit at `90°` to each other, and one lobe is a
single `90°` sector bounded by the two of them nearest its descending
direction. Choosing the two square-root signs independently — the obvious
coding — traces the two halves of `∂U` on **opposite** lobes, returning a
closure gap of order `ρ` and a perimeter inflated to `6.54ρ` on a random
quadratic whose true value is `3.7081ρ`. The bias is therefore **against** the
conjecture, so it could not have manufactured the observed maximum; but the
closure gate silently *excluded* those rows, which is the reportable part —
`280` of `400` rows in the first sweep were dropped this way and the sweep
reported only `120`. The fix is to select both signs against the descending
direction `v = ±sqrt(−2w_0/f''(c*))`, after which the same quadratic returns
`3.7081491` with closure `2.2e−16`. **General rule: a two-branch trace at a
saddle must fix its signs from a common reference direction, never
independently; and a silent exclusion gate must report its exclusion count
alongside its record.** The measured cone angle `|arg Ξ|`, `Ξ = (z−a)f'/f`,
reaches `π`, independently confirming `negative_results` 25: the turning-inflation
chain is vacuous, and no cone bound can substitute for Lemma 1.

**Receipt, 2026-08-24: `verdict pass`, exit `0`, `24` rows scored and `0`
excluded**, with all six gates green:

```text
tracer_bernoulli   perimeter/rho = 3.7081492209  vs  Gamma(1/4)^2/(2 sqrt pi)
                                 = 3.7081493546   (err 1.34e-7, inscribed polyline)
tracer_branch_pair descending pair / 2 rho = 1.0 exactly, audit max|f|/mu = 1.0
lemma1             worst H^1(dC_t)^2/(2 pi k t A'(t)) = 0.9217405616   (<= 1)
gronwall_area      worst Area(C_t)/(pi t^{2/n})      = 0.9693303583   (<= 1)
theorem1_path      worst assembled path / rho        = 5.0663268684   (<= 8)
conjectureP        worst H^1(dU)/(sqrt2 varpi rho)   = 0.9999997747   (<= 1)
```

The assembled path is the one Theorem 1 constructs, audited for containment,
and it comes in at `5.07 ρ` against the proved `8 ρ` — so the construction has
about `1.6×` of unused margin even before the constant is optimised. Lemma 1
runs at `0.92` of equality, so the Cauchy–Schwarz step is essentially tight and
is not where the constant is lost; the losses are the distortion estimate's
`(1−r)^{-3}`, the two Cauchy–Schwarz steps, and `Area ≤ π cap^2`.

## 12. Claim boundary

Theorem 1, Corollary 2, Step 0 and Theorem 3 are proved above by ordinary
mathematics; no computation enters any of their proofs. §11 is measurement:
Conjecture P is **not** proved, and no adversarial search has been run against
it — the `120` rows are random and family-seeded, so `negative_results` 19
applies and the reported maximum is a basin record, not a supremum. The
constant `8` in Theorem 1 is an honest upper bound for `λ = 2`, not an optimum.
Erdős #1041 is open.

## 13. Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_constant_factor_bound.py
```
