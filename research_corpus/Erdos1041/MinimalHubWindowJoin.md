# Erdős #1041: the minimal-hub window joins two roots inside `{|f| ≤ μ}`

Status: one unconditional theorem, assembled here from one directory-proved
estimate plus two short lemmas proved below, 2026-08-24. **Erdős #1041 remains
open** — nothing below reaches the constant `2` except where it is already
exact. What is new is the *containment*: every previously recorded
unconditional join pays for its constant with a larger level set, and this one
does not.

## 0. What was blocked

Two unconditional statements about joining roots are on file.

[UnconditionalConstantFactorBound.md](UnconditionalConstantFactorBound.md)
Theorem 1 joins two roots by a path of length at most `8 μ^{1/n}`, but the
path lives in `K_{2μ} = {|f| ≤ 2μ}`, and its own §10 shows that moving the
containment down to `K_μ` costs either Conjecture P (open) or nothing at all.
Its Corollary 2 reaches the unit lemniscate only under the proviso
`2R^n ≤ 1`.

[BergmanSegmentLengthBound.md](BergmanSegmentLengthBound.md) Theorem C bounds
the descent arc at any critical point `c`, `v = |f(c)|`, whenever some level
`t > v` has a two-root component at `c`; §3b of that file turns this into
windows `[v_i, coth(1) v_i)` for the capacity conjecture `(C)` and records
that the endpoint `t = v_i` itself stays open.

What neither statement records is the combination that matters for Erdős
#1041 itself. Theorem C's arc **lies in `{|f| ≤ v}`** — that is verbatim part
of its conclusion, independent of the auxiliary level `t`. At the
*minimising* critical point `v = μ`, so the arc is a root-to-root path inside
`{|f| ≤ μ}` — the exact containment Theorem 1 cannot reach — and the
auxiliary level `t` enters the length through a factor that is **decreasing**
in `t`. So the whole game is how far the two-root stage persists, and the
price of degeneracy is paid in the constant only, never in the containment.

## 1. Standing facts

Throughout, `f` is monic of degree `n ≥ 2` with distinct roots,
`K_t = {|f| ≤ t}`,
`μ = min{|f(c)| : f'(c) = 0}`, and `c*` a critical point attaining `μ`.
From [UnconditionalConstantFactorBound.md](UnconditionalConstantFactorBound.md)
§2 we use (F1)–(F7) unchanged; from
[BergmanSegmentLengthBound.md](BergmanSegmentLengthBound.md) we use Theorem C
verbatim, with its proof status ("proved, by ordinary mathematics", §7 of that
file):

> **Theorem C (quoted).** Let `c` be a critical point, `v = |f(c)| > 0`, and
> `t > v` a level whose component `Ω` of `{|f| < t}` containing `c` holds
> exactly two roots `a, b`. Then the descent arc `Γ` at `c` joins `a` to `b`,
> **lies in `{|f| ≤ v}`**, and
>
> ```text
> length(Γ)  ≤  sqrt( (2 Area(Ω)/π) · log((t+v)/(t-v)) )
>            ≤  t^{1/n} · sqrt( 2 log((t+v)/(t-v)) ).
> ```

One structural fact about the window is needed, and it is elementary.

> **Lemma 1 (two-root persistence).** Suppose `c*` is simple. Then the
> component `Ω_t` of `{|f| < t}` containing `c*` holds exactly two roots for
> every `t ∈ (μ, T*)`, where
>
> ```text
> T*  :=  sup{ t > μ : Ω_t holds exactly two roots }  ∈  (μ, +∞].
> ```
>
> Moreover `T* ≥ ν`, the smallest critical-value modulus strictly greater
> than `μ` (`T* = +∞` only when `n = 2`).

*Proof.* At a simple critical point the local model of `{|f| < μ}` has
exactly two sectors meeting at `c*` ((F6) with `m = 2`), lying in two one-root
lobes ((F5)); for `t > μ` those two lobes are joined through `c*`, so `Ω_t`
holds exactly two roots for all `t > μ` sufficiently close to `μ`. Root counts
of components are non-decreasing in `t` and jump only when the boundary
crosses a critical point of `f` (a component of `{|f| < t}` changes at level
`|f(c)|` for a critical point `c`); hence the set of levels with exactly two
roots is an interval `(μ, T*)`. Since no component can change before the next
distinct critical-value modulus `ν`, the interval reaches at least `ν`, so
`T* ≥ ν`; it may persist beyond `ν` when that critical level belongs to another
component. For `n = 2` there is a single critical point, `ν` does not exist, and
`Ω_t` holds both roots for every `t > μ`, so `T* = +∞`. ∎

## 2. The window factor decreases

> **Lemma 2.** For `n ≥ 2` and `x > 1` put
> `Ψ_n(x) = x^{1/n} · sqrt( 2 log((x+1)/(x-1)) )`. Then `Ψ_n` is strictly
> decreasing on `(1, ∞)`, with
>
> ```text
> Ψ_n(x) ~ sqrt( 2 log(2/(x−1)) )   as x → 1⁺ ,
> lim_{x→∞} Ψ_2(x)  =  2 ,      lim_{x→∞} Ψ_n(x) = 0  for n ≥ 3 .
> ```

*Proof.* Substitute `x = coth u`, `u > 0`. Then
`(x+1)/(x-1) = e^{2u}` exactly, so
`Ψ_n(x)^2 = 4u·coth(u)^{2/n}`, and

```text
d/du log Ψ_n(coth u)^2
  =  1/u + (2/n)·(coth′u / coth u)
  =  1/u − (2/n)·1/(sinh u · cosh u)
  =  1/u − 4/(n · sinh(2u))  >  0 ,
```

because `sinh(2u) > 2u` gives `4/(n·sinh(2u)) ≤ 2/(n·u) ≤ 1/u`, strictly for
every `u > 0`. So `Ψ_n(coth u)` increases in `u`, hence `Ψ_n` decreases in
`x`; the displayed asymptotics are the cases `u → ∞` (`x → 1⁺`) and `u → 0`
(`x → ∞`, using `coth u ~ 1/u`). ∎

(In particular the divergence at `x → 1⁺` is `Ψ_n(x) ~ sqrt(2 log(2/(x−1)))`
— slow, and that slowness is what §4 buys.)

## 3. The theorem

> **Theorem 1 (minimal-hub join, unconditional on its hypotheses).** Let `f`
> have a simple minimising critical point `c*` (so `μ > 0`), and let
> `T* ∈ (μ, +∞]` be the two-root persistence level of Lemma 1. Then two roots
> of `f` are joined by a path **inside `{|f| ≤ μ}`** — hence inside `K_μ`,
> and inside the unit lemniscate whenever `μ ≤ 1` — of length at most
>
> ```text
> L  ≤  inf_{μ < t < T*}  t^{1/n} sqrt( 2 log((t+μ)/(t-μ)) )
>     =  T*^{1/n} · sqrt( 2 log((T*+μ)/(T*−μ)) )          (T* < ∞)
>     =  2 μ^{1/n}                                        (T* = ∞, n = 2),
> ```
>
> and, with the area form of Theorem C kept un-Pólya'd,
>
> ```text
> L  ≤  inf_{μ < t < T*}  sqrt( (2 Area(Ω_t)/π) · log((t+μ)/(t−μ)) ).
> ```

*Proof.* Fix any `t ∈ (μ, T*)`. By Lemma 1 the component `Ω_t` holds exactly
two roots, so Theorem C applies at `c = c*`, `v = μ`: the descent arc joins
those two roots, lies in `{|f| ≤ μ}`, and its length is at most
`t^{1/n}√(2 log((t+μ)/(t−μ)))` and at most the displayed area form. Take the
infimum over `t`; by Lemma 2 the Pólya-form integrand is decreasing, so the
infimum is the limit at `T*`, finite for `T* > μ` and equal to `2μ^{1/n}` in
the case `T* = ∞` (only `n = 2`). ∎

**Scale covariance** is inherited from Theorem C (that file's remark after
Corollary D): under `z ↦ τ + σζ` lengths scale by `σ`, `μ` by `σ^n`, and
`T*/μ`, `Ψ_n` are invariant. No disk hypothesis appears anywhere; the
`R ≤ 2^{-1/n}` proviso of UnconditionalConstantFactorBound Corollary 2 has no
analogue here.

## 4. Corollaries

> **Corollary 2 (generic window).** If `T* ≥ coth(1)·μ`, i.e. the second
> relevant critical value exceeds `μ` by more than `31.3%`, then
>
> ```text
> L  ≤  √2 · coth(1)^{1/n} · μ^{1/n}  ≤  1.55 μ^{1/n}   (all n ≥ 2),
> ```
>
> attained in the worst case at `n = 3`, decreasing to `√2 μ^{1/n}`
> as `n → ∞`. The path is inside `{|f| ≤ μ}`.

This recovers the *content* of the `coth(1)` window of
[BergmanSegmentLengthBound.md](BergmanSegmentLengthBound.md) Theorem E at the
minimal hub, but routes it differently: that file spends the window on the
level (proving `(C)` above `coth(1) v_i`); here the window buys a *constant*
for a join that never leaves `K_μ`.

> **Corollary 3 (quadratic exactness).** For every monic quadratic, Theorem 1
> gives `L ≤ 2 μ^{1/2}` with the path in `{|f| ≤ μ}`, and the true value is
> `2 μ^{1/2}` (the root segment, Step 0 of
> [UnconditionalConstantFactorBound.md](UnconditionalConstantFactorBound.md)).
> The bound is therefore **exactly optimal on the full quadratic equality
> family**, not merely asymptotically — the same sharpness the Bergman file
> calibrates at §4, reached here without taking `t → ∞` against a budget.

> **Corollary 4 (master bound, dominating Theorem 1 everywhere).** Every
> squarefree monic `f` admits two roots joined by a path of length at most
>
> ```text
> min( 8 μ^{1/n}  inside K_{2μ} ,    Ψ_n(T*/μ) μ^{1/n}  inside K_μ )
> ```
>
> where the first alternative is Theorem 1 of
> [UnconditionalConstantFactorBound.md](UnconditionalConstantFactorBound.md)
> (valid with no hypotheses beyond squarefree-ness after its repeated-root
> reduction) and the second is Theorem 1 above (valid at simple minimal hubs;
> at a multiple minimiser no two-root stage exists at `c*` and the first
> alternative governs). The second alternative is the smaller one whenever
>
> ```text
> T*/μ  −  1  >  2 e^{−32}  ≈  1.7 · 10^{−14}   (worst case n = 3),
> ```
>
> by `Ψ_3(x) < 8 ⇔ 4u·coth(u)^{2/3} < 64` with `x = coth u`, using
> `coth u ≤ 1 + 2e^{−2u}` and solving for `u`. Only when the second distinct
> critical-value modulus exceeds `μ` by less than a factor
> `1 + 1.7·10^{−14}` does the fallback dominate — and even there the two
> alternatives agree to within the constant while the containment still
> improves from `K_{2μ}` to `K_{μ(1+δ)}` for every `δ < T*/μ − 1`.

*Proof.* Immediate from Theorem 1, Lemma 2, and the displayed estimate;
the `coth` bound used is `coth u − 1 = 2/(e^{2u} − 1) < 2e^{−2u}`. ∎

> **Corollary 5 (spectral settling criterion).** Let `f` be monic,
> squarefree, all roots in the closed disk of radius `R`, with a simple
> minimising critical point. Let `ν₂` be the second-smallest distinct
> critical-value modulus, and define `x_n*` by
>
> ```text
> Ψ_n(x_n*) = 2        (unique solution on (1, ∞);  x_2* = +∞).
> ```
>
> If `ν₂ / μ > x_n*`, then Erdős #1041 holds for `f`: two roots are joined
> **inside `{|f| ≤ μ}`** by a path of length `< 2R`.
>
> Computed thresholds (`Ψ_n(coth u)² = 4u·coth(u)^{2/n}`, so `Ψ_n(x_n*) = 2
> ⟺ u·coth(u)^{2/n} = 1` at `x_n* = coth u`; bisection residual `< 5·10^{-16}`):
>
> | `n` | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 10 |
> |---|---|---|---|---|---|---|---|---|
> | `x_n*` | `∞` | `1.6064943…` | `1.4784372…` | `1.4289343…` | `1.4023941…` | `1.3857936…` | `1.3744142…` | `1.3598081…` |
>
> strictly decreasing in `n`, tending to `1`.

*Proof.* Component root-counts are locally constant off the critical-value
moduli (Lemma 1's proof), and right above `μ` the count is `2`, so
`T* ≥ ν₂`; the hypothesis gives `Ψ_n(T*/μ) ≤ Ψ_n(ν₂/μ) < 2`. Theorem 1
delivers the join inside `{|f| ≤ μ}` with length `≤ Ψ_n(T*/μ)·μ^{1/n}`, and
the Fekete–Vandermonde chain of
[UnconditionalConstantFactorBound.md](UnconditionalConstantFactorBound.md)
Corollary 2 (`μ^{n−1} ≤ Π_c |f(c)| = Π_{i<j}|z_i−z_j|²/n^n ≤ R^{n(n−1)}`,
using `Π_{i<j}|z_i−z_j| ≤ n^{n/2}R^{n(n−1)/2}` attained by the regular
`n`-gon) gives `μ ≤ R^n`, hence `L < 2R`. Uniqueness of `x_n*` is Lemma 2's
strict monotonicity; `Ψ₂(x) ↓ 2` strictly from above makes `x₂* = ∞`, which
is the required behaviour — on quadratics the true geodesic *equals* `2R`
exactly, so no strict criterion may fire there. ∎

> **Corollary 6 (compositional pullback).** Let `P` be monic of degree
> `n ≥ 2` with `P'(0) ≠ 0`, let `μ_P` and `ν₂^P` be its smallest and
> second-smallest distinct critical-value moduli, and fix `q ≥ 2` and
> `h ∈ ℂ`. If
>
> ```text
> min( ν₂^P , |P(0)| )  >  x_n* · μ_P ,
> ```
>
> then `f(z) := P((z−h)^q)` satisfies Erdős #1041: two of its zeros are joined
> **inside `{|f| ≤ μ_f}`** by a path of length `< 2R_f`, where `R_f` is the
> smallest radius of a disk containing all `nq` zeros of `f` (`R_f = R^{1/q}`
> when `P`'s zeros lie in a disk of radius `R` about `h`). Since
> `x_N*` decreases in `N` and `x_{nq}* ≤ x_n*`, the weaker gap against
> `x_n*` suffices.

*Proof.* `f'(z) = q(z−h)^{q−1}·P'((z−h)^q)`, so the critical points of `f`
are `z = h` (value `P(0)`) together with the `q` lifts `z = h + ξ^{1/q}` of
each critical point `ξ` of `P` (values `P(ξ)`); the hypothesis gives
`|P(0)| > μ_P`, so the minimiser of `f` is a lift of a simple critical point
of `P`, hence simple, with `μ_f = μ_P`. The distinct critical-value moduli of
`f` are those of `P` together with `|P(0)|`, so
`ν₂^f = min(ν₂^P, |P(0)|) > x_{nq}*·μ_f`. Zeros of `f` solve
`(z−h)^q = ρ`, so `R_f = R^{1/q}` and Corollary 5 applied to `f` (degree
`N = nq`) delivers the join with length `< 2R_f`. ∎

This is the spectral-route counterpart of composition families: it needs no
spoke selector and no shape restriction on `P` beyond the gap, and it covers
every degree `n ≥ 4` — where selector-based routes currently stop — provided
`P`'s own critical spectrum is separated enough relative to `x_n*`.

## 5. Relation to what is on file

* Against **Theorem 1** of `UnconditionalConstantFactorBound.md`: strict
  improvement in containment (`{|f| ≤ μ}` versus `{|f| ≤ 2μ}`) and, outside
  the astronomically degenerate stratum of Corollary 4, in constant as well.
  Its Conjecture P route to `K_μ` (Theorem 3 there, conditional) would give
  `≈ 7.4 ρ` inside `K_μ`; Corollary 2 is unconditional and smaller wherever
  it fires.
* Against **Theorem E / Corollary D** of `BergmanSegmentLengthBound.md`: same
  engine, different spend. There the window `t/v ≥ coth(1)` proves the
  capacity conjecture `(C)` *at level `t`*; the endpoint `t = v` is recorded
  open, correctly, because `(C)` at the merge level asks for length
  `≤ 2 cap` with no room. Here the arc's own containment (`{|f| ≤ v}`, part
  of Theorem C's conclusion) is promoted to the payload at the minimal hub:
  the join is delivered inside `K_μ` for **every** window position, including
  ones `(C)`-at-level reasoning cannot touch. Nothing here contradicts or
  re-proves anything in that file.
* Against the **near-Fekete shell**: `NearFeketeCuspLaw.md` splits the
  multiplicity-`(n−1)` hub so that consecutive critical values separate by
  `O(ρ^n)`; at a *simple* nearby minimiser this makes `T*/μ − 1 = O(ρ^n)` and
  `Ψ_n(T*/μ) ~ sqrt(2n log(1/ρ) + O(1))` — degradation like `sqrt(n)`, never
  a failure of containment. On the extremal family `z^n − r^n` proper the
  minimiser is multiple, Theorem 1 is silent by design, and the truth
  (`2μ^{1/n}` through the origin spokes) is carried by the equality family
  itself.
* Negative results checked before writing: entries 22, 25, 28, 29, 38 of
  `research_packet.json -> negative_results` bear on hub selection, spoke
  bounds, and per-lobe halving; none applies. Entry 28 refutes `L(c*) ≤ 2ρ`;
  Corollary 2 claims only `≤ 1.55 μ^{1/n}` at `n ≥ 3` and `2μ^{1/n}` at
  `n = 2`, both compatible with the recorded ratio `1.004246913`.

## 6. What this does not say

* It does **not** prove Erdős #1041: on the quadratic family the target and
  the bound coincide at `2μ^{1/n}`, and no degree reduces below `2` here.
* It does **not** touch the merge-level endpoint for conjecture `(C)`
  (length `≤ 2 cap(K_μ)` inside the component at level `μ`); the constant
  delivered at small windows is unbounded, and rightly so.
* It does not require, use, or advance Conjecture P; the one-root lobe
  perimeter at the critical level remains open exactly as recorded in
  `UnconditionalConstantFactorBound.md` §10–12.
* Multiple minimising hubs: if `c*` has multiplicity `m ≥ 2` the two-root
  stage never occurs at `c*` (its `m+1` lobes merge at once), and Theorem 1
  is vacuous there; Corollary 4's fallback covers that stratum, and if
  another *simple* critical point ties `μ` the theorem applies at it
  unchanged.

## 7. Measurement

Instrument:
[`scripts/check_erdos1041_minimal_hub_window.py`](scripts/check_erdos1041_minimal_hub_window.py),
reusing the calibrated tracer of
[`check_erdos1041_constant_factor_bound.py`](scripts/check_erdos1041_constant_factor_bound.py)
(square-root uniformisation at the saddle; `negative_results` 24/34/41
guards). Fail-closed arms:

* `MONO` — Lemma 2's monotonicity and limits against high-precision quadrature
  of `Ψ_n` at sample degrees;
* `QUAD` — quadratic family: `inf_t` of the window factor equals `2 μ^{1/2}`
  to `1e-9` relative, and the traced descending pair returns exactly
  `2 μ^{1/2}` with containment audit `max|f|/μ = 1 + O(1e-15)`;
* `WINDOW` — over random and family-seeded configurations (`n = 2…8`): locate
  `T*` by bisection on the two-root witness (root count `k = 2` **and**
  exactly one critical point inside the traced component, per the
  critical-point-count rule of BergmanSegmentLengthBound §5), then verify the
  descended pair satisfies `L ≤ bound(t_eval)` at a safely interior level and
  `L ≤ Ψ_n(T*/μ)·μ^{1/n}`, with `max|f| ≤ μ(1+1e-9)` audited along every
  traced arc;
* `DEGEN` — forced near-degeneracy: two separated saddle pairs tuned so
  `T*/μ − 1 ≈ 10^{-3}` and `10^{-4}` (gated), with `10^{-6}` attempted
  report-only (its merge neck is at grid resolution; an unresolvable level is
  receipted as unresolved, never scored); confirm containment survives and
  the measured constant tracks `sqrt(2 log(2/(T*/μ−1)))`;
* `THRESH` — Corollary 5's table: bisection for `x_n*` at `n = 2…10`,
  residual `|Ψ_n(x_n*) − 2| < 5·10^{-16}` each, and strict monotone decrease
  in `n`, with `x₂* = ∞` (no crossing below `64`);
* `PULLBACK` — Corollary 6's spectrum identity on random
  `f = P((z−h)^q)` (`n = 3…5`, `q = 2…4`): the distinct critical-value moduli
  of `f` equal `{|P(ξ)|} ∪ {|P(0)|}` to `< 10⁻⁷` relative.

## 8. Claim boundary

**Proved here:** Lemma 1, Lemma 2, Theorem 1, Corollaries 2–4. The only
imported proof authority is Theorem C of
[BergmanSegmentLengthBound.md](BergmanSegmentLengthBound.md) (proved there)
and standing facts (F1)–(F7) of
[UnconditionalConstantFactorBound.md](UnconditionalConstantFactorBound.md).
§7 is measurement; no adversarial supremum search was run against the window
bounds, and per `negative_results` 18 a clean sweep is basin evidence, not a
supremum certificate. Erdős #1041 is open.

## 9. Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_minimal_hub_window.py
```
