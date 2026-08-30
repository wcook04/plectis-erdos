# Erdős 1041: an exact upper bound on the extremal family

Status: ordinary proofs of the complementary closed constructions and their
explicit open-lemniscate upgrade, a two-sided bracket, and one correction to
how the sharpness of the radius bound has been read. 2026-08-24.
Erdős #1041 remains open; nothing below claims otherwise.

## 1. What was missing

[TrueGeodesicLab.md](TrueGeodesicLab.md) proves the **lower** bound for the
extremal family: with `f = zⁿ − rⁿ` and `ε = (1−rⁿ)^{1/n}`, every curve joining
two distinct roots inside `{|f| < 1}` has length at least `2(r − ε)`. That is
exact, and it is what makes the family extremal: `2(r − ε) → 2` as `r → 1⁻`, at
every degree.

Its **upper** values are grid geodesics. The lab's own claim boundary says so:
"The theorem and its corollary are exact. Everything else is numerical." So on
the one family which every recorded formulation has to be tight on, the corpus
had an exact floor and a measured ceiling.

This note supplies the ceiling as a construction, exact at every degree.

## 2. The crossing chord

> **Theorem.** Let `n ≥ 3`, `0 < r < 1`, `β = rⁿ`, `ε = (1−β)^{1/n}`,
> `c = cos(π/n)`, `ω = e^{2πi/n}`, and suppose `β ≥ 1/(1 + cⁿ)` — equivalently
> `t := ε/c ≤ r`. Then the polygonal path
>
> ```text
> r  --radial-->  t  --chord-->  t ω  --radial-->  r ω
> ```
>
> lies in `{|zⁿ − rⁿ| ≤ 1}`, meets `|f| = 1` only at the chord's midpoint, and
> has length
>
> ```text
> L_n(r)  =  2r − 2 ε tan(π/4 − π/(2n)).
> ```

*Proof.* **Radial segments.** On `z = s e^{2πik/n}` with `s ∈ [t, r]` we have
`f(z) = sⁿ − rⁿ`, so `|f| = rⁿ − sⁿ ∈ [0, β] ⊂ [0,1)`.

**Chord.** Since `n ≥ 3` we have `π/n ≤ π/3 < π/2`, so the chord from `t` to
`t ω` is parametrised by
`z(θ) = (ε/cos θ) e^{i(π/n + θ)}`, `θ ∈ [−π/n, π/n]`; the endpoints `θ = ∓π/n`
give `t` and `t ω`, and the midpoint `θ = 0` gives `ε e^{iπ/n}`. Then
`z(θ)ⁿ = −(ε/cos θ)ⁿ e^{inθ}`, so with `u = cosⁿθ ∈ [cⁿ, 1]`, `v = cos(nθ)`,

```text
|f|²  =  ε^{2n}/u²  +  2 β (ε^n/u) v  +  β².
```

The target `|f| ≤ 1 = εⁿ + β` is, after multiplying out by `u² > 0`,

```text
(1 − β)(1 − u²)  ≤  2 β u (u − v).                                   (★)
```

The hypothesis `β ≥ 1/(1+cⁿ)` is exactly `(1−β)/β ≤ cⁿ`, so it suffices to prove
`cⁿ(1 − u²) ≤ 2u(u − v)`. Since `u ≤ 1` gives `1 − u² ≤ 2(1 − u)`, and
`|θ| ≤ π/n` gives `u ≥ cⁿ`, it suffices to prove `1 − u ≤ u − v`, that is

```text
1 + cos(nθ)  ≤  2 cosⁿθ            for |θ| ≤ π/n.                    (L)
```

**Lemma (L).** Write `1 + cos(nθ) = 2cos²(nθ/2)` and put `ψ = n|θ|/2 ∈ [0, π/2]`.
Then (L) reads `2 log cos ψ ≤ n log cos(2ψ/n)`. The map `s ↦ log(cos s)/s` is
strictly decreasing on `(0, π/2)`, and `n log cos(2ψ/n) = 2ψ · [log(cos s)/s]`
evaluated at `s = 2ψ/n`; as `n` increases `s` decreases, so the right-hand side
increases in `n`. At `n = 2` it equals `2 log cos ψ`. Hence (L) holds for every
`n ≥ 2`, with equality only at `θ = 0` (and identically at `n = 2`). ∎

Equality throughout the chain forces `u = 1`, i.e. `θ = 0`: the chord touches
`|f| = 1` exactly at its midpoint and nowhere else.

**Length.** `2(r − t) + |t − tω| = 2(r − t) + 2t sin(π/n) = 2r − 2t(1 − sin(π/n))`,
and `(1 − sin(π/n))/cos(π/n) = tan(π/4 − π/(2n))`. ∎

**`t` is the largest admissible crossing radius.** At `t' > t` the chord's
midpoint is `t'c e^{iπ/n}`, whose `n`-th power is the negative real `−(t'c)ⁿ`, so
`|f| = (t'c)ⁿ + β > εⁿ + β = 1`. Bisection reproduces `t/ε = 1/cos(π/n)` to nine
digits at degrees 3–16 and six radii.

**The complementary case, and it meets this one exactly.** The hypothesis
`β ≥ 1/(1+cⁿ)` is exactly `t ≤ r`. When it fails, the ordinary chord between two
adjacent roots does the job, and the threshold is the same number.

> **Proposition.** For `n ≥ 2` and `0 < r < 1`, the maximum of `|f|` on the chord
> between two adjacent roots of `zⁿ − rⁿ` is exactly `rⁿ(1 + cosⁿ(π/n))`.
> Hence that chord lies in `{|f| ≤ 1}` if and only if `β ≤ 1/(1 + cⁿ)`.

*Proof.* Parametrise the chord as in the theorem but with `t = r`, so
`z(θ) = (rc/cos θ) e^{i(π/n+θ)}` and `z(θ)ⁿ = −(rc/cos θ)ⁿ e^{inθ}`. With
`u = cosⁿθ`, `v = cos(nθ)` and `ξ = cⁿ/u ∈ [cⁿ, 1]` (so `ξ = cⁿ` at the midpoint
and `ξ = 1` at the endpoints), `|f|² = β²(ξ² + 2ξv + 1)`. Lemma (L) gives
`v ≤ 2u − 1`, and `ξu = cⁿ`, so

```text
ξ² + 2ξv  ≤  ξ² + 4ξu − 2ξ  =  (ξ − 1)² − 1 + 4cⁿ  ≤  (1 − cⁿ)² − 1 + 4cⁿ  =  c^{2n} + 2cⁿ,
```

using `ξ ∈ [cⁿ, 1]`. So `|f|² ≤ β²(1 + cⁿ)²`, attained at `ξ = cⁿ`, i.e. `θ = 0`. ∎

So the two constructions are complementary at the same threshold
`r* = (1 + cosⁿ(π/n))^{-1/n}` and together cover every `r ∈ (0,1)`: below `r*` the
adjacent-root chord, of length `2r sin(π/n) < 2r`; at or above `r*` the crossing
chord, of length `2r − 2ε tan(π/4 − π/(2n)) < 2r`. Both rest on Lemma (L). The
threshold runs `0.9615, 0.9457, 0.9422, 0.9430, 0.9482, 0.9587, 0.9716` at
`n = 3,4,5,6,8,12,20`.

*(This paragraph replaces a first version of this note that asserted only the
sub-case `β ≤ 1/2` and left the window `β ∈ (1/2, 1/(1+cⁿ))` uncovered. The
Proposition closes it, and the receipt now checks the identity.)*

### The boundary touch has an explicit open upgrade

The crossing chord above is extremal for its radius and touches `|f|=1` at its
midpoint.  That does **not** obstruct the open-lemniscate problem.  Shrinking
the chord radially gives a strict path with an even simpler proof than the
extremal containment theorem.

> **Open-path corollary.** For every `n ≥ 2` and `0 < r < 1`, two adjacent roots
> of `zⁿ-rⁿ` can be joined inside `{|zⁿ-rⁿ|<1}` by an explicit polygonal path of
> length less than `2r`, hence less than `2`.

For `n=2`, the adjacent-root diameter works: on it, `z²-r²` runs through the
real interval `[-r²,0]`, and its length is `2r<2`.

Now let `n≥3`.  Below the transition radius, the adjacent-root chord is already
strict because its exact maximum is `β(1+cⁿ)<1`.  At or above the transition,
let `γ` be the radius-`t` crossing chord proved above and choose any
`0<λ<1`.  Replace `γ` by its radial contraction `λγ` and join its endpoints to
the two roots by radial segments.  For a point `z` on `γ`, put `w=zⁿ` and
`α=λⁿ`.  The closed containment theorem gives `|w-β|≤1`, while `β<1`; hence

```text
|αw-β| = |α(w-β) - (1-α)β|
       ≤ α|w-β| + (1-α)β
       ≤ α + (1-α)β
       < 1.
```

But `(λz)ⁿ=αw`, so the contracted chord is strictly inside.  On either radial
piece, `0≤s≤r` and `|sⁿ-rⁿ|=rⁿ-sⁿ<1`.  Finally the contracted path has length

```text
L_{n,λ}(r) = 2(r-λt) + 2λt sin(π/n)
           = 2r - 2λt(1-sin(π/n))
           < 2r < 2.
```

The argument is rotation invariant, so the same statement holds for every
binomial `zⁿ-a` with `0<|a|<1`, after setting `r=|a|^(1/n)`.  This settles the
open-path question on the full binomial family.  It still says nothing about
how to select such a path for an arbitrary monic polynomial.

## 3. The bracket, and what it settles

Combining with TrueGeodesicLab.md's lower bound, for `n ≥ 3` and `t ≤ r`:

```text
2(r − ε)   ≤   geodesic( zⁿ − rⁿ )   ≤   2r − 2 ε tan(π/4 − π/(2n)).
```

Both sides tend to `2` as `r → 1⁻`, so **the family stays extremal at every
degree** and `negative_results` entry 28 is untouched: a proof of #1041 still has
to be tight in that limit.

What is new is at fixed `r < 1`.

* The **radius bound** (`geodesic ≤ 2·maxᵢ|zᵢ|`) and **Form A**
  (`geodesic ≤ |z_a| + |z_b|`) now hold on the extremal family **by proof, at
  every degree `n ≥ 3`, with the explicit strict margin `2 ε tan(π/4 − π/(2n))`**.
  TrueGeodesicLab.md records them there only as measured ratios
  (`0.95193`, `0.86525`, `0.67578` at `n = 3, 4, 6`, `r = 0.999`). Since that lab
  names Form A as "the first statement in this problem's file that is both sharp
  and not already refuted by its own witnesses", having an exact certificate on
  the family it must be tight on is worth having.

* **The two-radius broken line is not the geodesic.** Its length is `2r`; the
  crossing chord is shorter by `2 ε tan(π/4 − π/(2n))`, which is strictly
  positive for every `n ≥ 3`. So TrueGeodesicLab.md's reading that the radius
  bound "is tight in precisely the right place" is a statement about the limit
  `r → 1⁻` only. At any fixed `r < 1` the radius bound has strict slack at every
  degree `n ≥ 3`, and its only fixed-`r` equality case is `n = 2`, where the
  geodesic is the chord.

* The bracket **tightens with degree**: its width is `2ε(1 − tan(π/4 − π/(2n)))`,
  and `tan(π/4 − π/(2n)) → 1`, so the construction is asymptotically optimal in
  `n` (`0.268, 0.414, 0.510, 0.577, 0.668, 0.767, 0.854` at `n = 3,4,5,6,8,12,20`).

## 4. What the construction is not

It is **not optimal at fixed `n`**, and the honest comparison says so. A single
well-placed hub — two straight segments, not three — already beats it on this
family: at `n = 3, r = 0.999` an exactly-scored two-segment path reaches
`1.89913` against the crossing chord's `1.92074`, and the grid geodesic is
`≈1.902`. The natural candidate hub, the pinch point `ε e^{iπ/n}`, is **not**
admissible — its worse spoke reaches `|f| = 1.000416` at `n = 3`, `1.001303` at
`n = 4`, `1.003452` at `n = 6` — which is why the crossing chord has to step in
to radius `ε/cos(π/n)` and pay a chord rather than turn at a point.

So this does not enlarge the surviving constructive family. Its content is that
the extremal family now has a closed-form interior path at every degree instead
of a grid measurement.

## 5. Reproduction of the lab's blind search, and of its trap

An independent adversarial maximisation of the grid geodesic over root
configurations in the closed unit disc, degrees 2–9, five restarts each, seeded
from the regular polygon and from random draws, returned a maximiser that is the
**regular `n`-gon at the modulus cap at every degree** — angles equally spaced to
four decimals, all moduli `1.0` — reproducing TrueGeodesicLab.md's table from a
different searcher and a different grid. Values: `2.036, 1.997, 1.990, 1.987,
1.972, 1.983, 1.980, 1.955` at `n = 2 … 9`.

The `n = 2` entry is above two, and it is the thin-corridor artifact that lab
documents: at nearly antipodal roots of modulus one the chord is interior but the
`{|f| < 1}` corridor around it is thinner than a grid cell. Recorded because it
reproduced without being sought — the trap is real and a search will find it
first.

## 6. Claim boundary

Proved here: the theorem of §2, Lemma (L), the sharpness of the crossing radius,
the exact complementary adjacent-chord maximum, the explicit open-path
corollary, and the bracket of §3. Numerical: the bisection agreements, the
two-segment comparison of §4, and the search of §5. Erdős #1041 is open; the
extremal family is unchanged; no negative result is retracted.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_crossing_chord.py --max-degree 16 --lemma-max-n 400
```
