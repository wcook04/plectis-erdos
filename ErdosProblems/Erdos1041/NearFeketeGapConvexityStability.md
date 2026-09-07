# Erdős 1041 — Theorem 2′: sharp quantitative Fekete–Hadamard stability by gap convexity

Date: 2026-08-30.  Origin: wave-2 opus stability agent (proof authored
and 700-configuration verified; zero violations, worst final slack
`6.0e-6`, tightness `0.9966`), main-loop review.  Checker:
`scripts/check_erdos1041_gap_convexity_stability.py`.

Sharpening of `NearFeketeRadialAngularSplit.md` Theorem 2 (which stays valid).
Constant `7` → `0.478…` (asymptotically sharp: the true sup is `0.476411`);
window `η ≤ 1/(80n²)` → `η ≤ 1/(4n)` in general, and **no window at all** for
equimodular roots. New engine: GLOBAL strong convexity of the circular log-gas
in gap coordinates, replacing the Gram/Fischer localisation.

Two corrections/records against the measured landscape: (1) the wave-1
transfer campaign's "sharp constant `0.447 = 2/sqrt(n(n-1))`" was the
mode-1-only value, a coincidental near-miss — the true sup is
`C_5 = 0.476411` at the `d* = 2` chord profile (three-way confirmed;
the campaign's own sampling reached `0.4831`).  (2) The measured
"amplitude dictionary" `eta ~ 11.19 t^2` is family-dependent, not a
constant: the admissible band is `[n lambda_min/2, n lambda_max/2] =
[10, 15]` at `n = 5` (measured 11.19 = a mode-1/2 mix), `[15, 27]` at
`n = 6` (measured 27.34 = the top alternating mode).  Consumer impact
(`QuinticModelRealTransferLaw.md` §2 thresholds): the landed Theorem 2
gives NOTHING there (its window `5e-4` excludes every `eta_0`);
Theorem 2′ pins the roots at the tangent-hub threshold
`eta_0 = 4.54e-3` within `0.0344` — `2.9%` of the gon spacing and
`13%` of the hub margin scale `|c*| = 0.667 eta^{0.171}`.

Notation as in the landed note: `a_k = ρ_k u_k`, `|u_k| = 1`, `ρ_k ∈ (0,1]`,
`ζ = e^{2πi/n}`, `D = |disc f|/n^n`, `η = 1 − D`, and

```text
Φ(a) = Σ_{i≠j} log|a_i − a_j| = log|disc f|,     Ψ := log(n^n) − Φ = −log(1−η) ≥ η.
```

`Ψ ≥ 0` by Fekete; `Ψ = 0` iff `a` is a rotated regular `n`-gon.

---

## 0. The Hessian (the object the old proof never used)

**Lemma 0.** Let `a_k = e^{i(2πk/n + t_k)}`. Then at `t = 0` the Hessian of `Φ`
is the circulant

```text
H_ii = −(n²−1)/6,      H_ik = 1 / (2 sin²(π(i−k)/n))   (i ≠ k),
```

with Fourier eigenvalues `−k(n−k)`, `k = 0…n−1`. Hence

```text
Ψ = ½ Σ_{k=1}^{n−1} k(n−k) |τ̂_k|²  +  O(|τ|³),        τ̂ = unitary DFT of τ.
```

*Proof.* `log|e^{iα}−e^{iβ}| = S(α−β)`, `S(φ) = log(2 sin(φ/2))`,
`S″(φ) = −¼ csc²(φ/2)`. Differentiating `Φ = Σ_{i≠j} S(θ_i−θ_j)` twice gives the
matrix; `Σ_{d<n} csc²(πd/n) = (n²−1)/3` gives the diagonal; the circulant
eigenvalue is `−(n²−1)/6 + ½ Σ_d cos(2πkd/n) csc²(πd/n) = −k(n−k)` by
`Σ_d cos(2πkd/n) csc²(πd/n) = (n²−1)/3 − 2k(n−k)`. ∎

**Lemma 0r (radial is LINEAR).** `∂Φ/∂ρ_i = n−1` at the gon
(`Σ_{j≠i}(z_i−z_j)^{-1} = (n−1)/(2z_i)` for `z_i^n = 1`). So radial deficits
cost `Ψ` at first order, not second — they can never be the binding direction.

**Consistency (translation).** `disc` is translation-invariant, so translating
the gon by `ε` gives `Ψ ≡ 0`. That translation is angular mode 1 of amplitude
`|ε|` plus a radial part; the mode-1 quadratic gain `n(n−1)|ε|²/4` cancels the
radial linear loss `(n−1)·n|ε|²/4` exactly. This is *why* `λ₁ = n−1` is the
smallest non-zero eigenvalue, and why mode 1 governs the extremal constant.

---

## 1. Theorem 2′ (equimodular case — GLOBAL, no window)

**Theorem 2′E.** Let `|a_i| = 1` for all `i` and let `η ∈ [0,1)`. Then there are
a unimodular `ω` and a bijection `σ` with

```text
max_i |a_i − ω ζ^{σ(i)}|  ≤  2 sin(h/2)  ≤  h,        h := sqrt(2Ψ/n),  Ψ = −log(1−η).
```

In particular `max_i |a_i − ω ζ^{σ(i)}| ≤ sqrt(2/n) · sqrt(η/(1−η))` for
every `η < 1`, with asymptotic constant `sqrt(2/n)` — `0.6325` at
`n = 5`, `0.5774` at `n = 6` — as `η -> 0`.  (Checker-caught correction:
the first draft claimed `sqrt(2/n) sqrt(η)` for every `η`, which fails
for large `η` since `Ψ = −log(1−η) > η`; the `Ψ`-form above is the
universal statement.)

*Proof.* Sort the arguments, `θ_(1) ≤ … ≤ θ_(n) < θ_(1)+2π`, let `g_1…g_n` be the
cyclic gaps (`Σ g = 2π`) and `τ_i := θ_(i) − α − 2πi/n` the deviations from a gon
of offset `α`. For each `d = 1…n−1` and each `i` the cyclic chord argument is
`ℓ_{i,d} = Σ_{k=i}^{i+d−1} g_k = τ_{i+d} − τ_i + 2πd/n ∈ (0,2π)`, and

```text
Ψ = Σ_{d=1}^{n−1} Σ_{i=1}^{n} [ −S(ℓ_{i,d}) + S(2πd/n) ],      S(φ) = log(2 sin(φ/2)).
```

`(−S)″(φ) = ¼ csc²(φ/2) ≥ ¼` on `(0,2π)`, so `−S` is `¼`-strongly convex there.
Taylor with integral remainder at `ℓ⁰_d = 2πd/n` gives, for any `μ_d` with
`μ_d ≤ ¼ inf_{I_d} csc²(ℓ/2)` on an interval `I_d ∋ ℓ⁰_d, ℓ_{i,d}`,

```text
Ψ ≥ Σ_{d,i} [ −S′(ℓ⁰_d)(ℓ_{i,d} − ℓ⁰_d) + (μ_d/2)(ℓ_{i,d} − ℓ⁰_d)² ].
```

The linear part vanishes: `S′(ℓ⁰_d)` does not depend on `i` and
`Σ_i (ℓ_{i,d} − ℓ⁰_d) = Σ_i (τ_{i+d} − τ_i) = 0`. Since
`Σ_i (τ_{i+d} − τ_i)² = Σ_k 4 sin²(πkd/n) |τ̂_k|²`,

```text
Ψ ≥ ½ Σ_{k≠0} Λ_k |τ̂_k|²,        Λ_k := Σ_{d=1}^{n−1} 4 μ_d sin²(πkd/n).      (★)
```

`μ_d = ¼` is admissible with no hypothesis whatsoever, and then `Λ_k = n/2` for
all `k ≠ 0` (since `Σ_{d<n} sin²(πkd/n) = n/2`). For any `i ≠ j`,
`τ_i − τ_j = ⟨τ, e_i − e_j⟩`, so Cauchy–Schwarz against `(★)` gives

```text
τ_i − τ_j ≤ sqrt( 2Ψ · R(d) ),   R(d) = (1/n) Σ_{k≠0} 4 sin²(πkd/n)/Λ_k,   d = i−j,
```

and with `Λ ≡ n/2`, `R(d) ≡ 4/n`, so `range(τ) ≤ 2 sqrt(2Ψ/n)`. Take `ω` the
rotation putting the mid-range at `0`, so `|τ_i| ≤ h = sqrt(2Ψ/n)`, and `σ` the
sorting bijection; `|a_i − ω ζ^{σ(i)}| = |e^{iτ_i} − 1| = 2 sin(|τ_i|/2)`. ∎

**Sharpening inside `(★)`.** Once `h` is known, `|ℓ_{i,d} − ℓ⁰_d| ≤ 2h`, so one
may re-run `(★)` with `μ_d = ¼ csc²(ℓ*_d/2)`, `ℓ*_d` the point of
`[ℓ⁰_d − 2h, ℓ⁰_d + 2h]` nearest `π`, and iterate. In the limit `h → 0`,
`μ_d → ¼ csc²(πd/n)` and `Λ_k → k(n−k)` — the exact Hessian. So the proof is
*asymptotically sharp by construction*, with no cubic remainder analysis at all:
strong convexity replaces Taylor-with-error globally.

**Sharp constant.** `C_n := max_d ½ sqrt(2 R_n(d))` with `Λ_k = k(n−k)` is the
exact asymptotic sup of `d_max/sqrt(η)`:

```text
n        3        4        5        6        7        8       10       12
C_n  0.70711  0.57735  0.47641  0.41276  0.36109  0.32367  0.26738  0.22841
d*       1        2        2        3        3        4        5        6
```

(`R_n(d) = R_n(n−d)`, so `d*` and `n−d*` tie; the table lists the
smaller.)

---

## 2. Theorem 2′ (general radii)

**Theorem 2′.** Let `a_1…a_n` lie in the closed unit disk, `D ≥ 1 − η`,
`Ψ = −log(1−η)`. Define, with `P_n(x) = Σ_{l=0}^{n−2}(n−1−l)x^l`
(`P_n(0) = n−1`, `P_n(1) = n(n−1)/2`):

```text
(R) x₀ = 1 − nΨ/(n−1);   q = nΨ/P_n(x₀);   ρ_min ≥ sqrt(1−q);
    max_i(1−ρ_i²) ≤ q,   Σ_i(1−ρ_i) ≤ S_δ := q/(1+sqrt(1−q)),   δ_max ≤ S_δ.
(S) s₀ = (2(1−sqrt(η)) − nη)/(n−1)          [Fischer; landed Thm 2(2), no window]
(P) Ψ⁺ = Ψ + n S_δ² / (s₀² − δ_max²)                       (requires δ_max < s₀)
(C) h = the fixed point of the `(★)` iteration started at h₀ = sqrt(2Ψ⁺/n).
```

Then there are `ω` and a bijection `σ` with

```text
max_i |a_i − ω ζ^{σ(i)}|  ≤  δ_max + 2 sin(h/2).
```

*Proof.* **(R)** `D = det H · Π_i (s_i/n)` with `s_i = Σ_{m<n} ρ_i^{2m}` and both
factors in `[1−η,1]` (landed note), so `Σ_i log(n/s_i) ≤ Ψ`. Now
`log(n/s_i) ≥ 1 − s_i/n = (1−ρ_i²)P_n(ρ_i²)/n` and `P_n` is increasing, so the
crude `P_n ≥ n−1` gives `1−ρ_i² ≤ nΨ/(n−1)`, i.e. `ρ_i² ≥ x₀`, and re-inserting
`P_n(ρ_i²) ≥ P_n(x₀)` gives both stated bounds. (This alone beats the landed
Thm 2(1) by a factor `P_n(x₀)/(n−1) → n/2`; measured `2.5×` at `n = 5`.)

**(P)** With `u_i = a_i/ρ_i` and `Ψ_ang := log n^n − Σ_{i≠j} log|u_i−u_j|`, the
identity `|a_i−a_j|² = (ρ_i−ρ_j)² + ρ_iρ_j|u_i−u_j|²` gives EXACTLY

```text
Ψ_ang = Ψ + (n−1) Σ_i log ρ_i + ½ Σ_{i≠j} log(1 + X_ij),
X_ij = (ρ_i−ρ_j)² / ( |a_i−a_j|² − (ρ_i−ρ_j)² ).
```

`log ρ_i ≤ 0`, `log(1+x) ≤ x`, `|a_i−a_j| ≥ s₀`, `|ρ_i−ρ_j| ≤ δ_max`, and
`½ Σ_{i≠j}(ρ_i−ρ_j)² = n Σ_i(ρ_i−ρ̄)² ≤ n S_δ²` give `Ψ_ang ≤ Ψ⁺`. The
correction is **second order** in the radial deficit — this is exactly why the
window does not degrade: `S_δ = O(Ψ)`, so `Ψ⁺ = Ψ(1 + O(nΨ))`.

**(C)** Apply Theorem 2′E's argument to `u`, with `Ψ_ang ≤ Ψ⁺`. Finally
`|a_i − ω ζ^{σ(i)}| ≤ (1−ρ_i) + |e^{i(τ_i−c)} − 1| ≤ δ_max + 2 sin(h/2)`. ∎

**Corollary 2′a (general `n`).** `η ≤ 1/(4n)` ⟹ `max_i|a_i − ωζ^{σ(i)}| ≤
1.048 sqrt(η)`, and `≤ 0.795 sqrt(η)` for `n ≥ 4` (checked `n = 3…100`).
This replaces `η ≤ 1/(80n²)` — a widening by a factor `20n` — while cutting the
constant from `7` to `≈ 1`.

**Corollary 2′b (`n = 5`).** certified `C(η) = d_bound/sqrt(η)`:

```text
η       1e−5    1e−4    1e−3   4.54e−3  1e−2   3e−2   5e−2   1e−1
C      0.4779  0.4811  0.4915  0.5099  0.5286 0.5824 0.6397 0.9044
```

feasible to `η ≤ 0.176`; `C ≤ 1` for `η ≤ 0.1096`. Sharp value `0.476411`.

---

## Claim boundary

Lemma 0, 0r, Theorem 2′E and Theorem 2′ are ordinary proved mathematics; step
(S) imports the landed Theorem 2(2) unchanged (its proof uses only Fischer and
needs no window). Every inequality was checked numerically on 700 configurations
(`verify_theorem2prime.py`). `C_n` is proved to be an upper bound and verified
numerically to be attained; that it is exactly the sup is asserted on the
strength of the (★) → Hessian limit plus a 300-restart direction optimiser
agreeing to 7 digits, not on a separate proof of attainment. No literature check
was run; the strong-convexity-in-gap-coordinates argument is elementary and may
well be classical — claim "new to this directory" only.
