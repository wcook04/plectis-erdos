# Erdős #1049: irrationality of `F(a/b)` on the region `b^μ < a`, `μ = 2.46497868…`, with `31/4` the first new base

Status: ordinary complete proof citing published lemmas (Zudilin 2004, Lemmas 1, 2, 7).
Not kernel-checked; the finite part is Lean-checked in `RationalBaseContour.lean`.
Priority: extends Bundschuh–Väänänen 1994 Theorem 2; the rational-base extension of this
kind of result was announced without a constant in Zudilin 2016 (see §7).

## 0. Notation and the object

For real `t > 1`,

```
F(t) := Σ_{m≥1} 1/(t^m − 1) = Σ_{n≥1} τ(n) t^{−n}      (τ = number of divisors),
```

the Lambert value of Erdős #1049 (`F(t) = h_p(1)` in Zudilin's notation, `p = t`,
`q = 1/p`).  A rational base is written `a/b` with `a > b ≥ 1` coprime integers, and
its height parameter is `θ := log b / log a ∈ [0, 1)`.  In Zudilin 2016's notation
`p = r/s`, so `r = a`, `s = b`, and `log|r| > c log|s|` means `θ < 1/c`.

Constants of Zudilin 2004, Section 5, direction `(α₀, α₁, α₂; β) = (14, 12, 14; 27)`:

```
C₁ = (α₀+α₁+α₂)β − (α₁² + α₂² + β²)/2 = 1091/2 = 545.5                         (paper (25))
C₀ = α₁²/2 + α₀α₁ + (β−α₂)(α₂−α₁) − (3/π²)(m² − J) = 266 − (3/π²)(225 − J)     (paper (26))
J  = ∫₀¹ ω(x) d(−ψ'(x)) = Σ_{i=1}^{13} (ψ₁(uᵢ) − ψ₁(vᵢ)),  ψ₁(x) = Σ_{k≥0} 1/(k+x)²
μ  := C₁/C₀ = 2.464978683574975037454488275535521581878…   (Zudilin's Theorem 1 bound)
θ* := C₀/C₁ = 1/μ = 0.40568302138406054101566030557693017464819107867787…
```

with the thirteen intervals `[uᵢ, vᵢ)` = `[1/14,1/12) [1/7,1/6) [3/14,1/4) [2/7,1/3)
[5/14,2/5) [3/7,7/15) [1/2,8/15) [4/7,3/5) [9/14,2/3) [5/7,11/15) [11/14,4/5)
[6/7,13/15) [13/14,14/15)` (recomputed from `ω`, equal to the paper's printed list).
Numerics: `J = 77.943184475009095922589567023992110449…`,
`C₀ = 221.300088165005025124042696692215410…`; mpmath at 60 digits, `J` cross-checked
by direct series summation to `1e−59` (`formal_math/probes/erdos1049_zudilin_region.py`,
receipt `state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_region/region_receipt.json`).

## 1. Statements

**Theorem A (region).** Let `a > b ≥ 1` be coprime integers with

```
b^μ < a,   equivalently   log b / log a < θ* = 0.405683021384…,   μ = 2.464978683574975…
```

Then `F(a/b)` is irrational.  In the normalisation of Zudilin 2016, §2 ("the results can be
given for non-integer `p = r/s`, `|p| > 1`, under `log|r| > c log|s|` for some computable
constant `c > 0`"): the constant is

```
c = μ = C₁/C₀ = 2.46497868357497503745…,
```

the irrationality-exponent bound of Zudilin 2004 Theorem 1 itself, and the region is
`|r| > |s|^μ` for positive `r/s` (negative bases are not treated here, see §4 Step 5).

**Theorem B (first new base).** `F(31/4)` is irrational, and so is `F((31/4)^r)` for every
integer `r ≥ 1`.  Here `log 4 / log 31 = 0.4036981731… < 81/200 < θ*`, and
`4^μ = 30.4835… < 31 < 4^{μ_BV} = 32.3696…` with `μ_BV = 2π²/(π² − 2) = 2.508284761994…`
the Bundschuh–Väänänen exponent, so `31/4` lies outside their region
`log b/log a < 1/2 − 1/π² = 0.398678816357…` and inside Theorem A's.

**Theorem C (Archimedean cap, proof-backed no-go for `3/2`).** Let `(U_n, V_n) ∈ ℤ[x]²`
be any sequence with `Λ_n(x) := U_n(x) F(x) − V_n(x) ≠ 0`, `deg U_n, deg V_n ≤ δ n²(1+o(1))`,
and `log|Λ_n(x)| = −σ n² log x (1+o(1))` for every real `x > 1`, with `σ, δ > 0` independent
of `x` (all Padé-type families, including Zudilin's, are of this kind).  Then the
homogenised forms `b^{deg U_n} Λ_n(a/b)` tend to `0` exactly on `log b/log a < σ/(σ+δ)`,
and `σ/(σ+δ) ≤ 1/2`.  Hence no such family proves irrationality of `F(a/b)` unless
`b² < a`; in particular none reaches `3/2`.

Theorem A is the headline; Theorem B is its first consequence beyond the published
region; Theorem C says why the same mechanism cannot reach the problem's target base.

## 2. The published inputs, quoted as printed

All from W. Zudilin, *Heine's basic transform and a permutation group for q-harmonic
series*, Acta Arith. 111.2 (2004) 153–164 (annex
`annexes/zudilin-2004-heine-q-harmonic-series/`, `extracted.md` line numbers in brackets).
Standing hypothesis of the paper (p. 154, Section 2): "Throughout the paper
`p = 1/q ∈ ℤ ∖ {0, ±1}`."  `D_n(p) := Π_{l=1}^{n} Φ_l(p)`, `Φ_l` the cyclotomic
polynomials.

**Lemma 1** (p. 155 [132–136], attributed to [BV, Section 2] and [Ass, Lemma 2]).
`lim_{n→∞} log|D_n(p)| / (n² log|p|) = 3/π²`.

**Lemma 2** (p. 155 [137–148], attributed to [Zu1, Lemma 1]). For each demi-interval
`[u, v) ⊂ (0, 1)` with `u, v ∈ ℚ`,
`lim_{n→∞} (1/(n² log|p|)) Σ_{l : {n/l} ∈ [u,v)} log|Φ_l(p)| = (3/π²)(ψ'(u) − ψ'(v)) = (3/π²) ∫_u^v d(−ψ'(x))`,
where `{a} = a − ⌊a⌋` and `ψ` is the logarithmic derivative of Euler's gamma function.

**Lemma 7** (p. 161 [451–462]). With `c = (c₀₀, c₀₁, c₁₁, c₂₁, c₁₂, c₂₂)`,
`c₀₀ = a₀+a₁+a₂−b−1, c₀₁ = a₀−1, c₁₁ = a₁−1, c₂₁ = a₂−1, c₁₂ = b−a₁−1, c₂₂ = b−a₂−1`,
`m(c) = max c`, `s(c) = b − a₁ − a₂`, `H(c) = F(a; b)` the series (9),
`M(c) = M(a; b)` the integer of (16) when (14) holds, and

```
ν_l := max{0, ⌊c₂₁/l⌋+⌊c₂₂/l⌋−⌊c₁₁/l⌋−⌊c₁₂/l⌋, ⌊c₀₁/l⌋+⌊c₂₁/l⌋−⌊c₀₀/l⌋−⌊c₁₂/l⌋},   (22)
Ω(p) := Π_{l=2}^{m(c)} Φ_l(p)^{ν_l} ∈ ℤ[p],
```

"We have `p^{−M(c)} D_{m(c)}(p) Ω^{−1}(p) H(c) ∈ ℤ[p] h_p(1) + ℤ[p]`, provided that
`s(c) > 0`."  Its proof (p. 161) is a computation in the polynomial ring: it combines the
inclusion (21) for the six images `gc`, `g ∈ G⁺`, with the Heine-transform stability
(Lemma 5) and the cyclotomic order formula (5), and ends "these polynomials are coprime to
the polynomial `p ∈ ℤ[p]`, we arrive at (23)."  The paper's own display (24),
`p^{−M} D_{mn}(p) Ω^{−1}(p) H_n ∈ ℤ[p]h_p(1) + ℤ[p] ⊂ ℤh_p(1) + ℤ`, distinguishes the
polynomial ring `ℤ[p]` from its evaluation `ℤ`, so `ℤ[p]` in Lemma 7 is the polynomial ring
in the symbol `p`.  This is the reading used below, and it is the only reading under which
the paper's own proof of Theorem 1 goes through.

Also used from the paper: the linear-form identity (9)–(11), `H_n = A_n h_p(1) − B_{1,n} − B_{2,n}`,
with `A_k` from (8) and `A, B₁, B₂ ∈ ℚ(p)` given by (10), (11); and the parameter
conventions of Section 5: `a_j = α_j n + 1`, `b = βn + 2`, `c_{00} = α₀+α₁+α₂−β`,
`c_{j1} = α_j`, `c_{j2} = β − α_j`, `m = m(c)`, so that for `(14,12,14;27)`:
`c = (13, 14, 12, 14, 15, 13)`, `m = 15`, `N := mn = 15n`, `M_n = 266n² + 34n + 1`
(from (16); Lean: `two_mul_zudilinM`), `s(c) = n > 0`, and (14) holds
(`12n+1 ≤ 14n+1`, `26n+2 ≤ 27n+2 ≤ 28n+2`).

Other literature: P. Bundschuh, K. Väänänen, *Arithmetical investigations of a certain
infinite product*, Compositio Math. 91 (1994) 175–199, Theorem 2 second half (p. 177):
for `α = −1` (the case `L_q(−1) = h_p(1)`) the hypothesis is
`λ < (1/2 + 1/π²)^{−1}` with `λ = log h(q)/log|q|_v`; for `q = a/b ∈ ℚ` this is
`log a / log(a/b) < (1/2 + 1/π²)^{−1}`, i.e. `log b/log a < 1/2 − 1/π²`.  This is the only
published rational-base criterion for `F` located; it is used here only for comparison.

## 3. Elementary facts with complete proofs

**(E1) `F(x) ∉ ℚ(x)`.** As `x → 1⁺` with `ε = x − 1`, the terms with `m ≤ 1/ε` satisfy
`x^m − 1 ≤ mε e^{1}` and the tail is `O(1/ε)`, so `F(x) ≥ (e^{−1}/ε) Σ_{m ≤ 1/ε} 1/m − O(1/ε) ≥ (c/ε) log(1/ε)`
for small `ε`, while `F(x) ≤ (1/ε)(1 + log(1/ε)) + O(1/ε)`.  A nonzero rational function
behaves like `c ε^{−k}`, `k ∈ ℤ`, near `x = 1`; `ε^{−1} log(1/ε)` is not of that form.
∎

**(E2) Transfer of Lemma 7 to explicit polynomials.** Write
`Λ_n(x) := x^{−M_n} D_N(x) Ω_n(x)^{−1} H_n(x)` where `H_n = A_n F − B_n`, `B_n := B_{1,n} + B_{2,n}`,
`A_n, B_n ∈ ℚ(x)`.  Lemma 7 gives `U_n, V_n ∈ ℤ[x]` with `Λ_n = U_n F − V_n` as functions of
`x > 1`.  Then `(x^{−M_n} D_N Ω_n^{−1} A_n − U_n) F = x^{−M_n} D_N Ω_n^{−1} B_n − V_n` with
both coefficients in `ℚ(x)`; by (E1) the left coefficient vanishes identically, hence

```
U_n = x^{−M_n} D_N(x) A_n(x)/Ω_n(x),    V_n = x^{−M_n} D_N(x) B_n(x)/Ω_n(x)     in ℚ(x),
```

and Lemma 7 says these two rational functions are polynomials with integer coefficients.
∎  (Verified exactly, as an identity in `ℤ[x]`, for `n = 1, 2, 3`: `Ω_n | D_N A_n` and
`Ω_n | D_N B_n` with zero remainder, then `x^{M_n}` divides both quotients;
`formal_math/probes/erdos1049_zudilin_exact_forms.py`, and independently
`state/…/erdos1049_contour_adversary/zud_recon.py`, logs `n1.log, n2.log, n3.log`.)

**(E3) Degrees.** The `k`-th summand of `A_n(x) = Σ_{k=a₂}^{b−1} A_k x^{a₀k}` (from (8), with
`[m; j]_x` of degree `j(m−j)`) has `x`-degree
`d_k = a₀k + E_k + (a₁−1)(k−a₁) + (b−k−1)(k−a₂)`,
`E_k = a₁(a₁−1)/2 − (b−a₂)(b−a₂−1)/2 + (b−k)(b−k−1)/2`, and
`d_{k+1} − d_k = a₀+a₁+a₂−k−2 = 40n+1−k > 0` for `k ≤ b−2`.  So the degrees are strictly
increasing, no cancellation at the top is possible, and

```
K_n := deg A_n = d_{b−1} = (1091n² + 81n + 2)/2,     K_n/n² → 1091/2 = C₁.
```

(Lean: `twoMulZudilinSummandDegree_succ_sub`, `twoMulZudilinSummandDegree_top`,
`twoMulZudilinSummandDegree_step_pos`.)  Since `deg D_N = Σ_{l≤N} φ(l)`,
`deg Ω_n = Σ_{l=2}^{N} ν_l φ(l)`, and `deg B_n D_N ≤ K_n + deg D_N − 1` (each
`D_N/(x^l − 1)` has degree `deg D_N − l`), (E2) gives

```
deg U_n = W_n := K_n − M_n + Σ_{l≤N} φ(l) − Σ_{l≤N} ν_l φ(l),    deg V_n ≤ W_n − 1.
```

(Exact values `W₁, W₂, W₃ = 333, 1315, 2944`, leading coefficients `±1`, `V_n(0) = 1`,
`ord₀ U_n = 2n²`; both probes.)

**(E4) Positivity.** For real `x > 1`, `q = 1/x ∈ (0,1)`, every factor of
`R(q^t) = [(q^{t+1};q)_{a₁−1}/(q;q)_{a₁−1}] · [(q;q)_{b−a₂−1}/(q^{a₂+t};q)_{b−a₂−1}] · q^{a₀t}`
is positive for `t ≥ 0`, so `H_n(x) = Σ_{t≥0} R(q^t) > 0`; also `D_N(x) > 0`, `Ω_n(x) > 0`.
Hence `Λ_n(x) > 0`, in particular `Λ_n(x) ≠ 0`.  No determinant or Nesterenko-type
nonvanishing criterion is needed. ∎

**(E5) Archimedean size, uniform in the real base.** Each `q`-Pochhammer factor in `R(q^t)`
lies in `[(q;q)_∞, 1]`, so `(q;q)_∞² q^{a₀t} ≤ R(q^t) ≤ (q;q)_∞^{−2} q^{a₀t}` and

```
(q;q)_∞² ≤ H_n(x) ≤ (q;q)_∞^{−2}/(1 − q^{a₀}),    i.e.  log H_n(x) = O_x(1).
```

For `l ≥ 1`, `log Φ_l(x) = φ(l) log x + Σ_{d|l} μ(l/d) log(1 − x^{−d})`, and the correction is
at most `τ(l)·|log(1 − 1/x)|` in absolute value; summing over `l ≤ N` costs `O_x(N log N)`.
Therefore

```
log Λ_n(x) = −(K_n − W_n) log x + O_x(n log n) + O_x(1) = −(K_n − W_n) log x + o(n²).
```

(Checked numerically: residual `log Λ̂_n − (K log b − (K−W) log a)` equals `−0.257, +0.241, +0.117`
at `31/4` for `n = 1,2,3`, bounded as predicted; both probes.) ∎

**(E6) The limit `(K_n − W_n)/n² → C₀`, from Lemmas 1 and 2 at `p = 2`.**
`K_n − W_n = M_n − Σ_{l≤N} φ(l) + Σ_{l≤N} ν_l φ(l)`.  Lemma 1 at `p = 2`, with
`log Φ_l(2) = φ(l) log 2 + O(τ(l))`, gives `Σ_{l≤N} φ(l) = (3/π²) N² (1+o(1)) = (3/π²)·225 n² (1+o(1))`
(this is also Mertens' classical theorem).  For the second sum: `ν_l = ω(n/l)` with the
1-periodic `ω(x) = max{0, ⌊14x⌋+⌊13x⌋−⌊12x⌋−⌊15x⌋, 2⌊14x⌋−⌊13x⌋−⌊15x⌋}`
(Section 5 of the paper; `ω ∈ {0,1}` here, and `ω = 1` exactly on the thirteen intervals),
so `Σ_{l=2}^{N} ν_l φ(l) = Σ_i Σ_{l : {n/l} ∈ [uᵢ, vᵢ)} φ(l)`; the constraint `l ≤ N = 15n`
is automatic since `{n/l} = n/l < 1/15 < 1/14 ≤ uᵢ` for `l > 15n`, and `l = 1` never
contributes.  Lemma 2 at `p = 2` together with `log Φ_l(2) = φ(l) log 2 + O(τ(l))` gives
`Σ_{l : {n/l} ∈ [u,v)} φ(l) = (3/π²)(ψ'(u) − ψ'(v)) n² (1+o(1))` for each interval.  Hence

```
(K_n − W_n)/n² → 266 − (3/π²)(225 − J) = C₀,     with   J = Σ_i (ψ'(uᵢ) − ψ'(vᵢ)) = Σ_i (ψ₁(uᵢ) − ψ₁(vᵢ)),
```

using `ψ'(x) = ψ₁(x) = Σ_{k≥0} 1/(k+x)²` (classical).  Note that the *integer* instances
`p = 2` of Lemmas 1 and 2 suffice, because both lemmas are, after removing the elementary
cyclotomic correction, statements about the integers `φ(l)` alone. ∎

## 4. Proof of Theorem A

Fix coprime `a > b ≥ 1` with `θ = log b/log a < θ*`, set `x = a/b`.

*Step 1 (forms).* By (E2)–(E3), for each `n ≥ 1` there are `U_n, V_n ∈ ℤ[x]` with
`deg U_n = W_n`, `deg V_n ≤ W_n − 1`, and `Λ_n(a/b) = U_n(a/b) F(a/b) − V_n(a/b)`.

*Step 2 (homogenisation; the only non-Archimedean step).* Since `deg U_n, deg V_n ≤ W_n`,
`Û_n := b^{W_n} U_n(a/b)` and `V̂_n := b^{W_n} V_n(a/b)` are integers, and
`Λ̂_n := b^{W_n} Λ_n(a/b) = Û_n F(a/b) − V̂_n ∈ ℤ F(a/b) + ℤ`.
(`b^{W_n − 1} U_n(a/b) ∉ ℤ` at `31/4`, `7/2`: the degree is exactly `W_n`; probes.)

*Step 3 (nonvanishing).* `Λ̂_n > 0` by (E4).

*Step 4 (size).* By (E5), `log Λ̂_n = W_n log b − (K_n − W_n) log(a/b) + o(n²) = K_n log b − (K_n − W_n) log a + o(n²)`,
and by (E3), (E6), `log Λ̂_n / n² → C₁ log b − C₀ log a`, which is negative exactly when
`log b/log a < C₀/C₁ = θ*`.  So `Λ̂_n → 0`.

*Step 5 (conclusion).* If `F(a/b) = P/Q` with integers `Q ≥ 1`, then
`Q Λ̂_n = P Û_n − Q V̂_n` is a positive integer for every `n`, yet tends to `0`.
Contradiction. ∎

Every use of a real base `x = a/b` is in (E1), (E4), (E5), which hold for all real `x > 1`;
positivity (E4) is why only positive bases are treated.  The paper's hypothesis `p ∈ ℤ`
enters nowhere: Lemma 7 is a polynomial identity, and Lemmas 1–2 are consumed at `p = 2`.

*Proof of Theorem B.* `log 4/log 31 < 81/200` is `4^{200} < 31^{81}`
(`ZudilinHeightRegion.thirtyoneFour_power_certificate`), and `81/200 < θ*` is
`RationalBaseContour.eightyOne_twoHundredths_lt_zudilinContour`; the ratio is invariant under
`(a, b) ↦ (a^r, b^r)` (`zudilinContourRegion_pow`), and `(31^r, 4^r)` are coprime. ∎

## 5. Proof of Theorem C (the cap `b² < a`)

*Rational-base criterion.* With `deg U_n, deg V_n ≤ δn²(1+o(1))` and `|Λ_n(a/b)| = (a/b)^{−σn²(1+o(1))}`,
`log(b^{deg U_n} Λ_n(a/b)) = n²[(δ+σ) log b − σ log a](1+o(1))`, negative iff `θ < σ/(σ+δ)`.

*Exponent lemma at an integer base.* Fix an integer `p ≥ 2`, `h := F(p)`, `q_n := |U_n(p)| ≤ e^{δ' n²(1+o(1))}`,
`|q_n h − p_n| = e^{−σ' n²(1+o(1))}` two-sided, with `δ' = δ log p`, `σ' = σ log p`
(the two-sided estimate holds for every family satisfying the hypothesis of Theorem C).
Let `P/Q` be any rational with `Q` large and choose `n` minimal with `|q_n h − p_n| < 1/(2Q)`;
minimality gives `e^{σ' n²(1+o(1))} ≤ (2Q)^{1+o(1)}`.  If `Q p_n − P q_n ≠ 0` then
`|q_n Q (h − P/Q)| ≥ 1 − 1/2`, so `|h − P/Q| ≥ 1/(2 Q q_n) ≥ Q^{−1−δ'/σ'−o(1)}`.  If
`Q p_n = P q_n` then `|h − P/Q| = |q_n h − p_n|/q_n ≥ e^{−(σ'+δ') n²(1+o(1))} ≥ (2Q)^{−(1+δ'/σ')(1+o(1))}`.
Hence `μ(F(p)) ≤ 1 + δ/σ = (σ+δ)/σ`.

*Cap.* `F(p)` is irrational for every integer `p ≥ 2` (Erdős 1948 for `p = 2`; Bézivin 1988,
Borwein 1991 in general), so `μ(F(p)) ≥ 2` by Dirichlet, hence `(σ+δ)/σ ≥ 2`, i.e.
`σ/(σ+δ) ≤ 1/2`.  For `3/2`, `θ = log 2/log 3 = 0.6309 > 1/2`. ∎

For Zudilin's family `σ = C₀`, `δ = C₁ − C₀`, so `σ/(σ+δ) = θ*` and `(σ+δ)/σ = μ`: the
rational-base threshold of a `p`-uniform family is the reciprocal of its integer-base
irrationality-exponent bound, which is why `θ* = 1/μ` and `1/2 − 1/π² = 1/μ_BV`.  The packet's
"rank budget law" `t < (r−1−κ)/r` at `r = 2`, `κ = 0` and its "homogenisation ceiling
`a > b²`" are the same statement; Theorem C replaces their model hypotheses by Dirichlet's
theorem plus the known irrationality at integer bases, and is mechanism-independent.

Quantitative gap at `3/2` for this family: `C₁ log 2 − C₀ log 3 = +134.98879065… > 0` per `n²`,
against `log|Û_n| ≈ (C₁ − C₀) log 3 · n² = 356.18 n²`.  So an Archimedean-only argument would
need to remove a `2,3`-smooth content of logarithmic size `≥ 134.99 n²`, i.e. `37.9%` of the
height of `Û_n`, from the pair `(Û_n, V̂_n)`; the packet's measured content on the q-Apéry
diagonal is `gcd = 1` (`HomogenisationCeilingProof.md`).  Reaching `3/2` therefore needs a
family whose exponents are *not* uniform in the base (content imposed while the combination is
chosen: producer `congruence_constrained_adelic_hermite_pade`), or a higher-rank system with
full linear independence, never a rank-two Padé family with a better direction.

*Direction search (falsifier for "a different `(a,b,c;d)` reaches further").* For every
primitive direction on Zudilin's cone `α₁ ≤ α₂`, `α₁+α₂ < β ≤ α₀+α₂` with all entries `≤ 30`
(37,533 directions), `θ*(dir) = C₀/C₁` computed from (25)–(26) is maximised by `(14,12,14;27)`
and its group image `(15,12,13;26)`, value `0.405683021384`; the next values are
`0.405639` (`(16,13,14;28)`), `0.405583`, `0.405521`.  Larger boxes were not scanned
(`formal_math/probes/erdos1049_zudilin_direction_search.py`, receipt
`…/erdos1049_zudilin_region/direction_search_bound30.json`; the bound-22 scan is also there).

## 6. The region, explicitly

`θ* = 0.40568302138406054101566030557693017464819107867787`; rational bracket from the
`k < 1000` partial sums of the trigamma series with the integral tail bound:
`0.4056830213 < θ* < 0.4056830214`; Lean: `81/200 < θ* < 1/2`.

Coprime `a/b` with `a ≤ 60` in the region: 137 bases, of which the non-integer ones are
`7/2, 9/2, …, 59/2` (all `b = 2`, `a ≥ 7` odd), `16/3, 17/3, 19/3, 20/3, 22/3, …, 59/3`
(`a ≥ 16`, `3 ∤ a`), `31/4, 33/4, 35/4, …, 59/4` (`a ≥ 31` odd), and
`53/5, 54/5, 56/5, 57/5, 58/5, 59/5`.  Closest misses: `52/5` (`θ = 0.407324`, short by
`0.00164`), `51/5`, `29/4` (`0.411694`, short by `0.00601`), `49/5`, `48/5`, `14/3`.
Tightest members: `53/5` (margin `0.000313`), `31/4` (margin `0.001985`), `54/5`.

Bases new relative to Bundschuh–Väänänen, i.e. in the strip `s^μ < r < s^{μ_BV}`,
`(s^μ, s^{μ_BV})`:

```
s=2: (5.52, 5.69) none      s=3: (15.00, 15.73) none      s=4: (30.48, 32.37) 31
s=5: (52.84, 56.65) 53, 54, 56          s=6: (82.82, 89.50) 83, 85, 89
s=7: (121.10, 131.75) 122,123,124,125,127,128,129,130,131
s=8: (168.31, 184.16) 169,171,…,183 (odd)   s=9: (225.00, 247.46) 15 bases   s=10: 12 bases
s=11: 37 bases   s=12: 17 bases
```

So `31/4` is the new base of smallest denominator and smallest numerator; the strip is
infinite (its width `s^{μ_BV} − s^μ → ∞`).  The base `3/2` is at `θ = 0.630929753571…`,
a gap of `0.225247` above `θ*`; by Theorem C no `p`-uniform rank-two family can close it.

## 7. Prior art and attribution

* Zudilin 2004 proves `μ(F(p)) ≤ 2.46497868…` for integer `p`; it states no rational-base
  result.  Theorem A is its forms placed in the Bundschuh–Väänänen height framework; the
  identity `θ* = 1/μ` (Theorem C) makes the relation exact.
* Bundschuh–Väänänen 1994 Theorem 2 (α = −1) gives the region `θ < 1/2 − 1/π² = 0.398679`
  (`= 1/μ_BV`) over number fields; `7/2` and all `b = 2, 3` members of the region above are
  already theirs.  Duverney 1996 Theorem 2 (per `prior_art_adjudication_2026_09_02.md`) is
  weaker (`0.23201`).
* Zudilin 2016, *On the irrationality of generalized q-logarithm*, Res. Number Theory 2
  (2016), Art. 15, §2 (annex `arxiv-1601-02688`, source lines 200–204): "the results can be
  given for non-integer `p = r/s`, `|p| > 1`, as well under a customary in such situations
  assumption `log|r| > c log|s|` for some computable constant `c > 0`" — for the generalized
  `q`-logarithm of that paper, no `c` computed.  The contribution here is the explicit
  constant for `F` itself, `c = μ_{Zudilin 2004} = 2.46497868…`, its consequences (the strip,
  `31/4`), and the observation that any such `c` equals the integer-base exponent bound.
* Matala-aho, Väänänen, Zudilin, *New irrationality measures for q-logarithms*, Math. Comp.
  75 (2006) 879–889, DOI 10.1090/S0025-5718-05-01812-0 (read in full by the prior-art pass,
  `prior_art_adjudication_2026_09_02.md` addendum, commit `dea7d99cff`): it treats only
  `p = 1/q ∈ ℤ ∖ {0, ±1}` (abstract p. 879; Theorems 1–2; the §3 convention), for
  `ln_q(1−z) = Σ z^ν q^ν/(1−q^ν)` with `z ∈ ℚ`, so it prints no rational-base region and
  cannot beat Bundschuh–Väänänen's `0.398679`.  On p. 880 it says: "Another special case,
  `z = 1` in (1), of the q-harmonic series, is considered in [Z2]. Our present methods do not
  allow us to sharpen the result in [Z2]", where [Z2] is Zudilin, Acta Arith. 111 (2004),
  the result homogenised here.  So the integer-base exponent `μ = 2.46497868…` remained the
  best printed bound for `F(p)` after 2006, and by Theorem C's identity `θ* = 1/μ` the
  region of Theorem A is the one this family of methods yields.  (Any future improvement of
  `μ(F(p))` by forms with `ℤ[p]`-integrality of Lemma-7 type and `p`-uniform size would
  enlarge the region to `1/μ_new` by the same proof; a bound `2.4234` would give `0.4126`
  and admit `29/4`.)
* Krattenthaler–Rochev–Väänänen–Zudilin 2009 (Acta Arith. 136) uses the same normalisation
  `γ = log|ρ|/log|σ| > c` for the `q`-exponential, not for `F`.

## 8. Classification of every step

| step | content | class |
|---|---|---|
| (9)–(11) identity `H_n = A_n F − B_n` | partial fractions, `|q| < 1` | (a) literature, valid for all real `x > 1` |
| Lemma 7 | `x^{−M} D_N Ω^{−1} H_n ∈ ℤ[x]F + ℤ[x]` | (a) literature, polynomial reading fixed by the paper's (24); (b) exact check `n ≤ 3` |
| (E1) `F ∉ ℚ(x)` | log singularity at `x → 1⁺` | (c) new, complete |
| (E2) transfer to explicit `U_n, V_n` | uniqueness from (E1) | (c) new, complete; (b) exact `n ≤ 3` |
| (E3) degrees, `K_n`, `W_n` | integer identities | (b) Lean `RationalBaseContour` + probes |
| (E4) positivity | product of positive factors | (c) new, complete |
| (E5) Archimedean size | Pochhammer bounds, cyclotomic tail | (c) new, complete; (b) numerics |
| (E6) `(K_n − W_n)/n² → C₀` | Lemmas 1, 2 at `p = 2` | (a) literature at integer `p`, plus elementary transfer |
| Steps 1–5 | homogenisation and contradiction | (c) new, complete |
| `81/200 < θ* < 1/2`, `31/4`, powers, `3/2` excluded | finite trigamma sums, `π` bounds | (b) Lean, axioms `propext, Classical.choice, Quot.sound` |
| Theorem C | exponent lemma + Dirichlet | (c) new, complete (the exponent lemma is standard) |

Every step is (a), (b), or (c) with a complete proof.  The evidence class of Theorems A–C is
therefore **ordinary complete proof citing published lemmas**, an unconditional theorem in the
usual mathematical sense.  What is not kernel-checked: Lemma 7 and Lemma 2 (published), the
identity (9)–(11), (E1), (E2), (E4), (E5), the exponent lemma, and the limit passage in Step 4.
What is kernel-checked: the finite part listed in `RationalBaseContour.lean` (build rc 0,
2778 jobs, no warnings; `#print axioms` on the fourteen named declarations shows only
`propext, Classical.choice, Quot.sound`, the integer identities only `propext, Quot.sound`).

## 9. Receipts

* `formal_math/probes/erdos1049_zudilin_region.py` → `state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_region/region_receipt.json`
* `formal_math/probes/erdos1049_zudilin_direction_search.py 30` → `…/direction_search_bound30.json` (and `bound22`)
* `formal_math/probes/erdos1049_zudilin_c0_c1_check.py`, `formal_math/probes/erdos1049_zudilin_exact_forms.py`, and the adversarial reconstruction `state/…/erdos1049_contour_adversary/` (constants, exact forms `n ≤ 3`)
* Lean: `ErdosProblems/Erdos1049/RationalBaseContour.lean`, build via `scripts/lean_fast_build.py --jobs 2 ErdosProblems.Erdos1049.RationalBaseContour`
* Derivation history: `ZudilinRationalHomogenisationDerivation.md` (2026-09-02), Type B attachment `attachments/typeb_return_8a7ad785.txt`
