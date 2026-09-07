# The height route and the transcendence route are one axis, and it is the support density

Status labels are strict. **[PROVED]** = elementary derivation given here.
**[COMPUTED]** = exact integer computation, reproducible from the named script.

Script: `scripts/height_complexity_dichotomy.py`.
Receipt: `state/formal_math/erdos257_period_noncollapse/height_complexity_dichotomy_receipt.json`.

## 0. Two deaths the corpus records separately

* `RunLengthMarginLawAndDivisorMultiplicity.md` section 10: *"The height route is separately
  dead — `ρ_n` has denominator `≈ 2^{0.3n²}` against a window of width `≈ (2/3)4^{−n}`."*
* `RunLengthMarginLawAndDivisorMultiplicity.md` section 14: the Mahler–Nishioka /
  Adamczewski–Bugeaud regime is sub-exponential subword complexity of `ε`, with a measured
  transition at support density `δ ≈ 2^{−5}`; the candidate rationals sit at `δ ≈ 1/2`.

They are the same axis. Putting them on it shows the height lane is not merely dead for the
current candidates — it is **dominated everywhere**.

## 1. The denominator exponent is linear in the density [PROVED + COMPUTED]

Let `A_N = A ∩ [1,N]` and `δ_N = |A_N|/N`. The greedy remainder
`ρ_N = y − Σ_{d ∈ A_N} w_d` has denominator dividing `q · lcm{2^d − 1 : d ∈ A_N}`, and the
cyclotomic factorisation `2^d − 1 = Π_{k | d} Φ_k(2)` gives exactly

    log2 lcm{2^d − 1 : d ∈ A_N}  =  Σ_{k ∈ Div(A_N)} log2 Φ_k(2),                      (H)

`Div(A_N)` being the set of divisors of elements of `A_N`. Since `log2 Φ_k(2) = φ(k) + O(1)`
and `Div(A_N) ⊇ A_N`, (H) is at least `Σ_{d ∈ A_N} φ(d) ≫ δ_N N²`.

**[COMPUTED]** exactly, `N = 400`, synthetic supports of prescribed density `1/dd`:

| `δ` | 1 | 1/2 | 1/4 | 1/8 | 1/16 | 1/32 | 1/64 |
|---|---|---|---|---|---|---|---|
| `log2 den` | 48458 | 24299 | 12061 | 6113 | 3149 | 1443 | 754 |
| `log2 den / (δ N²)` | 0.3029 | 0.3037 | 0.3015 | 0.3056 | 0.3149 | 0.2886 | 0.3016 |

The normalised constant is flat at `≈ 0.302` across a 64-fold range of density — and
`0.302` is `3/π² = 0.30396`, i.e. `Σ_{k≤N} φ(k) / N²`. So

    log2 den  ≈  (3/π²) · δ_N · N².                                                    (D)

For the **actual** greedy supports the constant is a little higher (a generic density-`1/2`
set has a richer divisor closure than an arithmetic progression): `log2 den / (δ N²)` sits
at `0.34–0.39` over `1/2, 1/21, 4/9, 1/465, 1/5, 5/12` at `N = 100 … 700`, giving
`log2 den ≈ 0.15–0.19 N²` — consistent with section 10's `0.3n²` to within the constant.

## 2. What a height argument needs [PROVED]

Separation needs `|v − p/q| ≥ 1/den` to beat the fatal window `G_N ≈ (2/3)4^{−N}`, i.e.

    log2(den)  ≤  2N + O(1).                                                           (T)

With (D) that is `(3/π²) δ_N N² ≤ 2N`, i.e.

    δ_N  ≤  2π²/(3N)  ≈  6.6 / N.                                                      (C)

**The height route needs support density `O(1/N)` — density exactly zero, and thin enough
that `Σ_{d ∈ A} 1/d` barely diverges.** At `N = 700` the measured gap is a factor `≈ 64`:
`log2 den ≈ 90,000` against a budget of `1400`.

## 3. The dichotomy [PROVED, one-way]

The transcendence route's reach is a **fixed** density threshold — section 14 measures the
subword-complexity transition at `δ ≈ 2^{−5} = 0.03125`, below which `ε` has near-linear
complexity. The height route's threshold (C) is **`δ = O(1/N)`, which tends to zero.**
Equating them:

    6.6 / N  =  2^{−5}     ⟹     N ≈ 212.

> **For every `N ≳ 212`, the height route requires a strictly sparser support than the
> density at which the complexity machinery already applies.** Its viable regime is
> contained in — and shrinking inside — the regime the Mahler–Nishioka /
> Adamczewski–Bugeaud lane already covers. So there is no target the height route could
> separate that the complexity lane does not already reach.

This is why the two deaths in sections 10 and 14 are not independent bad luck. They are one
inequality read at two densities, and the ordering between them is strict and permanent.

## 4. What this does not claim

* Nothing here proves or refutes Erdős 257, and nothing here proves any irrationality.
  Section 14's claim boundary stands verbatim: "sub-exponential complexity" is strictly
  weaker than the hypotheses of Mahler–Nishioka or Adamczewski–Bugeaud, so *neither* lane
  currently closes any target.
* The `δ ≈ 2^{−5}` threshold is **[COMPUTED]** (section 14), not a theorem, so the crossover
  `N ≈ 212` inherits that status. The direction of the containment does not: (C) tends to
  zero and any fixed threshold does not, so the ordering is permanent regardless of where
  the complexity threshold actually sits.
* It says nothing about the carry lane, the prime skeleton, or the non-linear residual of
  `CertificateSocketCollapse.md` 73.4.
