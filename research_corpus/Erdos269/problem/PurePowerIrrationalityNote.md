# Irrationality of the pure prime-power running-LCM series

**Claim boundary, stated first.** This is **not** Erdős #269. Erdős #269 asks
about `S = Σ_{smooth s ≥ 2} 1/H(s)`, which remains open. What is proved here is
the irrationality of the **one-channel sub-series** `Σ_p = Σ_{m≥1} 1/H(p^m)`,
carried by the pure powers of a single prime. The proof is elementary and
unconditional. Its interest is twofold: it is a genuine unconditional
irrationality theorem in the #269 family, and it isolates in one line exactly
what makes `S` hard.

Companion Lean module: `ErdosProblems.Erdos269.PurePowerIrrationality`
(green focused build, no `sorry`; four theorems, the arithmetic core).
Checker: `scripts/check_erdos269_pure_power_irrationality.py`.

**Novelty: UNVERIFIED.** The argument is elementary and of a standard type
(small nonzero linear forms, Sturmian right-special factors, Cantor series with
bounded radices). For `r = 2` the statement is already known and strictly
weaker than what is known — Hecke–Mahler gives transcendence there. Whether the
`r ≥ 3` case is new, folklore, or already in the Cantor-series / Ostrowski
literature has **not** been checked against external sources. Do not present
this as new until a prior-art pass has been run. What is verified is that the
proof is correct, and that it does not reach `S`.

## 0. Setting

Fix distinct primes `p_1 < … < p_r`, `r ≥ 2`, and let

    H(x) = ∏_i p_i^{⌊log_{p_i} x⌋}

be the running LCM of the smooth prefix. Fix one channel `p = p_i` and put

    Σ_p = Σ_{m≥1} 1/H(p^m),
    H_M = H(p^{M-1}),
    y_M = H_M · Σ_{m≥M} 1/H(p^m),
    b_m = H(p^{m+1}) / H(p^m).

For `{2,3,5}` with `p = 2`: `b_m ∈ {2,6,10,30}` and

    Σ_2 = 0.5931259677635827115280234…

**Theorem.** `Σ_p` is irrational.

Also verified exactly: `Σ_{p∈{2,3,5}} (p−1)·Σ_p = 1` (the landed telescope), so
the three channel values are rationally dependent even though each is irrational.

## 1. The three structural facts

**(C) Clearing.** For `m < M`, `H(p^m) ∣ H_M`, because every exponent
`⌊log_q p^m⌋` is monotone in `m`. Hence

    y_M = H_M·Σ_p − (integer).                                     (1)

**(R) Range and recurrence.** `0 < y_M < 1`, and

    y_{M+1} = b_{M-1}·y_M − 1.                                     (2)

(2) is just `b_{M-1}·y_M = 1 + y_{M+1}`, read off the definition. `y_M < 1`
because every `b ≥ 2` and not all of them equal `2`.

**(I) Interval confinement.** Combining (2) with `0 < y_{M+1} < 1`:

    y_M ∈ ( 1/b_{M-1} , 2/b_{M-1} ).                               (3)

For `{2,3,5}`, `p = 2`, this reads

| `b` | interval |
|---|---|
| 2 | (0.5000, 1.0000) |
| 6 | (0.1667, 0.3333) |
| 10 | (0.1000, 0.2000) |
| 30 | (0.0333, 0.0667) |

Two intervals are disjoint exactly when `max(b,b′) > 2·min(b,b′)`. Every pair
qualifies except `{6,10}` — and `{6,10}` is a *simultaneous* flip of both odd
channels, so it never arises from a single-channel flip.

**This is the whole point.** The confining interval of the state is determined by
the *current radix letter alone*. That is available only because every Cantor
digit here equals `1`. For `S` the digits are dyadic-shell lattice counts growing
like `n²`, the state grows like `a²`, and no interval confinement exists —
which is precisely why the same argument does not touch #269.

## 2. The combinatorial input

The radix word `(b_m)` is determined by the `r−1` Beatty sequences
`δ_q(m) = ⌊(m+1)log_q p⌋ − ⌊m log_q p⌋`, each a Sturmian word of irrational
slope. For `{2,3,5}` the joint word has exactly `(N+1)²` factors of length `N`
(measured; `|W_3| = |W_5| = N+1`, `|W_b| = (N+1)²`).

For every `L` there is a **right-special** factor `u` of length `L`: a word with
two distinct one-letter extensions `ua`, `ua′`. Take `u` right-special in one
odd channel, with the other channel's window fixed; density of
`{(m·log_3 2, m·log_5 2)}` in `T²` makes both product cells nonempty, so both
extensions occur. The two extensions then differ by exactly one prime factor
`q ≥ 3`, so `a′ = q·a` and the pair is separated in the sense of (3).

**Measured caution.** Two factors of length `N` at Hamming distance one exist
**only** at positions `0` and `N−1` — never in the interior. (Counts at
`N = 8, 12, 17`: positions `{0, N−1}` only.) An earlier version of this argument
tried to place the flip at depth `≈ N/2` and is false. The proof must use the
*right-special* (last-position) flip, and nothing else.

## 3. The proof

Fix `L`. Let `u` be right-special of length `L` with separated extensions
`a, a′ = q·a`, `q ≥ 3`, and let `M ≠ M′` be occurrences of `ua`, `ua′`. Write
`P = ∏ u` for the product of the common prefix, so `P ≥ 2^L`. Splitting both
states after the common prefix,

    y_M − y_{M′} = ( y_{M+L} − y_{M′+L} ) / P.                     (4)

By (3), `y_{M+L} ∈ (1/a, 2/a)` and `y_{M′+L} ∈ (1/(qa), 2/(qa))`, and since
`q ≥ 3`,

    y_{M+L} − y_{M′+L} > 1/a − 2/(3a) = 1/(3a) ≥ 1/(3·30).

Hence, with `κ = 1/90`,

    0 < κ/P ≤ | y_M − y_{M′} | ≤ 1/P ≤ 2^{−L}.                     (5)

By (1), `y_M − y_{M′} = (H_M − H_{M′})·Σ_p − (integer)`, and `H` is strictly
increasing so `n := H_M − H_{M′} ≠ 0`. Since `|y_M − y_{M′}| < 1`, the nearest
integer is the one above, so

    ‖ n·Σ_p ‖ = | y_M − y_{M′} | ∈ ( 0 , 2^{−L} ].                  (6)

Now suppose `Σ_p = A/B`. Then `‖n·Σ_p‖` lies in `(1/B)·Z`, so any nonzero value
is at least `1/B`. Taking `L` with `2^{−L} < 1/B` contradicts (6). ∎

The argument is the classical "arbitrarily small nonzero linear form" criterion;
all the work is in producing forms that are provably **nonzero**, which (3)+(4)
deliver and which no argument for `S` currently does.

## 4. What is checked

`scripts/check_erdos269_pure_power_irrationality.py`, integers and `Fraction`
only, no floating-point logarithms. Every state is bracketed rigorously by
`y_M ∈ (A, A + 1/P)` using `0 < y_{M+depth} < 1`.

* (T) telescope `Σ_p (p−1)Σ_p = 1` exact to the truncation cutoff;
* (C) clearing: 0 failures;
* (I) confinement `y_M ∈ (1/b, 2/b)`: 0 failures in 1,500 scales;
* (S) a separated right-special factor found at every tested length, scanning
  10,000 positions;
* (G) gaps, with exact rational brackets:

| L | M | M′ | a | a′ | 1/P | gap | nonzero | bits of \|n\| |
|---|---|---|---|---|---|---|---|---|
| 4 | 19 | 3 | 6 | 30 | 2.778e−04 | 3.703e−05 | yes | 52 |
| 8 | 1 | 540 | 2 | 10 | 1.286e−07 | 5.215e−08 | yes | 1617 |
| 12 | 4 | 1012 | 6 | 30 | 1.191e−11 | 1.588e−12 | yes | 3031 |
| 16 | 3 | 133 | 10 | 30 | 3.308e−15 | 2.205e−16 | yes | 394 |
| 20 | 3 | 1206 | 6 | 30 | 9.188e−19 | 1.225e−19 | yes | 3613 |
| 24 | 312 | 3 | 2 | 6 | 8.507e−23 | 2.836e−23 | yes | 931 |
| 28 | 2 | 2828 | 2 | 10 | 3.939e−26 | 1.575e−26 | yes | 8479 |

Each gap is a nonzero rational lying below `1/P`, and the multiplier
`n = H_M − H_{M′}` is a nonzero integer of up to 8,479 bits. So the linear forms
`n·Σ₂ − (integer)` are provably nonzero and shrink geometrically, which is the
whole content of the theorem.

## 5. Reach, and what it does not give

*Reach.* The argument uses only: clearing, `0 < y < 1`, the all-ones recurrence,
and the existence of right-special factors with a non-dyadic flip. So it proves
irrationality of `Σ_{m≥1} 1/H(p^m)` for **every** channel of **every** finite
prime support with `r ≥ 2`, and likewise for the merged pure-power series
`Σ_j 1/H(r_j)` over the ordered prime-power ladder, whose digits are also all
`1`. For `r = 2` the conclusion is already known and stronger (Hecke–Mahler
gives transcendence); the content is `r ≥ 3`.

*What it does not give.* Nothing about `S`. The single hypothesis that fails for
`S` is the all-ones digit sequence: `S`'s ladder digits `C_j` are counts of
smooth numbers in an inter-boundary gap, growing like `j²`, so the normalized
tail state grows like `a²` (`X_a ≥ (1/60)(⌊a/(2log₂3)⌋+1)(⌊a/(2log₂5)⌋+1)`) and
(3) has no analogue. In the mod-1 picture the state `θ_a = {X_a}` *is* confined
to `(0,1)`, but its digits `ε_a = ⌊b_a θ_a⌋` are then no longer constant and are
not a function of the radix word, so no right-special factor of the radix word
separates two `θ`-states. The gap between this theorem and #269 is exactly the
gap between a constant digit sequence and one of unknown subword complexity.

## 6. A criterion for `S` that this suggests

Under rationality `S = p/q`, the proper (carry-normalized) digit word
`ε_a = ⌊b_a{X_a}⌋` satisfies

    P_ε(n) ≤ q · P_b(n) ≤ q·(n+1)² ,

because the window `(ε_a,…,ε_{a+n−1})` is a function of `({X_a}, b_a,…,b_{a+n−1})`
and `{X_a}` takes at most `q` values, while the radix word is a product of two
Sturmian words. Contrapositive: **superquadratic subword complexity of the
proper digit word implies `S` is irrational**, and `q ≥ P_ε(n)/(n+1)²` for every
`n`. This is the corrected home for the entropy intuition: the retired
Adamczewski–Bugeaud route measured the complexity of the *radix* word, which is
`Θ(n²)` and therefore useless; the digit word is the object whose complexity is
unconstrained a priori.
