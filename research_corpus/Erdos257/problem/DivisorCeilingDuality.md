# The divisor ceiling's slack is the dual carry

Status labels are strict. **[PROVED]** = elementary derivation given here.
**[COMPUTED]** = exact rational computation, reproducible from the named script.

Script: `scripts/divisor_ceiling_duality.py`.
Receipt: `state/formal_math/erdos257_period_noncollapse/divisor_ceiling_duality_receipt.json`.

## 0. The open item this answers

`scripts/carry_divisor_bound.py` records the necessary arithmetic condition on the
forward integer carry `C_m = 2C_{m-1} + eps_m - tau_A(m)`:

    0 <= C_m <= Theta(m) := sum_{k>=1} tau(m+k) 2^-k,                             (0)

because `C_m = floor(2^m sum_{j>m} tau_A(j) 2^-j)` and `tau_A <= tau`. Its docstring
leaves one branch open, verbatim:

> "A ratio bounded away from 1 means the divisor bound is slack and cannot be the
> binding constraint; a ratio approaching 1 infinitely often means it is."

That branch is settled below — not by measurement alone, but by identifying the slack.

`CertificateSocketCollapse.md` section 19 already closes every **linear** functional of
the ceiling (each one aggregates to the vacuous `y <= E - 1`), and section 73.4 narrows
the surviving residual to a **non-linear** use. This note does not enter that residual.
It closes the remaining *quantitative* question about the ceiling itself.

## 1. A closed form for the ceiling [PROVED]

Write `rho_d(m)` for the least `k >= 1` with `d | (m+k)`, i.e. `(-m) mod d` taken in
`{1,...,d}`. For **any** index set `B`, swapping the order of summation,

    S_m(B) := sum_{k>=1} tau_B(m+k) 2^-k
            = sum_{d in B} 2^-rho_d(m) * 2^d / (2^d - 1).                          (1)

(`scripts/carry_closed_form.py` records (1) for `B = A`; the point here is that it holds
for every `B`.) Taking `B = N` gives a closed form for the ceiling with **no support in
it at all**:

    Theta(m) = sum_{d>=1} 2^-rho_d(m) * 2^d / (2^d - 1),                           (2)

and splitting `N` into `A` and its complement,

    Theta(m) = S_m(A) + S_m(A^c)        for every m.                               (3)

**The ceiling's slack is not an accident of `A`: it is exactly the divisor supply of the
complement support.** The set-level complement symmetry is already in the corpus
(`SupportWordStructureLab.md`: `E - x = sum_{a not in A} z_a`, used in
`RunLengthMarginLawAndDivisorMultiplicity.md` section 13 to prove the exact `1/2`
survival rate). (3) is that symmetry read in the **carry** coordinate, which is where the
open question lives.

## 2. The complement is the dual greedy support [PROVED]

Since `sum_{d<=N} w_d = E - Tail_N`, for any target `y` with support `A`,

    (E - y) - sum_{d in A^c, d<=N} w_d  =  Tail_N - r_N  =  B_N,                   (4)

which is exactly the corpus's **complement budget** `B_N` (the object
`exclude_half_complement_budget_overspend` is about). So the complement budget is
literally the greedy remainder of the dual target `E - y`. If `y` survives then
`sum_{d in A} w_d = y`, hence `sum_{d in A^c} w_d = E - y`, and uniqueness of the
Mersenne representation makes `A^c` **the** greedy support of `E - y`.

So `S_m(A^c)` in (3) is not an auxiliary quantity: it is the carry functional of another
genuine surviving Erdős-257 target.

## 3. The ceiling is never tight [PROVED]

`rho_d(m) <= d` gives `2^-rho_d(m) * 2^d/(2^d-1) >= w_d`. Let
`D_0 := max{d : w_d > y}`, so `1..D_0` can never be selected. Then

    Theta(m) - C_m  >=  Theta(m) - S_m(A)  =  S_m(A^c)  >=  sum_{d <= D_0} w_d.     (5)

For every surviving `y < 1` — which is every candidate in this corpus, since
`𝒜 ∩ (0,1) = 𝒜 ∩ (0, E-1]` — this is `>= w_1 = 1`. **Equality in (0) is impossible at
every `m`, for every target.** (For `y >= 1` apply the same statement to the dual
`E - y <= E - 1`; the involution covers both branches.)

## 4. The open branch, converted [PROVED]

Dividing (3) by `Theta(m)`, and writing `r_m(y) := C_m / Theta(m)`:

    r_m(y) + S_m(A^c)/Theta(m) = 1 + O(1/Theta(m)),

the error being only the floor in `C_m = floor(S_m(A))`. So

> **`r_m(y) -> 1` if and only if the dual target `E - y` has carry `o(Theta(m))`,**
> i.e. if and only if `A^c` has asymptotically vanishing weighted divisor supply.

That is the exact content of the branch `carry_divisor_bound.py` left open, and it is now
a statement about a *dual surviving target of the same kind*, not about a bound. Since
`A` and `A^c` are complementary and (5) is uniform, the ratio is a **symmetric** statistic
on dual pairs: it cannot approach 1 for `y` without approaching 0 for `E - y`.

**Claim boundary.** (5) is a constant lower bound while `Theta(m) ~ log m`, so (5) alone
does *not* forbid `r_m -> 1`. What forbids it in practice is that `S_m(A^c)` is itself a
carry of a surviving target and grows at the same rate; that growth is **[COMPUTED]**,
not proved. The honest status is: the branch is reduced to a dual-carry vanishing
statement, and measured against it.

## 5. Measurement [COMPUTED]

`scripts/divisor_ceiling_duality.py`, exact `Fraction` arithmetic, `K = 64` so every
truncation is far below the compared quantities. Identities (1)(2)(3) and the floor
relation `C_m = floor(S_m(A))` are checked at every tested rank; the ratio is resolved by
dyadic band so that "no drift toward 1" is measured rather than assumed.

Depth 4000, six surviving targets, 362 ranks each sampled across dyadic bands 6–12
(`m` from 32 to ~4000):

| `y` | `D_0` | max `C` | swap (1) | split (3) | floor | min slack | proved LB (5) | max `C/Theta` | mean `C/Theta` |
|---|---|---|---|---|---|---|---|---|---|
| `1/21` | 4 | 13 | 0 | 0 | ok | 2.1415 | 1.5429 | 0.5506 | 0.2990 |
| `4/9` | 1 | 14 | 0 | 0 | ok | 2.1421 | 1.0000 | 0.6474 | 0.3563 |
| `1/465` | 8 | 11 | 0 | 0 | ok | 2.4969 | 1.6028 | 0.4966 | 0.2237 |
| `1/5` | 2 | 13 | 0 | 0 | ok | 2.1415 | 1.3333 | 0.6216 | 0.2912 |
| `5/12` | 1 | 14 | 0 | 0 | ok | 2.2466 | 1.0000 | 0.6247 | 0.3465 |
| `1/2` | 1 | 13 | 0 | 0 | **off(362)** | 1.8917 | 1.0000 | 0.6789 | 0.4099 |

Max `C_m/Theta(m)` by dyadic band — a drift toward 1 would show as a rising row:

| `y` | b6 | b7 | b8 | b9 | b10 | b11 | b12 |
|---|---|---|---|---|---|---|---|
| `1/2` | 0.679 | 0.651 | 0.543 | 0.592 | 0.638 | 0.601 | 0.679 |
| `1/21` | 0.483 | 0.523 | 0.470 | 0.551 | 0.496 | 0.542 | 0.477 |
| `1/465` | 0.339 | 0.394 | 0.447 | 0.485 | 0.444 | 0.445 | 0.497 |
| `1/5` | 0.483 | 0.481 | 0.562 | 0.481 | 0.519 | 0.622 | 0.583 |
| `4/9` | 0.566 | 0.607 | 0.571 | 0.606 | 0.598 | 0.541 | 0.647 |
| `5/12` | 0.539 | 0.571 | 0.484 | 0.590 | 0.554 | 0.595 | 0.625 |

Over a 64-fold range of `m` every entry stays in `[0.34, 0.68]`. Individual targets are
flat to mildly rising (`1/465` 0.339 → 0.497, `1/2` 0.679 → 0.679); none approaches 1.

**Corrected against a deeper measurement.** `CertificateSocketCollapse.md` section 87.2 runs
`carry_divisor_bound.py` at depth **100,000** and reports the running maximum over three
depths:

| `y` | 8000 → 30000 → 100000 | increments |
|---|---|---|
| `4/9` | 0.68488 → 0.73437 → **0.78916** | `+0.049, +0.055` (accelerating) |
| `1/21` | 0.62390 → 0.66131 → 0.67800 | `+0.037, +0.017` |
| `1/465` | 0.59073 → 0.61826 → 0.63698 | `+0.028, +0.019` |
| `5/12` | 0.69831 → 0.71367 → 0.72287 | `+0.015, +0.009` |
| `1/5` | 0.69959 → 0.71021 → 0.71021 | stalled, same rank `m = 22864` |
| `1/2` | 0.74950 → 0.74950 → 0.75459 | nearly flat |

Zero excursions above `0.9` at any depth, and none above `0.99` — so the qualitative
reading (the ceiling is slack, and never tight) survives. But the maxima do climb past the
`[0.34, 0.68]` band measured here, `4/9` reaching `0.789`, and section 87.2's verdict is
that **the data supports neither extrapolation**: four of six targets decelerate, one has
stalled outright, and only `4/9` accelerates.

So the conservative statement is narrower than the one first written here: **no excursion
above `0.9` at any measured depth up to 100,000, and the direction of the slow drift is
undetermined.** The earlier phrasing — "no approach to 1 over the tested range, which is
what the duality predicts" — over-read on two counts: it generalised a depth-4000 band, and
the duality does not by itself predict boundedness. What the duality gives is (5) and the
equivalence in §4; the asymptotics remain open.

Three things to read off the table:

* `swap(1) = split(3) = 0` everywhere — identities (1) and (3) are exact, on
  `6 × 362 = 2172` ranks, in exact integer arithmetic scaled by `2^K`.
* `min slack >= proved LB` in all six cases — inequality (5) holds with room.
* `floor_relation_violations > 0` exactly for the **dyadic** target `1/2`. That is not an
  error: it independently reproduces the transducer degeneracy recorded in
  `RunLengthMarginLawAndDivisorMultiplicity.md` section 11 (for dyadic `y` a seed below the
  true carry stays one below forever). Identities (1)–(5) are unaffected.

## 6. The mean half of the phase–scale coupling is exact [PROVED + COMPUTED]

`Erdos257ResearchFrontierCloseout.md` marks dense-support / LCM clocks as *"the main
orthogonal positive route, with phase–scale coupling as the required new content"*, noting
that *"reciprocal divergence supplies mass and common multiples supply pulses, but no theorem
controls pulse phase and carry scale together."*

The closed form (1) is already a phase–scale object: each `d ∈ A` contributes
`2^(−ρ_d(m)) · 2^d/(2^d − 1)`, depending only on its **phase** `ρ_d(m)` — the distance from
`m` to the next multiple of `d` — weighted by **scale** `2^(−ρ)`. The mean half closes
exactly.

**[PROVED]** As `m` runs over one period of `d`, `ρ_d(m)` takes each value in `{1,…,d}` once,
so the mean contribution is

    (1/d) · (2^d/(2^d−1)) · Σ_{r=1}^{d} 2^(−r)
      = (1/d) · (2^d/(2^d−1)) · (1 − 2^(−d))
      = 1/d.

The exponential weighting is **mean-preserving**: the phase weight `2^(−ρ)` and the Mersenne
normalisation `2^d/(2^d−1)` cancel exactly. By linearity,

> **`mean_m C_m = Σ_{d ∈ A} 1/d`, exactly.**

So "reciprocal divergence supplies mass" is this identity, with constant exactly `1`.

**[COMPUTED]** Exact rational check, `d = 1 … 24`: mean `= 1/d` in every case, no exceptions.
Support level, empirical mean over 200,000 ranks with `A ∩ [1,60]`: `1/21` gives `1.505817`
against `Σ1/d = 1.505872`; `4/9` gives `2.045528` against `2.045576`; `1/5` gives `1.541742`
against `1.541788` — relative error `2–4 × 10^(−5)`, consistent with finite-range truncation.

**What this does and does not settle.** It closes the *mean* half of the coupling in closed
form and thereby isolates the rest: since the mean is exactly `Σ 1/d` and carries no phase
information, **the whole of the missing phase–scale content is in the fluctuation, not the
mean.** Any future coupling theorem must control the deviation of `C_m` from `Σ_{d∈A,d≤m} 1/d`,
because the mean is already pinned. This is a dictionary entry on the named route, not a
producer, and it does not meet the closeout's allocation-guard bar.

## 7. What this does not claim

* Nothing here proves or refutes Erdős 257.
* It does not enter the non-linear residual of `CertificateSocketCollapse.md` 73.4; (3) is
  a linear identity and inherits that section's verdict for any *aggregated* use.
* It does not bound `C_m`. It says the crude divisor ceiling is the wrong object to bound
  it with, and says exactly why: the slack is another target's carry.
* The `~ log m` growth of `S_m(A^c)` is measured, not proved.
