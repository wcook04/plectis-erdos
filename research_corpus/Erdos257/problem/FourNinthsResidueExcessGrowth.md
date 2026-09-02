# 4/9 diagonal: the residue-certificate suffix is Θ(log d), hence unbounded

Status labels are strict. **[COMPUTED]** = exact integer computation, reproducible from the
named script. **[HEURISTIC]** = model-based, not a theorem.

Script: `scripts/four_ninths_residue_excess_growth.py`.
Receipt: `state/formal_math/erdos257_period_noncollapse/four_ninths_residue_excess_growth_receipt.json`.

## 0. The directive this executes

`FourNinthsDiagonalMarginInvariant.md` closes with an unexecuted instruction — *"Any next
computation should discriminate arithmetic descriptions of those overshoots, not merely
extend the trajectory horizon"* — and states the gap it leaves precisely: the residue
audit's finite facts *"neither prove that the required suffix excess is unbounded nor rule
out a genuinely nonlocal use of (5)."*

This decides the first half of that, and the outcome is two-sided by construction.

## 1. What was measured

The surviving 4/9 socket is `b_d = 1 ⟹ d ≤ ρ_d` (3). The history identity
`ρ_d = Σ_{0≤j<d} 4^(d−1−j) q_j` makes `ρ_d mod 4^k` depend only on the last `k` increments,
so the residue certificate `ρ_d mod 4^k ≥ d` would certify (3). For each selected rank let
`base_k` be the least `k` with `4^k > d`, and let the **excess** be the least additional
number of base-four digits making the certificate hold.

**Prediction, declared in the script before the run.** Modelling `ρ_d mod 4^k` as
equidistributed gives `P[excess ≥ e] ≈ 4^(−e)`, a geometric law independent of `d`. The
maximum over a dyadic band of `~2^i` ranks is then `~log₄(2^i) = i/2`: **P1** the max excess
grows linearly in the band index, **P2** with fitted slope in `[0.3, 0.8]`, **P3** the base
certificate first fails at rank 20 with `ρ₂₀ mod 64 = 12`. Falsifier: a plateau, which would
reopen the fixed-suffix route.

## 2. Result [COMPUTED]

Horizon 200,000; 100,098 selected ranks; **zero landing-rank violations**.

Three calibrators, all hit:

* bit prefix `010110110001` and `ρ₁₂ = 2460` reproduced — the Lean base fixture;
* first base-certificate failure at **rank 20, `base_k = 3`, `ρ₂₀ mod 64 = 12`** — the exact
  value `FourNinthsDiagonalMarginInvariant.md` records;
* **max excess 14 at rank 146803** — again the exact value that note records, reached here
  by an independently written instrument.

| band `i` | ranks | max excess | at rank | `base_k` | total `k` | `log₂ d` |
|---:|---|---:|---:|---:|---:|---:|
| 6 | `[2^5,2^6)` | 2 | 37 | 3 | 5 | 5.2 |
| 8 | `[2^7,2^8)` | 4 | 146 | 4 | 8 | 7.2 |
| 10 | `[2^9,2^10)` | 7 | 968 | 5 | 12 | 9.9 |
| 12 | `[2^11,2^12)` | 7 | 2530 | 6 | 13 | 11.3 |
| 14 | `[2^13,2^14)` | 6 | 16090 | 7 | 13 | 14.0 |
| 15 | `[2^14,2^15)` | 6 | 25002 | 8 | 14 | 14.6 |
| 16 | `[2^15,2^16)` | 9 | 45203 | 8 | 17 | 15.5 |
| 17 | `[2^16,2^17)` | 7 | 75770 | 9 | 16 | 16.2 |
| 18 | `[2^17,2^18)` | **14** | 146803 | 9 | 23 | 17.2 |

**Fitted slope over 13 bands: `0.6648`**, against the predicted `~0.5` and inside the
declared `[0.3, 0.8]`. **P1, P2 and P3 all confirmed; the falsifier did not fire.**

## 3. Reading

> **The required suffix excess is unbounded, and the total window `k` tracks `log₂ d`.**

Two consequences, in opposite directions, and both matter for allocation.

* **Negative, and it closes something.** No *fixed*-suffix residue certificate can work. The
  existing audit rejected the least natural `k`; this says the failure is structural rather
  than a horizon artefact — any constant `k` is defeated once the horizon passes `~4^k`. A
  proof of (3) cannot be a bounded-suffix argument.
* **Positive, and it is the useful half.** The window is only **logarithmic**. Total `k`
  sits at `log₂ d` plus max-statistic fluctuation (`k = 14` at `d = 25002` against
  `log₂ d = 14.6`; `k = 17` at `d = 45203` against `15.5`). So an adaptive certificate needs
  the last `Θ(log d)` increments — not a bounded window, but not a polynomial one either.
  This is outside the closeout's forbidden *"bounded window of divisor loads"* class, and it
  is why the depth-twelve local countermodel does not reach it: that countermodel fixes a
  constant depth, and the requirement grows.

**This quantifies what an adaptive proof must control, which was previously unknown.**

## 4. The other half of the directive: what the finite audits are worth [COMPUTED]

Script: `scripts/four_ninths_landing_distribution.py`.
Receipt: `state/formal_math/erdos257_period_noncollapse/four_ninths_landing_distribution_receipt.json`.

`FourNinthsDiagonalMarginInvariant.md` records "zero violations through rank 200000" and
"nonnegative through ten million ranks" as *"finite evidence only"* — without saying what
that evidence is worth. At a take, `ρ_d = T_d − (2^d + 1) < 2^d`, so the natural
normalisation is `x_d := ρ_d / 2^d ∈ [0,1)`. Predictions declared before the run: a flat
decile histogram, no `x_d ≥ 1`, `min x_d` of order `1/N`, and min slack `0` at rank 2 as the
unique record low.

Horizon 60,000; 30,247 takes; **zero landings with `x_d ≥ 1`**.

| decile | count | share |
|---|---:|---:|
| `[0.0,0.1)` | 2924 | 9.67% |
| `[0.1,0.2)` | 3030 | 10.02% |
| `[0.2,0.3)` | 3087 | 10.21% |
| `[0.3,0.4)` | 3084 | 10.20% |
| `[0.4,0.5)` | 3003 | 9.93% |
| `[0.5,0.6)` | 3008 | 9.94% |
| `[0.6,0.7)` | 3040 | 10.05% |
| `[0.7,0.8)` | 3001 | 9.92% |
| `[0.8,0.9)` | 3049 | 10.08% |
| `[0.9,1.0)` | 3021 | 9.99% |

**Max decile deviation from 10.00%: 0.33 pp.** `min x_d = 1.17×10⁻⁴` at rank 5270 against
the uniform order statistic `1/N = 3.31×10⁻⁵` — same order. Min slack `ρ_d − d = 0` at rank
2, the unique record low, reproducing the invariant note. All four predictions hold; the
depleted-lowest-decile falsifier did not fire.

**Consequence.** Under the measured equidistribution the socket's per-rank failure
probability is `d·2^(−d)`, so the residual risk beyond depth `D` is `~2D·2^(−D)`:

| beyond `D` | 12 | 100 | 1000 | 60,000 | 200,000 | 10⁷ |
|---|---|---|---|---|---|---|
| risk | `10^−2` | `10^−28` | `10^−298` | `10^−18057` | `10^−60200` | `10^−3010293` |

This is a **sharply different situation from the generic Erdős-257 fatal window**, whose
relative width is `~2^(−n)` with total risk `O(1)` spread across ranks
(`SupportWordStructureLab.md` §4g). Here the risk is super-exponentially concentrated at
tiny `d` — which is exactly why rank 2 is the unique record low — so finite verification
buys essentially everything beyond it. The existing audits are worth far more than "nothing
broke": at the depth already reached they leave residual risk `10^−3010293`.

**Claim boundary, and it is the whole of the caveat.** Equidistribution is **measured, not
proved**. The tail figure is a heuristic confidence statement about a deterministic orbit —
not a probability, not a theorem. If the orbit has hidden structure enriching small
landings, the estimate is wrong, and that is precisely what the lowest-decile falsifier
tests. It does not prove the socket, does not prove `4/9 ∈ 𝒞`, and does not decide
Erdős 257. Under the closeout's allocation guard it is calibration evidence.

## 5. What this does not claim

* Nothing here proves or refutes Erdős 257, and nothing here proves (3).
* The growth is **[COMPUTED]** on one target to horizon 200,000. It does not prove the
  excess is unbounded for all depths; it shows the measured growth is linear in the band
  index with a fitted slope, and that no constant suffix survives the measured range.
* The geometric model behind P1/P2 is **[HEURISTIC]**. It predicted the observed slope, but
  agreement with a model is not a theorem about the orbit.
* It supplies no producer. Per the closeout's allocation guard this is falsification and
  calibration evidence, not a new route.
