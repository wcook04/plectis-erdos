# Erdős 257: gap-avoidance reduction, and the measured absence of any local mechanism

Status labels are strict. **[PROVED]** = elementary derivation given here.
**[COMPUTED]** = exact/verified-precision computation, reproducible from the scripts named.
**[HEURISTIC]** = model-based extrapolation, not a theorem.

## 1. Exact reduction [PROVED]

Coins `w_k = 1/(2^k - 1)` are strictly superincreasing: `w_n > Tail_n := sum_{k>n} w_k`.
Hence every value has at most one representation and greedy is forced. With
`rho_0 = y`, `rho_n = rho_{n-1} - w_n` if `rho_{n-1} >= w_n`, else `rho_n = rho_{n-1}`:

* the run survives iff `rho_n <= Tail_n` for every `n`;
* taking preserves that invariant automatically;
* so the **only** failure is a skip landing in the Cantor gap

        rho_{n-1} in ( Tail_n , w_n ),      width  G_n = w_n - Tail_n ~ (2/3)·4^-n.

Equivalently, in `beta_n := 2^n rho_n`: `beta_n = 2 beta_{n-1} - b_n·2^n/(2^n-1)`.

> **`y` is achievable by an infinite `A` iff its greedy orbit never enters a gap.**
> The gaps are explicit: for each finite `F` with `max F = n`, the interval
> `(sigma_F - G_n, sigma_F)` immediately below the finite sum `sigma_F = sum_{d in F} w_d`.
> So **Erdős 257 asserts that the finite Mersenne sums approximate every rational
> from above to within `G_{max F}`** — an approximation `2^n` times sharper than the
> `2^-n` spacing of those sums predicts.

Verified in `scripts/beta_gap_reduction.py`: this reproduces the corpus's own greedy
supports exactly (1/21 -> 5,7,8,9,10,11,13,16,18,20,22,24,...; 1/465 -> 9,13,14,17,19,21,...)
with no divisor counts, no LCM, no carries, no Boolean ancestry.

## 2. Measured failure law [COMPUTED]

323,825 random targets `p/q`, `q` odd near 10^9, exact fixed point (M = 2R+96 bits):

* fatal 50.04%, alive at depth 64 **49.96%**;
* `P(fatal at n) = 0.25 · G_n/w_n` to within sampling noise for all `n >= 2`
  (`G_n/w_n` halves exactly each rank);
* deepest fatal rank 16, matching `N·P(n) ~ 1`.

So the failure process is **exactly Bernoulli with summable rate**. Failures are
front-loaded; the deepest observed failure grows only like `log2(#targets)`.

## 3. No local mechanism exists [COMPUTED — the one-way result]

Normalise the skip position `v_n = rho_{n-1}/w_n in [0,1)`; fatal iff `v_n > 1 - G_n/w_n`.
Pooled over ~2.9·10^5 skips at rank >= 40:

| `q` range | `P(v > 1-eps)/eps` at eps = 2^-2 … 2^-12 |
|---|---|
| 3..200 | 0.94 → 0.79 (biased **away** from danger) |
| 1e5..2e5 | 1.00 → 1.16 (flat) |
| 1e12..2e12 | 1.00 → 1.01 (flat) |

The apparent repulsion is a **small-denominator transient only**. For large `q` the
skip position is equidistributed to measured precision `2^-12`, and the failure rate
equals the geometric gap width exactly.

**Consequence.** There is no congruence, height, phase, density, ownership, window,
or carry signal distinguishing safe from fatal orbits, because there is no signal.
This is a structural explanation for why all ~25 mechanism families in this corpus
died: each was searching for a bias that the measurement says is absent. It also
rules out proving 257 *true* by any such mechanism, since ~50% of rationals survive.

Closest-call margins for the flagship targets (depth 10,000, `scripts/beta_gap_margin.py`):
1/21, 1/465, 4/9, 1/2, 1/5 all have their minimum margin at rank 5–8, at exactly the
random-model value, and margins thereafter grow like `2^n` gap-widths. The danger is
entirely front-loaded; depth audits past rank ~20 test nothing.

## 4. What this does and does not claim

* **Does not** prove 257 false. Survival to depth `R` is not survival.
* **[HEURISTIC]** Under the measured Bernoulli law a target alive at depth `R`
  survives forever with probability `1 - O(2^-R)`. Counterexamples are therefore
  abundant (about half of all rationals), not rare.
* The binding difficulty is **certification, not discovery**: proving one orbit avoids
  gaps forever is Diophantine avoidance where the residual denominator is `~2^{n^2/4}`
  against a window of relative width `2^-n`. No height argument can ever close that,
  which is the same wall in cleaner coordinates.
* **[PROVED, elsewhere]** An eventually periodic support gives a Lambert series over
  arithmetic progressions; those values are known transcendental. So a certified
  counterexample must have aperiodic support — consistent with the observed
  density-1/2 pseudorandom supports.
