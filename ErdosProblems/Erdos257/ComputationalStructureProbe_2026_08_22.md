# Computational structure probe — 2026-08-22

Four new exact instruments (all in `formal_math/erdos257_period_noncollapse/scripts/`,
all pure integer arithmetic, no floating-point decisions).  Everything below is
finite evidence; nothing here promotes a claim.

## Instruments

| Script | What it does | Validation |
|---|---|---|
| `deep_quotient_chain_audit.py` | Pure-integer replay of the exact `TwentyOneQuotientGreedy` state machine (pulse/target/core/coin) + Lambert defect, with log-window structure statistics. | Reproduces the certified 200000-rank receipt exactly: 96 defect-zero returns (last 193690), 4956 Q<=1 returns (last 199930, max gap 492), max defect 40 at 180179, six-step failures 61141 (first 73), slope-danger 1275 (last 5459, zero repair failures), min closed margin 1 at rank 6. |
| `half_orbit_structure_probe.py` | Exact residual replay toward 1/2 with wall coordinate sigma_n = 2^n(T_n - r_n), skip/double-skip gap laws. | Matches known greedy prefix (takes {2,3,6,7,14,20,21} through 21). |
| `rational_target_census.py` / `late_kill_hunter.py` | Census of greedy outcomes for rational targets; kill-rank distribution. | 1/3, 1/7, 1/15 detected as weight-ties (finite supports) as expected. |
| `theta_phase_prober.py` | Exact Theta_L(M) short-window divisor phase statistics. | Reproduces the reasoning-surface Swing-2 table digit-for-digit (0.035415, 0.009290, 0.002455, 0.000625, 0.000185; median 0.244709 vs recorded 0.24471). |

## Findings

### 1. Kill landscape is exactly the superincreasing measure count

Over 100000 random reduced odd targets (b <= 10^6, depth 400): kill ranks
decay geometrically with ratio exactly 1/2 (24942@1, 12556@2, 6146@3, ...),
**max kill rank 23**, zero kills after rank 50.  Mechanism identified: the
rank-n fatal gaps are disjoint cylinders of total measure
2^n * mersenneGap(n) ~= 2^-n.  Late fatality is a measure-2^-n event; the
1/21 fatal branch requires one at its last skip M — an event of relative
scarcity 2^-M inside the pinned orbit.

### 2. Both candidate orbits are Haar-generic in every measured statistic

Through 300000 ranks (21-chain) and 50000+ (half-chain):

* k-block census: zero missing blocks for k <= 14, missing counts at k=15..18
  match the log2(depth) null; no forbidden word.
* Lag autocorrelation 1..64: all |rho| < 0.006; no lag structure.
* Conditional take-density by rank mod 3 / mod 6: flat within 0.3%.
* Pair conditionals P(next|pair): 0.2497-0.2509 — independent to 4 decimals.
* Take density drift: 0.500 +/- 0.004 per window — no alignment drift.
* Margin minima decay like c/N (generic shrinking-target law): half-orbit
  sigma_min 3.9e-5 at N=5e4; 21-chain lambda_min 8.07e-7 at N~1.3e5 — the
  latter ~5-10x closer to the boundary than the 1/N null (watch: the 5M run
  decides whether this is trend or fluctuation).
* Run maxima: 20 ones / 17 zeros at 3e5 vs log2 null ~18 — within fluctuation.
* Double-skips (1/2 orbit): dense (25% of ranks), max gap 38 through 5e4,
  growth ~log — versus the c6b producer requirement t <= c-3-log2(c-2)
  (linear).  Empirical slack factor > 1000 and growing.

### 3. The naive periodic-shadow reduction is false, and the failure localizes the wall

Hypothesis tested: since r_N is rational with odd denominator q_N, the
mod-1 shadow of the scaled orbit is a periodic doubling orbit; decisions
outside ambiguity windows should be shadow-determined.  **Falsified at
anchor 300**: mismatches at full boundary distance from k=0.  Cause
identified: 2^n T_n approaches 1 from ABOVE (sum of 2^{-i}/(1-2^{-(n+i)})),
so survival legally permits y_n in [1, 2^n T_n); the mod-1 shadow loses the
integer part that carries exactly the wall.  Corrected layer model: the
orbit lives on [0, 1 + Theta(2^-n)); the entire open problem is the
orbit's behaviour inside an exponentially thin band of width Theta(2^-n)
around y = 1 plus the moving ceiling.

### 4. Theta near-hits clump into doubling cascades (new structural fact)

The prober reproduces the recorded Theta_40 table exactly, and adds: near-
integer hits occur in **consecutive-M chains** (M=1031034..37, 1077621..23,
1168664..66), because Theta(M+1) = 2 Theta(M) - c + 2^-L c' propagates a
hit at distance d into a hit at {2d}.  Near-hits are not Poisson; any
second-moment or clumping heuristic for Route R1 must use the cascade law
(Borel-Cantelli summability is unaffected).

### 5. Massive-artifact side outputs

* Certified-script frontier extension to 400000 ranks (running).
* Deep 21-chain to 5,000,000 ranks (running).
* Half-orbit to 2,000,000 ranks (running).
* ~4x10^7 stabilized binary digits of C = E - 3/2 via K(M+1)=2K(M)-(tau(M+1)-1)
  (running) — a digit artifact one order of magnitude beyond the published
  '11'-infinitude result for E (Campbell 2026).

## What this changes

The wall statement survives everything: all-depth statements are untouched
by finite genericity.  What changes is the *shape of the missing proof*:
every measured statistic says the pinned orbits behave like Haar-generic
points of the perturbed doubling map, whose generic behaviour gives cofinal
skips and membership.  A proof therefore only needs one global input of
the type "the orbit of this computable point is generic enough at the
exponentially thin boundary layer" — and the computations now quantify
exactly how much slack any such input must supply (factor 10^3+ on gap
laws, factor 2^-M scarcity on the fatal event, 1/N boundary-approach law).

## Deep-run addendum (5,000,000 ranks exact; certified receipt to 400,000)

Certified (`check_twenty_one_greedy.py --ranks 400000 --correction-depth 1000`,
exact intervals): all invariants hold; 141 defect-zero returns (last 381010),
max defect 51 at 360359, strict closed state at every audited even depth,
terminal defect zero everywhere.

Deep pure-integer chain to 5,000,000 ranks:

1. **Slope-danger dormancy.** Still exactly 1275 slope-danger ranks, last
   at 5459: zero new danger ranks in the following ~4.6 million ranks, zero
   repair failures ever.  The repair-load frontier looks finite.
2. **Square-root gap law (new empirical law).** Max gap between successive
   Q<=1 returns by decade of starting rank: 1, 5, 34, 88, 324, 999, 1650
   at 10, 10^2, ..., 10^6, 5x10^6.  From 10^3 onward G(N) ~= sqrt(N) to
   three digits (999 vs sqrt(10^6)=1000; 324 vs 316).  Full-sequence check
   at 10^6: max over all gaps of gap/sqrt(start) = 1.41, attained at
   N=1940; thereafter ratios sit in 0.70-0.90.  Empirical statement: every
   interval [N, N+1.5 sqrt(N)] contains a small-defect return.  If proved
   at any constant, cofinality of Q<=1 follows and hence 1/21 membership
   via `one_div_twenty_one_mem_mersenneAchievementSet_of_defect_le_one_cofinally`.
   This is the same square-root scale as `binaryCoeffTail_supportCoeff_le_
   two_sqrt_add_four` and `twentyOneGreedyDefect_lt_two_sqrt_add_six_of_
   skip` — a third independent appearance of one sqrt-N phenomenon.
3. **Apparent avoidance band near saturation.** The per-window minimum of
   the closed-margin mantissa lambda stops decaying near 1e-6..3e-6 from
   window 131064 through 5000000 (null predicts ~2e-7 at 5M).  Five
   consecutive windows sit above null.  Candidate structure: the orbit
   avoids saturation by a relative margin ~1e-6 more often than generic;
   unconfirmed (could be heavy-tail fluctuation).
4. Take density stays 0.49997; run maxima stay <= 20 (log2 null 22.3).

Overnight follow-ups launched: full gap sequence to 15,000,000 ranks;
half-orbit deep run continuing.

## Honest status

No claim changed status.  New measurable regularities (sqrt gap law,
danger dormancy, cascade clumping, boundary-layer localization) are
finite evidence and theorem-shaped targets; none is proved.
