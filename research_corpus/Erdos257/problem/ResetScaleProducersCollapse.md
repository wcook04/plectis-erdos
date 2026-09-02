# Reset Scale Producers: Exact Collapse of `SeamResetSqrtEscape`

**Date:** 2026-08-23
**Lane:** Erdős #257 — half-membership via reset square-root escape
**Module:** `Erdos257PeriodNoncollapse.HalfResetSqrtEscapeScaleProducers.lean`
**Status:** reduction LANDED — `lean_fast_build.py` exit 0 after 3345 jobs; all six printed theorem audits use only `propext, Classical.choice, Quot.sound` (no `sorryAx`). The build also validates the one-line repair of the previously broken HEAD dependency `HalfUpperResetCriticalBand.lean`. The two producers themselves remain open.

## 1. What collapsed

The surviving all-depth obligation for the negative answer to Erdős #257 was

```
SeamResetSqrtEscape :  ∀ r ≥ 10, upper-or-middle reset at r → 2^(r+5) < dev_r²,
dev_r := R_(r+1) − 2^(r+1).
```

This module proves that this single diffuse anti-concentration statement is
**exactly equivalent (given already-landed identities) to two independent,
monotone, branch-local lower bounds**:

| Branch | Identity used | dev_r | Producer |
|---|---|---|---|
| middle | `seamMiddleBranch_nextRemainder_add_belowPulse_eq` + pulse bound `≤ 2(r−2)` | `4·R_r − belowPulse_r` | `4·R_r ≥ 3·2^⌊(r+5)/2⌋ + 2(r−2)` |
| upper | `seamUpperBranch_remainder_add_resetCharge_eq` | `−(4·overshoot_r + abovePulse_r)` | `E_r := 4·overshoot_r + abovePulse_r ≥ 3·2^⌊(r+5)/2⌋` |

The uniform threshold `3·2^⌊(r+5)/2⌋` absorbs both parities of `r+5`
(`2⌊(r+5)/2⌋ ≥ r+4`, so `(3·2^k)² = 9·4^k ≥ 9·2^(r+4) > 2^(r+5)`).

Consequences landed in Lean:

* `middleResetDeviation_eq`, `upperResetDeviation_eq` — exact signed
  deviation identities per branch;
* `seamResetSqrtEscape_middle_of_scale`, `seamResetSqrtEscape_upper_of_scale`;
* `seamResetSqrtEscape_of_scaleProducers` and
  `half_mem_mersenneAchievementSet_of_scaleProducers` — the two named
  producers (`SeamMiddleResetRemainderScaleProducer`,
  `SeamUpperResetChargeScaleProducer`) jointly give `1/2 ∈`
  achievement set;
* boundary forms `seamUpperReset_landingScale_iff_chargeScale`,
  `seamMiddleReset_landingScale_iff_remainderScale` restating each producer
  on the post-reset landing remainder — the quantity the nested backward
  pullback identities control directly.

The return-time detour is thereby removed as a *necessary* intermediate:
the open obligation is now literally "remainders/charges at reset rows stay
above √-scale", with no run-length quantifier anywhere.

## 2. Computation that selected the shape

Probe scripts (this wave):

* `/tmp/erdos257-return-band/reset_deviation_census.py` (rows 3–1600):
  764 resets, exactly 382 upper / 382 middle.
  * Gap law `s − floor(log₂|dev_s|)` histogram from row 14:
    `369, 187, 98, 50, 25, 14, 7, 5, 3, 0, 1, 0, 1` for gaps `0…12` —
    geometric with ratio ≈ 1/2, i.e. the invariant measure of the doubling
    map on the normalized coordinate `y_s = X_s/2^s`.  No arithmetic
    clustering near zero deviation.
  * Worst middle producer margin from row 14: **row 14**, slack **8**
    (`4R − pulse = 1565` vs required `1557`).  Worst upper margin from
    row 14: row 19, slack ~486k over threshold `12288`.
  * So both producers hold through row 1600, but the middle producer is
    *numerically tight* only in rows 14–20; after that slack grows like
    `2^(s/2−O(1))`.

* `/tmp/erdos257-return-band/producer_margin.py` (rows 10–6000): exact
  sweep of both producer inequalities; result bound to receipt.

Earlier audit context consumed: `audit_forced_seam_words(2000)`
(`half_midpoint_tail_bridge_lab.py`) — pullback strict-growth failures kill
naive monotone descent (8 counterexamples), while pullback coordinates
themselves are ~`2^a` scale, so *size*, not monotonicity, carries the
descent.

## 3. The descent target this opens (next wave)

Suppose the middle producer fails at `s`: then `R_s < √-scale`.  Row `s`
is a middle reset, so the preceding block is an upper/middle reset `r < s`
followed by `L = s − r − 1` right branches.  The landed nested identity

```
R_s + nested_charge = 4^(L+B) · pullback_coordinate(r-block)
```

with `nested_charge ≥ 0` forces the corresponding scaled quantity at the
*earlier* reset to be `< √-scale / 4^(L+B)` — strictly smaller in absolute
terms.  Iterating gives an infinite strictly decreasing sequence of
nonnegative integers indexed by descending reset rows, impossible once the
finite base band (rows 10–13, plus every reset whose ancestor chain exits
below row 14) is certified exactly.  The same argument through
`seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap` handles
upper resets via the landing boundary form.

Claim ceiling: this descent is a plan, not a proof; the strict-growth
counterexamples above show the naive monotone variant is false and the
correct decreasing quantity must be the scaled landing deficit, not the raw
pullback coordinate.

## 4. Receipts

* Lean module: `formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/HalfResetSqrtEscapeScaleProducers.lean`
* Validation: `lean_fast_build.py --jobs 2 Erdos257PeriodNoncollapse.HalfResetSqrtEscapeScaleProducers` — exit 0, 3345 jobs; deferred twice under lease tickets `rct_7b5bda46a2c92d249cd0`, `rct_625c4847d9ddafe39e66` before admission.
* Census: `/tmp/erdos257-return-band/census_1600.json`; durable scripts
  `formal_math/erdos257_period_noncollapse/scripts/reset_deviation_census.py`
  and `formal_math/erdos257_period_noncollapse/scripts/scale_producer_margin_sweep.py`
  (margin sweep receipt: `state/formal_math/erdos257_period_noncollapse/reset_scale_producer_collapse_receipt.json`).

## 5. Second wave: middle-producer discharge into three margins (landed)

`HalfResetSqrtEscapeMiddleDischarge.lean` (build exit 0, 3346 jobs, all
audits `propext/Classical.choice/Quot.sound`) eliminates the middle
producer as an independent obligation.  Splitting on the branch entering
a middle reset:

* right predecessor ⟹ `R_s = 4·R_(s−1) − 2^s − p_(s−1) − 4` exactly: the
  post-right remainder IS the take-decision margin (`SeamTakeMarginScaleProducer`);
* middle predecessor ⟹ `R_s ≥ 2^s − 2(s−2)` unconditionally (free);
* upper predecessor ⟹ `R_s = 2^s − E_(s−1)` exactly: needs a charge
  CEILING (`SeamUpperResetChargeCeilingProducer`).

`SeamResetSqrtEscape` therefore follows from three uniformly-shaped
margin statements — floor `E ≥ 3·2^⌊(d+5)/2⌋`, ceiling
`4E + 3·2^⌊(d+6)/2⌋ + 2(d−1) ≤ 2^(d+3)`, take-margin
`2^(t+1) + p + 4 + 3·2^⌊(t+6)/2⌋ + 2(t−1) ≤ 4R_t` — every decision of
the seam greedy clears half-row scale.

**Design error caught by Lean:** the first draft claimed a right
predecessor alone forces `R_s ≥ 2^s`; omega's counterexample exposed the
sign slip (the take threshold is the LOWER half-boundary `4X ≥ p+4−2^s`,
not `+2^s`), and the exact identity above replaced it.

**Three-margin sweep** (`scale_producer_margin_sweep.py`, rows 10–1600):
zero failures; worst slacks — floor 14456 (row 13), ceiling **8 (row
13)**, take-margin 1699 (row 10).  The binding constraint is the ceiling
at row 13, which feeds the historically-tight row-14 middle reset.

Remaining open: prove the three margin producers all-depth (descent via
nested pullback identities against the finite base band) or any one of
them directly.

## 6. Frontier map: what a descent proof can and cannot use (do-not-rederive)

Read this before attacking the three margin producers.

* **What descends.** SMALL(u) (`R_u < Θ_u`, Θ_u ≈ half-row scale) propagates
  BACKWARD only through non-right predecessors: middle-prev is free
  (`R_s ≥ 2^s − 2(s−2)` landed); upper-prev converts SMALL into
  ceiling-failure at `s−1` (same fact restated). Both give strict row decrease.
* **What does not descend.** Right-predecessors CREATE fresh smallness from
  large remainders: `R_s = 4R_(s−1) − 2^s − p − 4` is the take slack, and a
  borderline take from `R_(s−1) ≈ 2^{s−1}` leaves `R_s` arbitrarily small
  while `R_(s−1)` was exponentially large. Any proof scheme whose induction
  hypothesis is a size bound on `R` alone dies here. This kills naive
  infinite-descent AND forward-dilution arguments symmetrically (smallness
  dilutes ×4 per reset going forward, so forward persistence also terminates
  without contradiction).
* **Where the leverage must come from.** A borderline take is not just small
  slack `D`; it pins the suffix packet congruence `4^L | R_end + P_L` for the
  whole following run, and the packet `P_L` is a base-four register of the
  actual pulses. The open question in one sentence: *can the pulse register
  of a genuine greedy run ever sit within sub-half-row distance of a
  multiple of `4^L` from below?* Size arguments cannot answer this;
  congruence + the divisor-incidence structure of pulses must.
* **Existing tools that plug in.** `modPacket_eq_zero_or_topWindow_of_small`
  (top-window residue dichotomy), the nested pullback identities
  (`backwardCriticalDistance_eq_fourPow_mul_pullback`), the card-bound
  certificate `E >= card + 2` (linear, too weak alone), and the late-reset
  exponential barriers (handle the late-largest-false region completely).
* **Binding numeric case.** Row-13 ceiling, slack 8 (feeds the historically
  tight row-14 middle reset). Rows 10-16 are the entire finite base band a
  hybrid theorem would need; everything downstream has exponential slack.

## 7. Final consolidation: two producers, not three

Ceiling at d is equivalent to `R_(d+1) >= (3*2^((d+6)/2) + 2(d-1))/4`
(quarter-threshold form); take-margin at t is `R_(t+1) >= thr(t)`. Both
are remainder lower bounds at landing rows. Candidate master statement:
`R_u >= 3*2^((u+5)/2) + 2*(u-3)` for `u >= 11`. Sweep rows 11-1600:
exactly ONE violation - row 14 (`R_14 = 392` vs 1558 needed; ratio -1
bit), which is the already-finite-base cell feeding the row-13 ceiling
(slack 8). Everywhere else the margin grows without bound (ratio_bits
>= -1 worst, rising linearly).

So the open core is TWO producers:
1. `SeamRemainderSqrtScale`: quarter-threshold remainder bound at every
   landing row `u >= 11` (covers ceiling; row 14 sits inside the finite
   base band);
2. `SeamUpperResetChargeFloor` (floor, unchanged).
Plus the take-margin producer, which empirically has exponential slack
beyond row 20 and only binds inside the base band.

Attack order for a future session: (i) prove the quarter-threshold
universal via the pulse-register congruence route at borderline takes;
(ii) floor via overshoot granularity at the adjacent cut; (iii) keep the
base band finite-verified. Do NOT re-attempt size descent (see §6).

## 8. Cross-index: Proposition C closes denominator routes here too

From the coupled-factor lane (TwentyOnePrimorialRepair, 2026-08-23):
Proposition C — for d ∈ Aₙ with 2d > n > 6, Φ_d(2) divides exactly one
summand of Σ 1/(2^d'−1) and survives into den(rₙ); measured cancellation
loss < 36 bits against ~400k-bit denominators (exponent 0.17–0.18·n²).

Consequence for THIS lane: proving `R_u >= sqrt-scale` via
`|δ_u| >= 1/den` would yield only `|δ| >= 2^(-0.17u²)` — exponentially
too weak against the needed `2^(-3u/2)`. Denominator separation is
therefore a closed route for the three margin producers as well. The
margin content must be extracted from the greedy decision structure
itself (take-margin identity, pulse register congruences), consistent
with §6 and §7. Coordinate change away from raw remainders — the other
lane's conclusion — applies to any consumer that still estimates in rₙ.

## 9. Base band is Lean-native

`HalfResetBaseBandCertificate.lean`: exact remainders R_9..R_17 computed
inside Lean (`native_decide`; values match Python byte-for-byte, e.g.
R_13 = 15147, R_14 = 392), plus consumption-ready base instances:
ceiling producer at d = 10..15 (tightest: d = 13, slack 8) and floor
producer at d = 13. A future descent lemma quantifies away from these;
the finite half of any hybrid theorem is now proof-checked, not just
audited in Python.
