# Erdős 1041: the model→real transfer LAW — obligation (b) fails at the MODEL's hub above `eta ~ 4.5e-3`, the REAL trace-max hub is uniformly coercive on the sampled near-gon core, and Theorem 2's stability constant is ~16x conservative

Date: 2026-08-30.  Origin: wave-1 opus transfer agent (263 quintic + 66
sextic + 71 large-`eta` samples; two instruments; 12-digit cross-checks
against four landed certificates), main-loop replay of both decisive
specimens.  Checker: `scripts/check_erdos1041_model_real_transfer_law.py`
(self-contained; replays specimen 1 and the degree-4 scoping witness
exactly).  This is a COMPUTATIONAL LAW note in the sense of
`TraceMaxRadialExcessLaw.md` — measured geography for FRONTIER §4.3
obligation (b), not a theorem, except where a row says "replayed exactly".

## 0. Objects and normalizations (pinned)

Real side: for monic `f` with roots `a_k` in the closed unit disk and a
critical hub `c`, the two arms are the Newton-flow descents
`f(z(t)) = f(c) e^{-t}` (`z' = -f/f'`), terminating at two roots
`z_i, z_j`; the REAL pair excess is

```text
E_real(c) = L(c) - (rho_i + rho_j),   rho = |root|,
```

`L(c)` the two-arm length.  Since `rho_i + rho_j <= 2`, any hub with
`E_real(c) <= 0` and `|f(c)| < 1` gives a parent connector of length
`<= 2` (containment automatic on descent arms).  The REAL trace-max hub
is `argmin_c |f(c)|` (equivalently max `Re(-log f(c))`).  Model side: the
sigma-blow-up `p_m = sum_k a_k^{-m}`, `sigma = (p_5/5)^{-1/5}` (branch by
critical-matching cost), `b_r = (p_r/r) sigma^r`,
`H(v) = v^5 + b_2 v^2 + b_1 v`; the model hub is `H`'s trace-max critical
point; `mu = b_2/v_c^3`; `E_model = |c*| mathcal E(mu, phi)`.  The Fekete
deficit is `eta := 1 - |disc f|/5^5`; the agent verified `eta = 1 - D`
EXACTLY against `NearFeketeRadialAngularSplit.md`'s `D` (deviation 0.0)
and the trace identity `sum_j -log|f(c_j)| = -log(1-eta)` to 12 digits.

## 1. The transfer law

Same-hub random families (215 samples, `eta in [3e-4, 3e-2]`):

```text
max |E_real - E_model| = 0.371 eta^0.348     (rms-log 0.076)
rms                     = 0.190 eta^0.381     (rms-log 0.087)
```

Chamber-targeted adversarial samples, hub-to-hub:
`max = 1.079 eta^0.185` (rms-log 0.008).  In the coercivity coordinate
the remainder is FLAT: `R = (E_real - E_model)/|c*|` has band maxima
`+0.093, +0.107, +0.122, +0.054, +0.070` at `eta = 3e-4 .. 3e-2` — no
`eta`-trend.  Signed relative remainder: global max `+0.0904`.  Model
margin scale: `|c*_real| = 0.667 eta^0.171`.  Radial perturbations
transfer almost exactly (median relative error `0.0011` at `eta = 3e-4`
vs `0.054` pure-angular) — consistent with Theorem 3a.  This is the
quantitative content of "the model decides first order only": both the
excess and its remainder are governed by `|c*| ~ eta^0.17`, so shrinking
`eta` improves the absolute budget (`eta^0.35` vs margin `eta^0.17`) but
NOT the relative one (fitted exponent `-0.11`).

## 2. Obligation (b) FAILS at the model-selected hub above `eta_0 ~ 4.5e-3` (sign anomaly, replayed exactly)

Located by lambda-scan per chamber region:

```text
eta_0 = 4.5417e-03   at the tangent orbit (mu = 50+30sqrt3, phi = -pi/2)
eta_0 = 2.1129e-02   at mu = -100
eta_0 = 2.3936e-02   at mu = -190
```

**Specimen 1** (in the checker, exact roots; all five unimodular to
`5.7e-13`; `eta = 9.9727654e-3`):

```text
a_1 = +0.999741221817 + 0.022748393333 i
a_2 = +0.343108181546 + 0.939295893612 i
a_3 = -0.829581249913 + 0.558386022205 i
a_4 = -0.813268406148 - 0.581888734692 i
a_5 = +0.294434207833 - 0.955671751836 i
```

Its blow-up sits EXACTLY at the tangent orbit (`mu_model = 101.961524 =
50+30sqrt3`, `phi = -pi/2`); at the model-selected hub the real excess is
POSITIVE, `E_real = +0.0024253` (main-loop instrument; agent
`+0.0024872815`), i.e. connector length `> rho_i + rho_j = 2`, while
`E_model = -0.01636`.  A second agent specimen at `eta = 3.00242347e-2`
gives `E_real = +0.0076788528` (agent-reported; roots not preserved), and
the model hub also goes positive at `eta = 3e-2` for `mu = -100`
(`+0.004933`) and `mu = -190` (`+0.001508`).

**This does not touch the parent**: the SAME quintics at the REAL
trace-max hub give `E_real = -0.459, -0.566, -0.594, -0.597` (specimen 1
replayed: `-0.459120`).  The failure is a HUB-SELECTION failure of the
naive transfer: model trace-max != real trace-max in 45/263 samples,
sharply keyed to `|mu|` — disagreement rate `1/106` at `|mu| < 1`,
rising monotonically to `20/20` at `|mu| >= 30`.  Mechanism: (CH) is
decided by `Re H(c) ~ |c|^5` while the dropped `m = 3, 4` modes
contribute `~ sqrt(eta) |c|^3`; at large `|mu|` the chamber hub is the
SMALL hub and the remainder dwarfs its level.  At the tangent orbit all
four model hubs tie at `Re H = 0` EXACTLY (replayed: tie `4.9e-13`), so
argmax hub selection there is pure noise — specimen selection must be by
`mu`-matching.  Any analytic obligation-(b) theorem must therefore
either (i) restrict to `eta <= eta_0(region)` with the model hub, or
(ii) key the connector to the REAL trace-max hub and prove the real-hub
law of §3 directly.

## 3. The real-hub coercivity law (measured), and its exact scope

At the REAL trace-max hub: `E_real <= 0` in **263/263** samples
(max `-3.64e-2`), with UNIFORM measured coercivity

```text
-E_real / |c*_real|  in  [1.117, 1.384]        (1st pct 1.186),
```

across all bands, and `E_real` only becomes more negative as `eta`
grows: max `-0.487` at `eta = 0.05`, `-1.146` at `eta = 0.7` (71-sample
large-`eta` probe).  The real object never visits the model's marginal
region (the chamber allows `|mathcal E|` down to `~0.06`–`0.17`; the
measured real bound is `~6.6x` better).  No `eta_1` upper limit was
found for the real-hub law on THIS sampling.

**Scope guard (replayed exactly; do NOT promote the law beyond it).**
The corpus's `MinimalHubArmBudgetRefutation.md` Result A witness at
degree 4 is a perturbed SQUARE at `eta = 0.01087` — inside the near-gon
band — whose argmin-hub excess is POSITIVE: the checker replays
`E_real^{(4)} = +0.003654` (`L = 2.0018366` chart, `R_MEC = 1.00091105`,
MEC-centred budget).  So "the real trace-max hub is safe" is FALSE as a
universal all-degree law even at small `eta`; the violating mechanism
(near-degenerate saddle pair + all-tie critical values + spectator-
determined enclosing geometry) is exactly the collapsed-saddle stratum,
and NEAR-GON CONFIGURATIONS ARE COLLAPSED-SADDLE CONFIGURATIONS (for
`z^n - lambda` all `n-1` critical points sit at `0`).  The degree-5
analogue of that witness is the single most important open falsification
target: A4's 263 samples and adversaries never visited the deg-5
tie/collapsed sub-stratum (the known deg-5 argmin violation sits far
away at `eta ~ 0.345`).  Until that probe runs, the real-hub law is a
measured quintic near-gon regularity with an explicit degree-4
counterexample pattern to rule out — not a conjecture to consume.

## 4. Stability sharpness (Theorem 2 is ~16x conservative)

Root-to-rotated-gon matching distance over all bands:

```text
d_max / sqrt(eta):  sup 0.447,  median 0.262,  min 0.0014   (n = 5)
                    sup 0.366,  median 0.199                (n = 6)
```

versus the landed `7 sqrt(eta)` of `NearFeketeRadialAngularSplit.md`
Theorem 2 — `15.7x`–`17.1x` conservative (`n=6`: `19x`–`21x`).  Free
fit `d_max = 0.225 eta^0.533`.  Sub-bounds: Thm 2(1) ratio max `0.238`
(bound 1); Thm 2(2) separation `1.06`–`1.16` vs bound `0.376`–`0.491`.
Amplitude dictionaries: `eta = 11.19 t^2` (n=5 angular), `27.34 t^2`
(n=6); `1 - rho_min = 0.0811 eta^0.979`.  Checker spot: specimen-1
`d_max = 0.361 sqrt(eta)`.  A reproof of Theorem 2 with constant `<= 1`
would widen every consumer's validity window by two orders of magnitude
in `eta`; the measured target is `~0.45`.

## 5. Secondary measured rows

- `n = 6` transfers BETTER: `max|d| = 0.451 eta^0.446`, 0/66 hub
  disagreements, coercivity `[1.377, 1.432]` (no chamber-targeted
  adversaries at `n = 6` — generic comparison only).
- Instrument note (FRONTIER §4.6 reproduced): the Newton-continuation
  instrument slipped to `4.2e-5` on exactly one sample with raygap
  `3.6e-6` (foreign critical value nearly on the value ray); DOP853
  unaffected; campaign-min raygap `9.0e-8`.
- Hygiene: cutoff `S = 20/40` deviation `7.8e-13`; Newton residual
  `2.1e-13`; second instrument median agreement `4.4e-12`; distinct-tract
  arms 263/263 and 66/66.

## 6. Consequences for the campaign

1. The (EX-U)/chamber program (and the wall reduction of
   `QuinticChamberWallReduction.md`) remains the `eta -> 0` decider; its
   real-scale consumption window at the model hub is now measured:
   `eta <= 4.5e-3` near the tangent region, `~2e-2` elsewhere.
2. For `eta` above that window the connector must be keyed to the REAL
   trace-max hub; the measured uniform coercivity `>= 1.117 |c*|` is the
   quantitative shape an analytic real-hub theorem should take, PENDING
   the degree-5 collapsed-saddle falsification probe of §3.
3. Theorem 2's constant is the cheapest analytic upgrade on the board
   (16x headroom measured).

## Claim boundary

Measured law throughout (grids, adversaries, two instruments), except:
specimen 1, the degree-4 scoping witness, the 4-fold tangent tie, the
trace identity, and the `eta` reconstruction, which the checker replays
exactly from printed exact inputs.  Nothing here proves obligation (b),
the real-hub law, (EX-U), degree five, or the parent.  The `eta_0`
values are empirical scan locations, not certified thresholds.  Specimen
2 (`eta = 3.00242347e-2`, `E_real = +0.0076788528`) is agent-reported;
its roots were not preserved — treat as replayable-by-method, not
replayed.
