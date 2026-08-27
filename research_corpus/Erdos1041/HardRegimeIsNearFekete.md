# Erdős 1041: the hard regime is the near-Fekete regime

Status: exact measurement on stored witnesses plus an elementary consequence of
two facts already in this directory. Current through 2026-08-27 source audit.
This note proves nothing about Erdős #1041. It is a statement about **where the
hard configurations live**, and therefore about where to search and how a proof
may split.

## The elementary observation

Two facts already recorded in [CriticalBudgetLab.md](CriticalBudgetLab.md):

* the resultant identity, over the `n−1` critical points with multiplicity,

  ```text
  prod_k |f(c_k)|  =  prod_(i<j) |z_i − z_j|^2 / n^n
  ```

* Fekete: the Vandermonde product over the closed unit disk is at most `n^(n/2)`,
  with equality exactly at the `n`-th roots of unity.

Write `T* = min_k |f(c_k)|` and `D = prod_(i<j)|z_i − z_j|^2 / n^n`, so `D ≤ 1`.
Since `T*` is the minimum of the `n−1` critical values,

```text
T*^(n−1)  <=  prod_k |f(c_k)|  =  D  <=  1,
```

hence

```text
T*  <=  D^(1/(n−1)).
```

So **`T*` near one forces `D` near one, and `D` near one forces the roots near a
rotated regular `n`-gon on the unit circle.** The equality case is classical and
this file claims nothing new about it; what is worth recording is the direction
of the implication and how sharply it bites on the actual hard instances.

## The measurement

The corpus stores two hard witnesses — the degree-6 and degree-9 configurations
of [StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md) §3, where
no admissible hub carries two contained straight spokes — as exact IEEE-754
hexadecimal literals, because their margins are near `1e-5`.

| configuration | `D` = disc / `n^n` | max deviation from regular gon | modulus range |
|---|---|---|---|
| degree-6 witness | `0.999992181741` | `0.000518655` | `0.999999850` (all equal) |
| degree-9 witness | `0.999947120693` | `0.000115445` | `0.999994638 … 0.999999850` |
| exact regular 6-gon, `r = 0.99999985` | `0.999995500010` | `0` | — |
| exact regular 9-gon, `r = 0.99999985` | `0.999989200058` | `0` | — |
| generic random, degree 6 | `0.000005888113` | `0.790255264` | `0.474 … 0.946` |
| generic random, degree 9 | `~1e-13` | `1.114931860` | `0.464 … 0.997` |

Every angular gap of both witnesses is within `0.1%` of `2π/n`. The degree-6
witness has all six moduli **identical** to the last stored digit.

The separation between the hard witnesses and generic configurations is twelve
orders of magnitude in `D`. The hard witnesses are not merely unusual; they are
perturbations of the regular `n`-gon at radius `1 − 1.5e-7` with relative
perturbation about `5e-4`.

Receipt: [`scripts/check_erdos1041_hard_regime_is_near_fekete.py`](scripts/check_erdos1041_hard_regime_is_near_fekete.py),
which fails if a stored witness stops registering as near-Fekete or a generic
control starts to.

## Correction to this note, same day: the search explanation below was wrong

The section that follows originally claimed that the recorded searches never
entered the near-Fekete shell, and offered that as the explanation for six
pinned suprema. **That claim is false and is retracted**; two sibling files
already had a better answer.

* [InverseRayAggregateComputationalLab.md](InverseRayAggregateComputationalLab.md)
  states that its deterministic probe already contains "perturbations of
  boundary-near regular polygons in degrees 3 through 9 and four perturbation
  scales". The near-Fekete coordinates have been searched.
* [StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md) records the
  actual mechanism, and it is sharper than a coordinate story: **the extremum is
  a cusp.** At `z^n − r^n` the critical point has multiplicity `n−1`; splitting
  it drops the ratio by a *fractional* power of the perturbation. At degree five,
  perturbation `1e-9` gives `0.99648`, `1e-6` gives `0.98012`, `1e-3` gives
  `0.88553`. So a search at any fixed perturbation scale genuinely sits below the
  supremum, and does so by an amount that shrinks only like a fractional power.
  The pinned values are not a failure to reach the shell; they are the correct
  values of the objective at the scales sampled.
* The same file records that the integrator itself under-reports at a degenerate
  hub — on `z^n − r^n` the substitution `f(z(u)) = (1−u²)f(c)` returns `1.7989`
  against the true `2r = 1.8` at degree six, with a deficit that does not shrink
  with the start offset — and draws the right conclusion: **equality families
  must be asserted from their ordinary proofs, not from the integrator.**

Two consequences for the rest of this note. The retained measurement (that the
stored hard witnesses sit at discriminant ratio `0.99999` with deviation `5e-4`
from a regular gon) stands, and so does the correction to the "tight at `n = 3`
and only there" paragraph, which is an ordinary-proof statement about the
extremal family and does not depend on any search. But the "consequence for a
proof" below is weaker than it reads: the `D`-near-1 side is a **cusp**, not a
smooth maximum, and `StraightSpokeHubCriterionLab.md` states in terms that a
second-order variational argument at the extremum "will not see the right
behaviour". Any perturbative attack there must handle a fractional-power
response, which is a materially harder object than a Hessian.

## Why the suprema pin (superseded explanation, retained for the record)

[CriticalBudgetLab.md](CriticalBudgetLab.md) records six occasions on which a
hub statement was supported by adversarial maximisation of its own objective,
came back with a supremum pinned just below its threshold, and was later false.
The suprema were `1.999999688 … 1.928588184` against 2, and `0.986769` against 1.

The reason is now concrete rather than methodological. The hard set is an
exponentially thin neighbourhood of a measure-zero configuration. A search that
parametrises by root positions in the bulk, started from uniform or clustered
samples, has essentially no chance of entering a `1e-7`-thin shell around a
particular rotated regular polygon. It converges to the best configuration in
its own basin and reports a pin. That is exactly what happened, six times, and
it is why the witnesses had to be stored rather than rediscovered.

**A pinned supremum is evidence of one basin, not evidence for the claim** —
with one exception worth stating, because it rescues the main conjecture. A pin
is not suspicious when a *known extremal family explains it*. The
`max min_c L(c) = 1.999999986` pin at `n = 3` is explained: the extremal cubic
`z^3 − r^3` gives exactly `2r → 2`. The `0.986769` pin on the spoke claim was
explained by nothing, and the claim was false.

## Consequence for search

Parametrise near-Fekete rather than in the bulk:

```text
z_k = r (1 + a_k) exp( i (2 pi k / n + t_k) ),    r = 1 − eps,
```

and search over `eps` on a log grid together with small `a_k, t_k`. At
`eps ~ 1e-7` the quantities of interest have margins `~1e-5`, so double
precision carries only about nine significant digits of headroom; the
measurements above are float but any *violation* found in these coordinates
must be re-verified at high precision before it is believed. This directory has
four recorded false counterexamples that were all branch-mistracking artifacts.

## Consequence for a proof

An argument is free to split on `D`, and the two sides are genuinely different
problems rather than two halves of the same difficulty:

* **`D` bounded away from 1.** Then `T* ≤ D^(1/(n−1))` is bounded away from 1,
  so the two cells of `{|f| < T*}` that merge at `c*` do so strictly below level
  one, and the merged component has room between level `T*` and level 1. Nothing
  here converts that room into a length bound yet.
* **`D` near 1.** Then the roots are a small perturbation of a rotated regular
  `n`-gon on a circle of radius `r`, i.e. `f` is a perturbation of `z^n − r^n`,
  whose critical point is `0`, whose admissible descent branches are the `n`
  radial spokes, and whose two-arm length is exactly `2r < 2`. This is the
  extremal family for the constant 2, and it is understood exactly.

Neither half is proved here. What the measurement supplies is the assurance that
the second case is not a degenerate corner to be waved away — it is where the
actual difficulty lives — and that a stability estimate for the Fekete maximiser
is the object that would join the two halves. No such estimate is claimed, cited,
or known to this file, and locating one is the obvious next step.

## Correction: MIN and AVG are tight at every degree, not only at `n = 3`

[CriticalBudgetLab.md](CriticalBudgetLab.md) records, under "Maximising MIN and
AVG directly":

| n | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|
| max of `min_c L_c` (MIN) | `1.999999986` | `1.852321` | `1.634226` | `1.592300` | — |
| max normalized aggregate (AVG) | `0.999999994` | `0.904177` | `0.822727` | `0.746591` | `0.680409` |

and concludes that both are "tight at `n = 3` and only there", with "both
ceilings falling monotonically with degree afterwards". **That conclusion is
false, and the counterexample is this problem's own extremal family.**

The argument is analytic, not a measurement. Take `f = z^n − r^n`, `0 < r < 1`.
Its only critical point is `0`, with multiplicity `n−1`, and `|f(0)| = r^n < 1`,
so it is admissible. Since `arg f(0) = π`, the descent set `{arg f = π,
|f| decreasing}` solves `z^n = r^n − ρ` for `ρ` running from `r^n` down to `0`,
which is exactly the `n` radial segments `[0, r ω^k]`, each of length `r`.
Resolving the multiplicity into `n−1` edges of two radial arms each:

```text
min_c L(c)            = 2r
aggregate             = 2r(n−1) = 2Rm,   so normalized aggregate = 1 exactly
```

for **every** `n ≥ 2`. Letting `r → 1⁻` gives `sup min_c L(c) = 2` and
`sup AVG = 1` at every degree. The recorded values `1.852321`, `1.634226`,
`1.592300` and `0.904177 … 0.680409` are therefore basin artifacts of a bulk
search, not ceilings.

Numerical confirmation through the corpus's own machinery
(`formal_math/probes/erdos1041_critical_budget.py`), perturbing the extremal
family by `1e-9` at `r = 0.999` so the degenerate critical point splits into
`n−1` simple ones, gives minimum two-root budgets over admissible hubs of
`1.998000` at `n = 4`, `1.996981` at `n = 5`, `1.998001` at `n = 6` — that is
`2r` to five figures, and above every recorded MIN value. Arc length dominates
the chord budget, so `min_c L(c)` is at least these.

One mechanical contributor is worth recording. `descend_branches` returns `None`
when `|f''(c)| < 1e-11·max(1,|f(c)|)`, calling the hub degenerate; for
`z^n − r^n` the critical point has multiplicity `n−1`, so `f''(0) = 0`. Measured
against the exact family this skips **all** admissible hubs at `n = 5, 6, 7`
(4/4, 5/5, 6/6) while skipping none at `n = 3, 4`, and skips none at any
perturbation scale tested. So the blind spot is real but narrow and is **not**
the explanation.

The explanation is the cusp, already recorded in
[StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md): splitting
the multiplicity-`n−1` hub drops the ratio by a fractional power of the
perturbation, so a search at any fixed scale returns a value genuinely below the
supremum. That file's degree-five figures — `1e-9 → 0.99648`, `1e-6 → 0.98012`,
`1e-3 → 0.88553` — are the same phenomenon as the measurements above, and the
`1.998` figures here at scale `1e-9` are consistent with them rather than in
tension. The same file also warns that the integrator under-reports at the
degenerate hub (`1.7989` against the true `2r = 1.8` at degree six), which is why
the statement in this section is derived from the ordinary proof and only
*checked* numerically.

So what is corrected here is a single paragraph of `CriticalBudgetLab.md` that
read the search maxima as ceilings. It is not a discovery that the searches were
run in the wrong place.

**Consequence for a proof.** No degree-dependent slack exists. Any argument must
be tight at every degree, and the extremal configuration is the same one at every
degree. An approach whose constant degrades with `n` cannot work, and an approach
calibrated on the recorded ceilings would be calibrated against artifacts.

## Claim boundary

**Primary-source boundary (read 2026-08-27).** The Fekete/Vandermonde statement
used at the start is recorded in the downloaded arXiv TeX source for Calegari,
Dimitrov, and Tang, arXiv:2408.15403, *The linear independence of 1, zeta(2),
and L(2, chi_-3)*: `extracted.md` lines 1615--1623, Lemma 1 (Fekete). The
archived source bundle is
[`source.tar.gz`](../../../../annexes/arxiv-2408-15403-calegari-dimitrov-tang-linear-independence/source.tar.gz),
SHA-256
`00dd2b1078a2e6c166562e29c18f98dabb27d0c711225c455e7afae913ddce11`; the
official record is [arXiv:2408.15403](https://arxiv.org/abs/2408.15403).
That lemma states the unit-torus Vandermonde supremum and regular-polygon
equality case used here. It is a modern primary text stating the classical
lemma, not evidence that the local observation is new or that this paper is the
original source. No priority or novelty claim is made.

Exact: the inequality `T* ≤ D^(1/(n−1))`, which is immediate from the resultant
identity and `T*` being the minimum critical value. The tabulated measurements,
which are float and reproducible from the receipt.

Not established: any stability theorem for the Fekete maximiser, quantitative or
otherwise; any length bound in either regime; any claim that the two-case split
closes. Erdős #1041 remains open.
