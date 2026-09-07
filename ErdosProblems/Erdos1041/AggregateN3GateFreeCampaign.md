# Erdős 1041: the gate-free (AGG) campaign at n = 3, and the free-point FP_m experiments

Date: 2026-08-30 (overnight session).  Origin: main-loop computational campaign
following FRONTIER gap #2 ("decide (AGG) at n=3; two independent hunts stall at
0.999386, both on the instrument's `d_pt >= 0.02 R` gate") and FRONTIER gap #1's
free-point program.  Checker:
`scripts/check_erdos1041_aggregate_n3_gatefree.py`.

Everything here is COMPUTATIONAL (evidence classes labeled per section); the
parent problem remains open, and no claim below is a proof except the explicitly
marked exact identities.

## Part I — (AGG) at n = 3, gate-free

Recall the target row (`SeparatrixAggregateReduction.md`): with
`L(c)` the two-arm inverse-ray length and `R` the MEC radius,

```text
(AGG)   Sigma_c L(c)  <=  2 (n-1) R      [= 4 R at n = 3],
```

equality on the radial family `(z - tau)^3 - lambda` (both critical points
coincident at the centre, `L = 2r` each).  The prior hunts stalled at ratio
`0.999386` because the guarded instrument excluded the near-degenerate shell
`d_pt < 0.02 R` — exactly the shell the radial equality family lives in.

### Instruments (two-tier)

- **Tier 1 (screen):** the corpus's calibrated DOP853 lift instrument
  (`check_erdos1041_separatrix_aggregate.py`, validated this session: it
  reproduces every landed witness row), with the shell guard REMOVED and a
  step floor.  Cost ~0.5 s/config.
- **Tier 2 (exact-fibre adjudication):** a new mpmath instrument.  The branch
  `z(t)` with `f(z(t)) = v(1-t)`, `t in [0,1]`, is algebraic (Newton
  continuation with secant seeds and polyroots fallback); the arm length is
  `L = int_0^1 |v|/|f'(z(t))| dt`, computed piecewise (splits at foreign
  critical-value crossings) with exponent-adaptive substitutions:
  `t ~ u^2` at a regular hub, `t ~ u^3` when the hub is nearly degenerate
  (`|f''(c)/2| < 0.02 |v|^{1/3}` — the cube-root regime; the `u^2` integrand
  behaves like `u^{-1/3}` there), cubic substitutions at near-crossings.
  Per-piece Richardson until `1e-9` relative; dps 40-45.

Tier agreement: on generic, near-gon, and moderately near-radial
configurations the two instruments agree to all printed digits (examples in
the checker; e.g. generic torus triangle ratio `0.8334538556` both ways).

### Result 1 (computational law): the radial approach is strictly from below

On the near-radial family `f = z^3 - 1 + eps*(b2 z^2 + b1 z)`
(`|b2| = 1`, `|b1| = 0.7`, 10 phase pairs; roots recomputed exactly from the
coefficients), the maximal aggregate ratio over phases is

```text
eps      max ratio        gap 1 - ratio     C = gap/sqrt(eps)
1e-2     0.992560064      7.440e-3          0.0744
1e-3     0.997738656      2.261e-3          0.0715
1e-4     0.999292510      7.075e-4          0.0707
1e-5     0.999776989      2.230e-4          0.0706
1e-6     0.999929548      7.045e-5          0.0705
1e-7     0.999977728      2.227e-5          0.0705
1e-8     0.999992958      7.042e-6          0.0704
1e-9     0.999997774      2.226e-6          0.0704
1e-10    0.999999330      6.70e-7           0.067 (approaching noise floor)
```

**Law (AGG3-radial):** `4R - Sigma_c L(c) = (C(phase) + o(1)) sqrt(eps)` —
the aggregate deficit is POSITIVE and vanishes like the critical-point
split `sqrt(eps)`, NOT like the critical-value split `eps^{3/2}`.  On the
10-phase grid of the slice family the maximal-deficit coefficient is
`C = 0.0705(1)` across eight decades (`0.0744` at `eps = 1e-2` down to
`0.0704` at `1e-9`); other phase slices give their own stable constants
(the checker's 4-phase subset: `0.091`), so `C` is a positive
phase-dependent function, not a universal constant.  The stalled hunts at
`0.999386` were seeing the gate, not the mathematics: the true ratio inside
their shell is strictly below 1 all the way in.

### Result 2 (exact adjudication in the deep shell)

The exact-fibre instrument (dps 45) confirms positive gaps where float64 is
unreliable, including RANDOM two-parameter families (not only the slice):

```text
slice ph0  eps=1e-3:  gap +3.443e-3   (d_pt 3.1e-2, v_gap 5.4e-6)
slice ph3  eps=1e-3:  gap +1.003e-3   (v_gap 1.0e-8)
slice ph5  eps=1e-3:  gap +4.198e-3   (v_gap 1.0e-5)
rand0      eps=1e-3:  gap +3.177e-3   (d_pt 2.1e-2, v_gap 4.4e-6)
rand1      eps=1e-3:  gap +3.410e-3
   [deeper rows appended by the checker / rerun; see deepshell log]
```

### Result 3 (adversarial sweep, no violation)

3500+ configurations across five families (random torus, random interior,
near-gon pockets, near-radial log-grid `eps in [1e-12, 1e-1]`, clustered
pairs): no configuration with ratio > 1 outside the float noise floor
`~3e-6`.  Every apparent violation collapsed on inspection:

- **Fake-positive adjudication (instrument lesson, new instance).**  The best
  float "violations" (`ratio` up to `1.0000028` at `d_pt ~ 1e-6`) are the
  radial family itself up to `1e-11` perturbations — at a nearly-double
  critical point the float ODE instrument OVER-reports by `O(noise)`; the
  corpus's instrument-defect entries (NEG 32, 42, 49) documented
  under-reporting at degenerate hubs, this is the OVER direction.  Rule
  restated: near-degenerate-hub measurements are admissible only from the
  exact-fibre instrument at dps >= 40, never from float64 ODE.

### Status of gap #2

Upgraded from "two hunts stall at 0.999386 behind a gate" to: **no violation
found by a gate-free two-tier campaign; the deficit obeys a positive
`0.0705 sqrt(eps)` law along the entire near-radial approach; working
conjecture `(AGG) true at n=3, false for all n >= 4` is now supported by a
campaign that finally sees the equality stratum.**  This is computational
evidence, not a proof; the deep shell remains the weakest instrument zone
(Recorded residual: derive the constant `C_*` by matched-asymptotic
perturbation at the double hub — the inner problem is the n = 3 blow-up
model, the outer correction is the hub displacement; the `sqrt(eps)` scale
and positivity are the theorem-shaped targets).

## Part II — the free-point FP_m experiments (gap #1 program)

`FP_m`: for `c_1..c_m` in the closed unit disk,
`(1/m) Sigma_j (prod_k |1 - conj(c_j) c_k|)^{1/m} <= 1`; `FP_2`, `FP_3`
are proved (`FreePointMeanInequalityFP3.md`).

### Result 4 (sampled truth and extremal structure)

- Adversarial sampling + Nelder-Mead polish (6000 samples + 60 descents per
  m): `sup (1/m) S = 1.0000000` at `m = 2..8` up to optimizer resolution,
  approached by configurations COLLAPSING TO THE ORIGIN.  Equality is
  attained only at `c_1 = ... = c_m = 0` (consistent with the FP_3 equality
  analysis); there is no boundary extremal (boundary points kill the
  diagonal factor).
- Exact flatness identities (ordinary algebra, checker-verified): for the
  balanced m-gon at common radius `r`,
  `S = m (1 - r^{2m})^{1/m}` — e.g. the 4-gon gives
  `S = 4 (1 - r^8)^{1/4}` (each `A_j = 1 - r^8` exactly).  The extremal
  families are EIGHTH-order flat at m = 4 (vs sixth at m = 3): any FP_4
  proof must capture an `O(r^6)`-per-config deficit that vanishes to
  `O(r^8)` on the symmetric family.

### Result 5 (why the FP_3 proof does not mirror; the captured route)

FP_3's engine is a Hölder decomposition whose two d-columns are
PERMUTATIONS of the same multiset (possible iff the complete graph's
directed edges admit the multiset partition — it does at m = 3, and at
m = 2), reducing the chain to `(Σx)(Σd)^2` and then to the exact Delta
identity.  At m = 4 no such permutation assignment exists (each of the 6
pairwise distances appears exactly twice among directed entries, so three
columns with a common 4-entry multiset cannot partition 12 directed
entries).  The naive cyclic-column Hölder chain
`S^4 <= (Σx) D_cyc^2 D_diag` is FALSIFIED as an identity — measured max
`4.0e5` against the needed `256` (the chain is loose by three orders at
boundary-spread configurations).

Captured route (rank-2 Lorentzian structure, per FRONTIER's unused
ingredient): with `N_{jk} = 1 - conj(c_j) c_k` the Gram matrix of
`u_j = (1, c_j)` in the Hermitian form of signature `(1,1)`, and the exact
identity `|1 - conj(c_j) c_k|^2 = |c_j - c_k|^2 + (1-|c_j|^2)(1-|c_k|^2)`
(checker-verified), `A_j = prod_k |N_{jk}|` is a row product of a Lorentzian
Gram matrix.  `FP_m` is therefore a spectral inequality for rank-2
signature-`(1,1)` Gram matrices with cone-point columns; the natural proof
object is a symmetric-function/SOS identity in the real and imaginary parts
at m = 4 (8 real parameters), generalizing the FP_3 Delta identity.  This is
the concrete next step for the FP program, recorded with its obstruction.

## Addendum (same night): the arm-resolved decomposition and the inner model

Measured immediately after the campaign; checker rows in
`check_erdos1041_aggregate_n3_gatefree.py` cover the identities used here.

**Inner model.**  For `f = z^3 - 1 + eps(b2 z^2 + b1 z)` with
`s = sqrt(-eps b1/3)`, the hub split is `c± = -eps b2/3 ± s` and the value
split is `v± = -1 ± (4/3) eps b1 s + O(eps^2)`.  Scaling `z = s w`, the
inner equation is `G(w) = w^3 - 3w = -tau` (hub at `w = 1`, `G(1) = -2`),
and BOTH inner branches from the hub are REAL segments: the right branch
`w in [1, 1 + x*]` with `tau = x^2 (3 + x)`, and the middle branch
`w = 1 - y` with `tau = y^2 (3 - y)` — the arms launch along the HUB-SPLIT
LINE, and in the pure inner model the middle branch runs into the sibling
critical point `w = -1` (a saddle connection, broken at `O(eps^{3/2})` by
the value split in the true family).

**Arm-resolved decomposition (measured, converges smoothly).**  With
`saving(arm) = 1 - |c - a|` and `excess(arm) = L(arm) - |c - a|` per arm,

```text
4R - Sigma_c L(c)  =  Sigma_arms [saving - excess]  +  O(eps^2),
(Sigma_arms [saving - excess]) / (2|s|)  ->  D(phase)
```

with `D = 0.375, 0.489` at the two checker phases (`1e-3 -> 1e-5` rows
converge monotonically; exact per-arm tables in the session scratch).
Pairing observed: the shared root is the one in the split direction; both
hubs feed it.  The shared-root saving is `Re(conj(a_shared)(c+ + c-)) =
O(eps)` (the critical-point sum is `-2 eps b2/3`), so the leading deficit is

```text
2|s| D  =  |s| sqrt(3) cos(theta_s - offset)  -  Sigma_arms excess,
```

a finite-dimensional trigonometric inequality over the phase torus once
`excess(arm) <= K |s|` is established with explicit `K` from the inner
model (launch-mismatch times inner length, plus the outer deformation).
This is the theorem-shaped skeleton for the positivity half of gap #2's
matched-asymptotics CAP; the global closure then needs the corpus's
terminal-strata program (`SeparatrixAggregateReduction.md` "Degree-wise
certifiability": circle-locked + wall strata at n = 3 are
certified-computation-sized).

  NOT a proof of
  `(AGG)` at n = 3; the near-degenerate shell is exactly where both
  instrument classes are weakest, which is why the two-tier design and the
  `0.0705 sqrt(eps)` law (eight decades of phase-torus stability) are the
  load-bearing evidence.  No parent-theorem claim.
- Result 4: sampled + exact algebraic identities (the m-gon flatness
  identities are ordinary algebra).  `FP_m` for `m >= 4` remains OPEN.
- Result 5: the permutation obstruction is an ordinary (checked) counting
  argument; the `4.0e5` falsification of the cyclic Hölder chain is a
  computational measurement.  The Lorentzian route is a RESEARCH PROPOSAL,
  not a result.
- Instrument lesson: float64 ODE instruments OVER-report near nearly-double
  critical points (new defect direction; complements NEG 32/42/49).
- PRIORITY CAVEAT: no literature search; nothing here is claimed new to the
  literature, only new to this directory.

## CORRECTIONS (2026-08-30, derivation session — see `AggregateN3InnerModelClosedForm.md`)

The matched-asymptotic derivation this note's addendum asked for has
landed, as an EXACT reduction, and it corrects three rows here:

1. **Factor-2 slip in the value split** (line "`v± = -1 ± (4/3) eps b1
   s + O(eps^2)`"): the exact split is `v_pm = -1 +- (2/3) eps b_1 s`
   (equivalently `-1 -+ 2 s^3` in the normal form `z^3 - 3 s^2 z - 1`).
   The `O(eps^{3/2})` structure downstream is unaffected.
2. **The headline constant `C = 0.0705(1)` is a wall-adjacent
   instrument artifact, not the law.**  The true law is
   `C(phase) = 2 sqrt(|b_1|/3) * D(phi)` (conversion factor MEASURED,
   checker section 7), with `D` the derived deficit function: minimum
   `D(0) = 3E - (9/4)K - 1/2 = 0.109448...` at the saddle-connection
   wall (closed form, proved positive), maximum `0.608021` at
   `phi = pi/2`.  At `|b_1| = 0.7` the true phase-minimum of `C` is
   `0.1057` — ABOVE the reported `0.0705`.  The gate-free conclusion
   ("no violation; ratio approaches 1 strictly from below at scale
   sqrt(eps)") STANDS and is now proved at the worst phase; only the
   constant's value and its claimed phase-stability were wrong.
3. **Third instrument-defect direction**: at the wall the middle arm
   hits the sibling critical point and real-arithmetic Newton marches
   BRANCH-JUMP at that foreign critical value, first depressing the
   deficit (the `0.0705`) and, pushed further, reporting false AGG3
   violations (`D_march = -0.18` at `|s| = 1e-6` vs exact `+0.121`).
   Complements this note's over-report direction and NEG 32/42/49's
   under-report; the admissible instrument near a saddle connection is
   the globally single-valued `nu`-parametrization of the new note.
   This note's recorded `D = 0.375 / 0.489` rows are CONFIRMED (they
   sit on the derived curve at `phi/pi = 0.0706 / 0.1710`).
