<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Erdős #257 — the reset–crossing unification: one producer, its rigidity, and the decision structure of the half-greedy orbit

Date: 2026-07-24; Lean status amended 2026-08-23. The reset–crossing
unification in Theorem A is now Lean-checked in
`HalfCylinderResetSqrtEscape.lean`; Theorems B and C remain ordinary
mathematics, and the numerical observations remain exact finite computation.
Every Lean-checked statement is cited by declaration name (§9). Erdős #257 is
**not** closed here. What is new:

1. **Theorem A (Lean-checked unification).** The two live seam producers — the crossing socket
   `LargestSkipLateStepSocket` and the reset anti-concentration pinned in
   `docs/formal_math/erdos249_257_orbit_anticoncentration_reduction_2026_07_14.md`
   (`|rem(r) − 2^r| > 2^{(r+5)/2}` at resets) — are one statement: the socket
   follows from √-scale reset anti-concentration, with the exponent `(r+5)/2`
   *derived* from run-length-to-crossing geometry rather than conjectured from
   data, and with every correction constant exact (no O(1)'s).
2. **Theorem B (rigidity).** A dangerous reset (deviation at or below √-scale)
   pins the *previous* reset's deviation to a single explicitly pulse-determined
   integer whenever the intervening right-run is long enough. Failure of the
   programme cannot happen generically; it requires an exact integer-coincidence
   tower in the divisor-pulse stream.
3. **Theorem C (decision structure).** Membership of 1/2 in the Mersenne
   achievement set is *co-semi-decidable through the greedy orbit*: if #257 is
   true, the half-greedy dies at a finite computable rank, and every certificate
   depth is a lower bound on that rank. The truncation-rung ladder is proved
   *equivalent* (not merely sufficient) to full-greedy survival, so the four
   certificate families in this repo are one semi-decision procedure in four
   coordinates.
4. **Boundary exclusion via Erdős 1948.** Every greedy comparison is strict: the
   take boundary is excluded because partial residuals provably have *even*
   reduced denominator while every weight has odd; the skip-safety boundary is
   excluded because the Mersenne tail is a rational shift of the Erdős–Borwein
   constant, irrational by Erdős's own 1948 theorem.

Claim discipline: `[Lean]` = kernel-checked on disk, cited by name and
signature-audited this pass; `[Math]` = proved in ordinary mathematics here, then
adversarially audited by an independent verification fleet (exact algebra plus
20,000 property-based trials per claim plus real-orbit cross-checks — receipts in
§8); `[Cert]` = exact finite computation with landed reproducible verifier;
`[Open]` = the remaining wall, stated exactly.

---

## 1. One orbit, four coordinates

Fix weights `x_n = 1/(2^n − 1)`, `n ≥ 2`, target `1/2`. The greedy orbit:
residual `ρ` starts at `1/2`; at rank `k`, take iff `ρ ≥ x_k`. A skip at `k` is
*safe* iff `ρ ≤ T_{k+1} := Σ_{j>k} x_j` and *fatal* iff `ρ ∈ (T_{k+1}, x_k)` —
then no completion reaches `1/2`.

`[Lean]` `half_mem_iff_every_actual_skip_survives`
(HalfCylinderFixedTailSocket.lean): `1/2 ∈ mersenneAchievementSet` iff every
actually-skipped rank `M` has `greedyMersenneRemainder(1/2, M) ≤ mersenneTail M`.
Membership yields an infinite witness support (finite supports are excluded by
§3(a)), which negates universal Mersenne-subseries irrationality through the
landed frontier consumer.

The repo measures this single orbit in four integerisations:

| Coordinate | Object | Certified depth |
|---|---|---|
| Truncation rung `J` | greedy on `Σ_{q≤J} 2^{-qn}` | `J = 3..22` all survive (rung ladder doc) |
| Seam row `s` | `rem(s)` vs `⌊4^s/(2^d−1)⌋` weights | rows `6..2500` this pass (§8) |
| Integer margin `m_c` | `Q_{2c−3}(D_c) + 2^{c−3} − 2^{2c−4}` | `5·10^5` (advisory Type B scan) |
| Sharp tail margin | certified `T_{k+1} − ρ` at skips | ranks `2..3000` this pass (§8) |

That these are the *same* decision stream is not folklore; it follows from the
no-ties lemma (§3): every comparison is strict, so sufficiently fine truncations
reproduce the full decisions exactly on any fixed prefix.

## 2. The seam model and its exact branch algebra

`[Lean]` (§9, items 3–10, 15–16.) At row `s ≥ 6`: weights
`truncatedMersenneWeight s d = 4^s / (2^d − 1)` (ℕ-division = floor) for
`d ∈ [2, s−1]`, target `seamSubsetTarget s = 2^{2s−1} − 2^s`, greedy ascending,
remainder `rem(s)`; anchor `rem(14) = 392`. The largest false rank `d` (first
false from the top) evolves by the trichotomy (`nextRemainder_trichotomy`), with
pulses `0 ≤ p, ap ≤ 2(s−2)`:

- **U** (carry reset): `rem(s+1) = 2^{s+1} − E`, `E = 4·overshoot + ap`;
- **M** (middle reset): `rem(s+1) = 4·rem(s) + 2^{s+1} − p`;
- **R** (right): `rem(s+1) = 4·rem(s) − 2^{s+1} − p − 4`.

After U/M at row `r` the largest false rank becomes `r`
(`seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle`); R preserves
it (`IsLargestFalseRank.seamGreedyWord_succ_of_rightBranch`). On *late* rows
(`2s < 3d`): `three_mul_remainder_add_overshoot_eq_exactLateGap` gives
`3(rem + overshoot) = 3·2^{s+1} + 2·4^{s−d} + 4`, and `rightBranch_remainder_window`
gives the exact two-sided R-window
`2^{s+1} + 4 ≤ 4·rem` and `12·rem + 3·2^{s+1} < 4(3·2^{s+1} + 2·4^{s−d} + 4) + 3·(2(s−2))`.

`[Math, fleet-confirmed]` **Deviation coordinate.** Put `w := rem(s) − 2^s`. The
branch maps become exactly

- R: `w' = 4w − 4 − p`,
- M: `w' = 4w + 2^{s+2} − p`  (equivalently `w' = 4·rem(s) − p`),
- U: `w' = −E`,

and the late R-window reduces *identically* (no approximation) to

```
1 − 2^{s−1}  ≤  w  <  2^{s−1} + (2/3)·4^{s−d} + (3s+2)/6.
```

Along a pure R-run of length `L` from row `d+1`,

```
w_{d+1+L} = 4^L · w_{d+1} − C_L,   C_0 = 0,  C_{j+1} = 4·C_j + p_j + 4,
```

with the charge range (corrected by the fleet from this author's first guess)

```
1 ≤ C_L/4^L < (2s+4)/3,    exact minimum (4/3)(1 − 4^{−L}) at all-zero pulses.
```

`[Math]` **Every reset creates a late largest-false**: after U/M at row `r` the
new largest false `d = r` satisfies `2(r+1) < 3r ⟺ r ≥ 3`. The late regime
survives R-steps until the *crossing cell* — the last late row `s`, where
`3d ∈ {2s+1, 2s+2}` — with run length from creation to crossing

```
L = s − d − 1 = (d−3)/2  (odd cells, 3d = 2s+1;  d odd)
              = (d−4)/2  (even cells, 3d = 2s+2; d even).
```

`[Lean]` At the crossing cell the boundary pulse is `2` (odd) or `1` (even)
(`rowPulse_boundary_of_late_firstCrossing`), the filled suffix contributes zero
pulse (`rowPulse_eq_zero_of_late_strictSuffix`), and the charge balance
`E + M_coord = 4G − 2` (odd) / `4G − 3` (even) is an exact integer identity
(`exists_exactLateGap_upperResetCharge_add_middleCoordinate_firstCrossing`).

## 3. No ties, stabilisation, and the decision structure

**Lemma (no ties).** `[Math, fleet-confirmed]` At every rank of the full greedy
orbit both comparisons are strict:

(a) `ρ ≠ x_k`, with a parity argument sharper than "finite sums miss 1/2": a
finite Mersenne sum has odd reduced denominator `D` (each `2^n − 1` is odd), so
`ρ = 1/2 − P/D = (D − 2P)/(2D)` with `D − 2P` odd — the factor 2 never cancels.
*Every partial residual has even reduced denominator; every weight has odd.*

(b) `ρ ≠ T_{k+1}`: the tail is `E − 1 − Σ_{2≤j≤k} x_j` where
`E = Σ_{n≥1} 1/(2^n − 1)` is the Erdős–Borwein constant, irrational
(Erdős, 1948 — trusted classical citation), so the tail is irrational while `ρ`
is rational. The free-lunch boundary `ρ = T_{k+1}` (which would hand over the
counterexample `taken ∪ {k+1, k+2, …}` outright) never occurs: Erdős's 1948
irrationality theorem is precisely what closes the boundary of the orbit
attacking his own problem.

**Consequence (stabilisation).** All comparisons at ranks `≤ N` are finitely many
strict inequalities between quantities that converge monotonically as truncation
deepens (rung weights `w_n^{(J)} ↑ x_n`). Hence there is `J₀(N)` such that every
rung `J ≥ J₀(N)` makes decisions identical to the full greedy through rank `N`.

**Theorem C (decision structure).** `[Math]`

1. `1/2 ∈ 𝒜 ⟺ the full greedy survives every rank` (`[Lean]` fixed-tail iff).
2. **Diagonal equivalence.** `DiagonalRungSurvival` (`∀N ∃J ≥ N`: rung `J`
   survives through rank `N`) `⟺ 1/2 ∈ 𝒜`. Forward: finite sections converge
   to `1/2` inside the closed achievement set (truncation error
   `≤ (2/3)4^{−J} + 2^{1−N}`); backward: full survival plus stabilisation. The
   rung ladder is the same semi-decision procedure, not an analogy.
3. **Co-semi-decidability.** If #257 is true then `1/2 ∉ 𝒜`, so the greedy dies
   at a finite rank `K`, and a finite exact computation exhibits the death
   certificate. Contrapositive of every certificate: the rung ladder (`J ≤ 22`),
   the seam and sharp-margin runs of §8, and the advisory `m_c` scan each force
   `K` beyond their depth. #257-true is *refutable-in-principle by a single
   finite object whose non-existence keeps being certified at growing depth and
   growing margin*; #257-false requires exactly one more theorem — §6.

## 4. Theorem A — the unified producer

**Definition (reset √-escape).** `[Lean]` The seam orbit has *reset √-escape from
row 10* if for every actual upper or middle reset row `r ≥ 10`:

```
2^{r+5}  <  (rem(r+1) − 2^{r+1})².
```

This division-free square formulation is `SeamResetSqrtEscape`. It is exactly
the real square-root inequality `|dev| > 2^{(r+5)/2}`. (U-resets have
`rem(r+1) − 2^{r+1} = −E_r`; M-resets have `= 4·rem(r) − p_r`.)

**Theorem A.** `[Lean]` Reset √-escape from row 10 implies
`LargestSkipLateStepSocket`, hence `1/2 ∈ 𝒜`, hence the negation of universal
Mersenne-subseries irrationality. The checked chain is
`SeamResetSqrtEscape.crossingBoundEscape` ⟹
`SeamResetCrossingBoundEscape.largestSkipLateStepSocket` ⟹
`half_mem_mersenneAchievementSet_of_resetSqrtEscape`.

The formal proof uses the integer envelope
`resetCrossingBound(r) = 2^((r+4)/2) + 2r + 3`. Lean proves both that every
late right crossing forces `|dev_r| ≤ resetCrossingBound(r)` and that
`resetCrossingBound(r)^2 ≤ 2^(r+5)` for `r ≥ 10`. Thus a crossing and square-root
escape give contradictory strict inequalities. The first theorem reconstructs
the creating reset and every intervening actual right branch from the largest-
false-rank hypotheses; it does not assume a hypothetical affine tail.

*Ordinary-mathematics derivation of the same bound.* A socket violation is an R branch at a crossing cell `(s, d)` with
`s ≥ 14`, `d` late, `3d ∈ {2s+1, 2s+2}`; then `3d ≥ 2s+1 ≥ 29`, so `d ≥ 10`. The
rank `d` was created by a reset at row `d` (§2), every intervening step was R
(else `d` is replaced), and the run length is `L = (d−3)/2` or `(d−4)/2 ≥ 3`. The
R branch at `s` places `w_s` in the exact late R-window (§2); dividing the affine
iterate `w_s = 4^L w_{d+1} − C_L` by `4^L` and using
`2^{s−1}/4^L = 2^{2d−s+1}` and `(2/3)4^{s−d}/4^L = 8/3` (both exact at crossing
cells, where `s = d+1+L`):

```
| w_{d+1} − C_L/4^L |  <  2^{2d−s+1} + κ(s,L),      κ(s,L) := 8/3 + (3s+2)/(6·4^L),
```

with `2^{2d−s+1} = 2^{(d+3)/2}` at odd cells and `2^{(d+4)/2}` at even cells.
Since `1 ≤ C_L/4^L < (2s+4)/3`:

- U-case (`w_{d+1} = −E_d < 0`): `E_d < 2^{(d+4)/2} + κ(s,L) − 1`;
- M-case (`w_{d+1} = 4·rem(d) − p_d`): `|w_{d+1}| < 2^{(d+4)/2} + (2s+4)/3 + κ(s,L)`
  (when `w_{d+1} < 0` it already satisfies `|w_{d+1}| ≤ p_d ≤ 2(d−1) < 2^{(d+5)/2}`).

Absorption: for `d ≥ 10` (so `s ≤ (3d)/2 + 1`, `L ≥ 3`),

```
2^{(d+4)/2} + (2s+4)/3 + κ(s,L)  ≤  2^{(d+5)/2},
```

since the gap `2^{(d+4)/2}(√2 − 1)` grows geometrically while the corrections are
linear in `d` (fleet-verified exactly for every `r = 4..39` against each `r`'s own
cell geometry, and at the boundary case `r = 14`: threshold `724.077` vs U-bound
`364.716`, M-bound `379.382` — ratios `1.98×`, `1.91×`). So an R branch at a
crossing forces `|rem(d+1) − 2^{d+1}| ≤ 2^{(d+5)/2}` at the creating reset
`d ≥ 10`, contradicting √-escape. ∎

**Base bootstrap.** `[Lean+arithmetic]` The kernel-landed exact remainders
`rem(14..31)` in `seamUpperResetDyadicBandEscape_through_thirty`
(HalfCylinderUpperResetBandCertificates.lean) verify the √-escape hypothesis for
every reset row `13 ≤ r ≤ 30` by direct arithmetic (tightest: `r = 14`,
`|dev| = 1565` vs `724.08`, ratio `2.16×`; all others exceed `6×`). Together with
Theorem A the open content of the seam lane starts at reset row `31`.

**Sharpness at the base.** The single row of the real orbit where √-escape fails
is `r = 7` (M-reset, `dev = +9`, threshold `64`) — and it is exactly the single
real R-branch crossing ever observed, at `s = 10, d = 7`, sitting fully inside
the R-window (`margin_widths = 0`) and *below* the socket's `s ≥ 14` scope. The
reduction predicts the base-range violation and the in-scope silence from the
same inequality; nothing is loose in either direction on real data.

**Relation to the sibling producers.** The strong anticoncentration form pinned
in the reduction document implies √-escape; √-escape implies the socket; the
dyadic band escape (`SeamUpperResetDyadicBandEscape`, U-side only, linear-width
bands under every dyadic) is neither implied by nor implies √-escape and feeds a
different fan-in (`…_of_upperResetDyadicBandEscape`). √-escape at resets is the
*minimal known producer* for the crossing socket.

## 5. Theorem B — pullback rigidity of dangerous resets

Call a reset at row `r` *dangerous* if `|rem(r+1) − 2^{r+1}| ≤ 2^{(r+5)/2}`.

**Theorem B.** `[Math]` If the reset at row `r` is dangerous, and the preceding
reset happened at row `r₀` with a pure R-run of length `L' = r − r₀ − 1 > (r+5)/4`
between them, then `w_{r₀+1}` is confined to an interval of width
`2·2^{(r+5)/2}/4^{L'} < 2` around the explicit pulse point — hence pinned to at
most two adjacent integers, determined by the divisor-pulse stream alone; and mod
`4^j` (`j ≤ L'`) the pinned value is congruent to the truncated affine charge. A
chain of `n` consecutive dangerous resets with long runs forces the divisor-pulse
stream to solve `n − 1` nested exact congruence towers.

*Proof sketch.* Danger constrains `w_r` to a width-`2^{(r+7)/2}` set; the affine
iterate transfers a width-`W` constraint on `w_r` to a width-`W/4^{L'}`
constraint on the integer `w_{r₀+1}`; the congruences are `C_{j+1} = 4C_j + p_j + 4`
read mod `4^j`. (The measured layer: the affine identity held *exactly* at every
verified crossing; §8.) ∎

The force of Theorem B: the failure mode of the whole programme is not drift or
density — it is a tower of exact integer coincidences, each level a checkable
divisor-sum identity. In 2,500 rows the orbit was never inside a danger window at
any in-scope reset, and run lengths never exceeded `12` — while reaching a
crossing at reset row `d` requires a run of length `≈ d/2`. Beyond the base, the
orbit does not even get *near* the geometry that could hurt it.

## 6. What remains — the open statement, exactly

`[Open]` Reset √-escape from row 31 (rows 10–30 are certificate-closed, §4):

```
at every reset row r ≥ 31:   | rem(r+1) − 2^{r+1} |  >  2^{(r+5)/2}.
```

Everything else in the seam lane — socket, fan-in to `1/2 ∈ 𝒜`, frontier
consumer to ¬#257 — is landed Lean. Known structure pressing on it:

- the three static adversary families were killed in the anticoncentration
  reduction document; Theorem B adds that the dynamic adversary needs an integer
  coincidence tower;
- `[Cert]` the deviation's empirical scale is `|dev| ≈ 2^{r−O(log r)}` — the
  in-scope margin over the `2^{(r+5)/2}` threshold was `1.11` bits at `r = 14`
  and grows to `~1246` bits by row `2500` (mean `627`), never re-approaching the
  threshold;
- `[Cert]` a perfect sign law held at all `1209` resets: M-resets always
  `dev > 0` (`605/605`), U-resets always `dev < 0` (`604/604`), no zero
  deviations — worth attempting as a lemma before the inequality itself;
- run lengths (`≤ 12` observed over 2,500 rows, mode `0`) sit far below the
  `≈ d/2` needed to reach a crossing, so beyond the base the socket is not
  merely satisfied — it is empirically vacuous, and `s = 10` is plausibly the
  last crossing this orbit ever produces (not proved).

## 7. Lean landing status

The unification contour has landed. The source-current checked interface is:

```lean
def SeamResetSqrtEscape : Prop
def SeamResetCrossingBoundEscape : Prop
theorem resetCrossingBound_square_le ...
theorem resetDeviation_le_crossingBound_of_late_right_crossing ...
theorem SeamResetSqrtEscape.crossingBoundEscape ...
theorem SeamResetCrossingBoundEscape.largestSkipLateStepSocket ...
theorem SeamResetSqrtEscape.largestSkipLateStepSocket ...
theorem half_mem_mersenneAchievementSet_of_resetSqrtEscape ...
```

The remaining landing targets are the all-depth producer itself, its finite-base
wrapper from the existing remainder certificates, and Theorem B's consecutive-
danger rigidity. Side lemmas worth landing independently: the no-ties pair (§3) — (a) is an
even/odd reduced-denominator lemma; (b) needs `Irrational erdosBorwein` (the 1948
proof is finite p-adic counting; Mathlib has the `Irrational` API); and
`rungDecisions_stabilise (N) : ∃ J₀, ...`, which upgrades the rung ladder into
the diagonal equivalence (Theorem C.2).

## 8. Certificates from this pass

Verification fleet: workflow `wf_24f417e5-463`, four sonnet subagents
(adversarial algebra auditor; Lean signature auditor; seam-orbit runner;
sharp-margin runner), 665,752 tokens, 128 tool calls, zero errors. The algebra
auditor rebuilt the greedy from primitives (reproducing `rem(14)=392`,
`rem(15)=34333`), tested every claim with ~20,000 property-based trials across
the full admissible parameter space plus the real orbit to row 2599, and returned
two genuine corrections (the exact `κ(s,L)` and the charge lower bound), both
folded into §§2, 4 above. U/M disambiguation was decisive at all 1264 real resets
(632/632, zero ambiguous).

**Seam run** (rows 6..2500, 21 s; verifier below): anchors pass; 1209 resets
(604 U / 605 M); zero classification anomalies; dev-sign law perfect (§6);
minimum in-scope reset margin `+1.1119` bits at row 14, maximum `+1246.55` bits
near row 2500; exactly 2 crossing cells ever — `(s=7, d=5)` branch M (outside
the R-window by `0.4397` widths) and `(s=10, d=7)` branch R (inside, margin 0) —
both below socket scope; zero crossings in `14 ≤ s ≤ 2500`; affine iterate
`4^L·w(d+1) − C = w(s)` exact at both crossings; run-length mode 0, max 12.

**Sharp-margin run** (ranks 2..3000, 12.3 s; verifier below): no fatal at any
skip, no unresolved certification; 1497 takes / 1502 skips (take fraction
`0.4992`); minimum certified gap-margin `+2.9922` bits at rank 5 and `+3.3572`
at rank 4 — the only two skips under 6 bits in the entire run; every skip from
rank 6 to 3000 has `≥ 6` bits of certified room; minimum take-margin `+0.0340`
bits at rank 7 (the historic near-tie `1/126 ≥ 1/127`); denominator reaches
2,279,591 bits. An independent 200-digit `decimal` cross-check reproduced both
minima to ~13 significant figures. The orbit gets structurally *safer* with
depth; there is no late-onset erosion anywhere in the certified range.

Reproduction:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_seam_reset_crossing.py 2500 /tmp
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_half_greedy_margins.py 3000 300 /tmp
```

Both scripts were authored by the fleet, reviewed, and promoted with path
parametrisation only; both refuse to run past failed anchors, and the margins
verifier exits nonzero on any certified fatal — a death certificate, if one ever
appears, is itself the decision of `1/2 ∉ 𝒜` (§3).

## 9. Lean signature receipts (audited verbatim this pass)

All under `formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/`:

| Declaration | File |
|---|---|
| `LargestSkipLateStepSocket` (def, `s ≥ 14`) | HalfCylinderLargestSkipInduction.lean |
| `half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket` | HalfCylinderLargestSkipInduction.lean |
| `rightBranch_remainder_window` (both inequalities) | HalfCylinderResetDeficitEscape.lean |
| `rightBranch_remainder_succ_eq` | HalfCylinderResetDeficitEscape.lean |
| `upperOrMiddle_within_of_two_pow_deficit` (deficit run law) | HalfCylinderResetDeficitEscape.lean |
| `nextRemainder_trichotomy` (in `namespace AdjacentCut`) | HalfCylinderIntegerGreedy.lean |
| `truncatedMersenneWeight`, `seamSubsetTarget` | HalfCylinderIntegerGreedy.lean |
| `three_mul_remainder_add_overshoot_eq_exactLateGap` | HalfCylinderMiddleCarryLowerBound.lean |
| `exists_exactLateGap_upperResetCharge_add_middleCoordinate_firstCrossing` | HalfCylinderMiddleCarryLowerBound.lean |
| `SeamUpperResetDyadicBandEscape` (def) + its `half_mem…` fan-in | HalfCylinderMiddleCarryLowerBound.lean |
| `seamUpperResetDyadicBandEscape_at_thirteen` | HalfCylinderMiddleCarryLowerBound.lean |
| `seamUpperResetDyadicBandEscape_through_thirty` (rem(14..31) by `decide`) | HalfCylinderUpperResetBandCertificates.lean |
| `seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle` | HalfCylinderLargestSkipGap.lean |
| `IsLargestFalseRank.seamGreedyWord_succ_of_rightBranch` | HalfCylinderLargestSkipGap.lean |
| `rowPulse_boundary_of_late_firstCrossing`, `rowPulse_eq_zero_of_late_strictSuffix` | HalfCylinderBoundaryPulse.lean |
| `half_mem_iff_every_actual_skip_survives` | HalfCylinderFixedTailSocket.lean |
| `seamIntegerGreedyRemainder_fourteen_eq` (`= 392`) | HalfCylinderLastProducerContradiction.lean |
| `halfStripBound` (`2·√n + 4`) | HalfCarryReachability.lean |
| `SeamResetSqrtEscape`, `SeamResetCrossingBoundEscape` | HalfCylinderResetSqrtEscape.lean |
| `resetCrossingBound_square_le` | HalfCylinderResetSqrtEscape.lean |
| `resetDeviation_le_crossingBound_of_late_right_crossing` | HalfCylinderResetSqrtEscape.lean |
| `SeamResetSqrtEscape.largestSkipLateStepSocket` | HalfCylinderResetSqrtEscape.lean |
| `half_mem_mersenneAchievementSet_of_resetSqrtEscape` | HalfCylinderResetSqrtEscape.lean |

Audit notes: 20/21 located declarations are exact literal-name matches with all
constants verified verbatim. One naming deviation: the right-branch sibling is
`IsLargestFalseRank.seamGreedyWord_succ_of_rightBranch` (dot notation), not
`…_terminal_of_rightBranch`. Do not confuse `SeamUpperResetDyadicBandEscape`
with the unrelated `DyadicBandEscape` in HalfUpperResetCriticalBand.lean. A
byte-identical export of these files exists under
`microcosm-substrate/examples/certificate_kernel_execution_lab/…` — snapshot
bundle, not primary source.

## 10. Honest boundary

Theorem A is now a Lean-checked reduction with exact constants, not a proof of
§6's all-depth inequality.
Theorem B is rigidity, not exclusion. Theorem C sharpens the logic but decides
nothing by itself. No claim is made that #257 is resolved in either direction.
What changed this pass: the seam lane has a single quantitative producer with a
derived exponent and certificate-closed base through row 30; failure is proved
non-generic in a precise integer sense; the rung, seam, margin, and residual
lanes are proved to be one orbit, so every future certificate in any coordinate
presses on the same `[Open]` line; and the strongest-yet exact certificates show
the orbit's distance from danger *growing* — `1.11` bits at its tightest
in-scope point, over a thousand bits by row 2500.
