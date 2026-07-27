/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.R2
import ErdosProblems.Rem.C1
import ErdosProblems.Three.T2

/-!
# W3 — scratch: difficulty-class audit of the `#257` half-membership target

This file proves nothing new.  It exists to record two verifications performed
for the W3 (devil's-advocate) review; the review's content is its analysis, not
a theorem.

## 1.  Axiom audit (run, not predicted)

`#print axioms` on the chain named in the W3 brief returns
`[propext, Classical.choice, Quot.sound]` — nothing else — for every one of

* `Erdos249257.half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`
* `Erdos249257.AngleD2.half_mem_iff_unboundedLargestSkipLate`
* `ErdosProblems.BitR2.half_mem_of_remainderReachesHalfPointCofinally`
* `ErdosProblems.BitR2.exists_largestSkipLateAt_of_remainder_le_two_pow`
* `ErdosProblems.ThreeT2.half_mem_of_carryCofinally`
* `ErdosProblems.RemC1.exists_persistent_surplus_model`
* `Erdos249257.irrational_erdosBorweinMersenneConstant`

The chain is clean.  Nothing below disputes any corpus theorem.

## 2.  Measurements re-run from the Lean definitions, independently

`ρ s = seamIntegerGreedyRemainder s` was reimplemented directly from
`truncatedMersenneWeight`, `seamWeights`, `seamSubsetTarget` and
`integerGreedyBits`, and cross-checked against the corpus's certified values
`ρ 14 = 392`, `ρ 15 = 34333`, `ρ 7 = 3`, `ρ 20 = 549353`.

* **Hit density.**  `ρ s ≤ 2 ^ s` at `2996` of the `5996` rows `s ∈ [5, 6000]`:
  density `0.4996664`.  Gap histogram
  `1:1524, 2:706, 3:384, 4:189, 5:94, 6:48, 7:29, 8:10, 9:7, 10:2, 12:1, 13:1`
  — finite counts consistent with a geometric pattern, with maximum gap `13`
  (at `s = 5372`).  This reproduces
  the corpus number exactly.
* **The direct criterion is far commoner than the hit.**  Computing the largest
  false rank `d₀ s` of the row-`s` greedy word and testing `2 s < 3 d₀ s`
  (`LargestSkipLateAt`) over `s ∈ [5, 1500]`: it **fails at exactly
  `s = 5, 11, 12, 13`** and nowhere else.  `d₀ 81 = 75`, `d₀ 1148 = 1135`,
  `d₀ 1500 = 1499`, matching `H4` and `Corr3`.  Top-take-run histogram
  `1:718, 2:368, 3:191, 4:100, 5:53, 6:30, 7:16, 8:9, 9:5, 10:2, 11:2, 12:1,
  13:1` — again finite counts with maximum `13`.
  On this range the late-skip predicate holds at `1492/1496` rows.  No limiting
  density or asymptotic error term is proved.
* **Sampled row-word compatibility.**  The taken ranks of `seamGreedyWord s`
  agree, for the five sampled rows `s ∈ {40, 60, 100, 200, 400}`, with a common
  prefix
  `2, 3, 6, 7, 14, 20, 21, 26, 27, 32, 33, 34, 35, 38, 39, 42, 44, 45, 46, 47,
  48, 49, 50, 51, 53, 55, 56, 57, 58, 59, 60, 63, 65, 66, 70, 74, 75, 82, 86,
  87, …`.  An independent exact computation gave the same prefix for the greedy
  Mersenne expansion of `1/2`.  These five samples do not prove that all row
  words are prefixes of one infinite word.
* **The Cantor margin.**  With `r d` the exact greedy residual of `1/2` before
  rank `d` and `A d = ∑_{m ≥ d} 1/(2^m − 1)`, put `μ d = (A d − r d) / A d`.
  Over `d ∈ [2, 2000]`: mean `0.5100`, median `0.5086`, `P(μ < 0.1) = 0.102`,
  `P(μ < 0.01) = 0.0175`, finite statistics consistent with a broad
  distribution on `(0,1)`.  Minimum `1.13e−4`, at
  `d = 1136`.  The take-run length `L d` starting at rank `d` satisfies
  `L d = ⌊−log₂ μ d⌋` in the tested range (`−log₂ μ d − L d ∈ [0.002, 1.000]` over
  `d ≤ 1500`).  `1/2 ∉ mersenneAchievementSet` requires `μ d < 0`, whose
  distance from the observed record low at `d = 1136` is a factor `≈ 2 ^ 1123`.
* **Other tested targets.**  Run against other targets, the same greedy *fails*
  at `d = 3` for `3/10` and `1/π` and at `d = 4` for `0.47`; it survives with
  record margins `3.1e−3` for `√2 − 1` and `3.6e−3` for `0.55`.  About `40 %` of
  targets in the sampled experiment fall into a gap, mostly at small ranks.
  This finite comparison does not establish a distribution over targets or a
  general statement that `1/2` is typical.

Checked with `lake env lean ErdosProblems/Hlow/W3.lean` (exit `0`, empty
output).  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace ErdosProblems.HlowW3

end ErdosProblems.HlowW3
