/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.R1
import ErdosProblems.Bit.R2
import ErdosProblems.Bit.R3

/-!
# Rem C3: the hit set of `rem s ≤ 2 ^ s`, and what its gap structure does and does not buy

`Bit/R2` reduces the `1/2` question of Erdős `#257` to one inequality holding
cofinally: `RemainderReachesHalfPointCofinally`, i.e.
`seamIntegerGreedyRemainder s ≤ 2 ^ s` at arbitrarily large `s`.  Write
`HitAt s` for that inequality and call `{s | HitAt s}` the **hit set**.

This file does two things.

## 1.  The gap route, and its sharp refutation at small `K`

The obvious way to force cofinality is a *bounded gap*: if every window of
length `K` meets the hit set then the hit set is cofinal and `#257`'s `1/2`
question is answered positively.  That implication is
`half_mem_of_hitGapBoundedBy`, and it is the entire content of the "bounded
gap" idea.

The file then kills the small-`K` instances of it outright.  An
arbitrary-precision replication of `seamWeights`, `seamSubsetTarget` and
`integerGreedyBits` (checked against `#eval` on the Lean definitions at
`s = 0,…,24, 40, 63, 100, 137, 199`) computes the hit set on `[3, 2000]`:

* density `979/1998 ≈ 49%`, stable across every sub-block;
* the multiset of gaps between consecutive hits is
  `1 : 492, 2 : 227, 3 : 120, 4 : 70, 5 : 35, 6 : 15, 7 : 10, 8 : 6, 9 : 2,
  10 : 1` — geometric with ratio `1/2` to within sampling error;
* the **maximal gap is `10`**, realised exactly once, between the consecutive
  hits `502` and `512`;
* the maximal gap over `[3, S]` is `7, 9, 9, 10, 10, 10` for
  `S = 100, 200, 500, 1000, 1500, 2000`, tracking `log₂ S`.

Extending the scan to `[3, 4500]` leaves the picture unchanged: `2266` hits out
of `4498` rows (`50.4%`), maximal gap still `10`, first occurrence of gap `k`
at `k = 8, 9, 10` being `174, 113, 502`.

`not_hitGapBoundedBy_eight` certifies the record run in the kernel:
`rem s > 2 ^ s` at all nine rows `503, …, 511`, with hits at `502` and `512`.
So `HitGapBoundedBy K` is **false** for every `K ≤ 8`, and the measurement says
the least admissible `K` grows like `log₂` of the range — the hit gap is not
bounded by any constant that can be read off a finite computation.

At the time this file was written, only the right-branch recurrence
`rem (s+1) + 2 ^ (s+1) + pulse + 4 = 4 * rem s`
(`rightBranch_remainder_succ_eq`) was **PROVED**; the corresponding
upper/middle-branch formula was **MEASURED**.  `ErdosProblems/Three/T2.lean`
later proves the missing branch identities
`middleBranch_remainder_succ_eq` and `upperBranch_remainder_succ_eq'`.
Those identities do not give an exact conjugacy: after normalising
`u s = rem s / 2 ^ s`, the pulse term remains as a perturbation of size
`O(s / 2 ^ s)`.  The resulting map is a summably perturbed doubling map, not
literally `y ↦ 2 * y mod 1`.  Moreover `ThreeT2.two_pow_mul_y` proves that the
normalised point at every finite row is dyadic, so a finite-row
non-dyadicity argument cannot establish cofinal hits.

The following run remains **MEASURED**, not proved: for `s = 503, …, 511`,
`u` is
`1.003244, 1.006488, 1.012976, 1.025953, 1.051906, 1.103812, 1.207624,
1.415247, 1.830494`, each the previous doubled minus one, and `u 512 = 0.660988
= 2 * 1.830494 - 3`.  Its resemblance to a Bernoulli-`1/2` orbit explains the
observed logarithmic gaps, but it is not a theorem about this deterministic
sequence.  The proved branch identities and the finite measurements do not
provide a bounded-gap theorem for `#257`.

## 2.  What the measurement *does* buy: the ceiling decouples

`Bit/R2`'s Theorem B (`exists_largestSkipLateAt_of_surplus`) is conditional on
`ObeysRemainderCeiling (3 * N + 2)` — the ceiling at one *specific* row, paired
with the base row `N`.  That pairing is what makes
`RemainderMissesHalfPointWindowCofinally` awkward to certify: it demands the
window-escape at `s` and the ceiling at `3 * s + 2` *simultaneously*, at
cofinally many `s`.

The main new results here remove the pairing.

* `obeysCeiling_of_succ_of_bad` — **the ceiling propagates downward across a
  bad row.**  If row `s + 1` is bad then the row-`s` step is a right branch, and
  the right-branch recurrence *contracts* the ceiling: `3 * rem (s+1) <
  7 * 2 ^ (s+1) + 4` forces `3 * rem s < 5 * 2 ^ s + O(s)`, comfortably inside
  the ceiling at `s`.  Note the direction: the half point is repelling upward,
  so the ceiling can only be transported *down*.
* `obeysCeiling_of_badRun` — the iterate.
* `exists_largestSkipLateAt_of_surplus_of_ceiling_above` — **Theorem B with the
  ceiling hypothesis moved off its row.**  A surplus of at least `2 * N` at row
  `N` produces a late largest false rank above `N` as soon as *some* row at or
  above `3 * N + 2` obeys the ceiling.
* `pinned_of_ceilingCofinally_of_not_half_mem` — **the unconditional pin.**  If
  the ceiling merely holds cofinally, then failure of `1/2 ∈
  mersenneAchievementSet` forces `2 ^ s < rem s < 2 ^ s + 2 * s` at *every*
  sufficiently large row.  `Bit/R2`'s `badRun_pins_remainder` gives this only at
  base rows whose whole `[N+1, 3N+2]` block is bad and whose top row is known to
  obey the ceiling; here the hypothesis is a bare cofinality statement.
* `half_mem_of_ceilingCofinally_of_pinEscapes` — the endpoint, with the two
  cofinality hypotheses fully decoupled.  Strictly weaker than
  `RemainderMissesHalfPointWindowCofinally`.

The surviving configuration is exactly the corpus's named obstruction: `rem s =
2 ^ s + a s` with `1 ≤ a s < 2 * s`, on which `stepLaw_pow_add_two` shows the
recurrence is satisfied identically.  The measurement says it is never entered —
over `[5, 3000]` the pin window `(2 ^ s, 2 ^ s + 2 * s)` is occupied at exactly
one row, `s = 8`, and `rem s < 2 ^ (s + 1)` at every row except `s = 5`, with
worst ratio `rem s / 2 ^ s = 1.99989` at `s = 1135` — but the cofinal statement
is not proved here.  Note that the second measurement is `CeilingCofinally` with
room to spare (`2 < 7/3`); an unconditional bound `rem t = O(λ ^ t)` for any
`λ < 3` supplies it, because along a bad run the surplus triples
(`surplus_iter`) while the only unconditional bound the corpus has,
`rem t ≤ seamSubsetTarget t ≈ 4 ^ t / 2`, grows by `4`.  That is the precise
shape of the missing input, and it is the target of `Rem/C2`.

## Non-vacuity

The local hypotheses used by the ceiling and pin-transfer theorems have
kernel-checked instances in section 5.  Three global hypotheses are not
exhibited: `CeilingCofinally`, `PinEscapesCofinally`, and
`HitGapBoundedBy K`.  The first two have their inner predicates certified at a
spread of concrete rows (`29, 100, 502, 1200`), but cofinality is not proved.
No `K` is known for the bounded-gap condition; `not_hitGapBoundedBy_eight`
proves it false for every `K ≤ 8`, and larger ranges show growing gaps only by
measurement.
-/

namespace ErdosProblems.RemC3

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.BitR2

/-! ## 1. The hit set and the bounded-gap criterion -/

/-- Row `s` is a **hit**: the deterministic seam greedy remainder has not risen
above the half point.  Cofinality of the hit set is exactly `Bit/R2`'s
`RemainderReachesHalfPointCofinally`. -/
def HitAt (s : ℕ) : Prop := seamIntegerGreedyRemainder s ≤ 2 ^ s

/-- The hit set meets every window of length `K`. -/
def HitGapBoundedBy (K : ℕ) : Prop :=
  ∀ s : ℕ, ∃ t : ℕ, s ≤ t ∧ t ≤ s + K ∧ HitAt t

theorem remainderReachesHalfPointCofinally_of_hitGapBoundedBy {K : ℕ}
    (h : HitGapBoundedBy K) : RemainderReachesHalfPointCofinally := by
  intro N
  obtain ⟨t, h1, _, h3⟩ := h (max N 5)
  exact ⟨t, by omega, by omega, h3⟩

/-- **The bounded-gap criterion.**  Any constant bound on the gaps of the hit
set answers the `1/2` question of `#257` positively. -/
theorem half_mem_of_hitGapBoundedBy {K : ℕ} (h : HitGapBoundedBy K) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_of_remainderReachesHalfPointCofinally
    (remainderReachesHalfPointCofinally_of_hitGapBoundedBy h)

/-! ## 2. Kernel-computable transfer

`seamWeightsFrom` is defined by well-founded recursion, so
`seamIntegerGreedyRemainder` does not reduce in the kernel.  `Bit/R3.rem` is the
same number by structural recursion; everything computational below goes through
it. -/

theorem hitAt_of_rem {s : ℕ} (h : BitR3.rem s ≤ 2 ^ s) : HitAt s := by
  show seamIntegerGreedyRemainder s ≤ 2 ^ s
  rw [← BitR3.rem_eq]; exact h

theorem not_hitAt_of_rem {s : ℕ} (h : ¬ (BitR3.rem s ≤ 2 ^ s)) : ¬ HitAt s := by
  intro hh
  exact h (by rw [BitR3.rem_eq]; exact hh)

theorem obeysRemainderCeiling_of_rem {s : ℕ}
    (h : 3 * BitR3.rem s < 7 * 2 ^ s + 4) : ObeysRemainderCeiling s := by
  show 3 * seamIntegerGreedyRemainder s < 7 * 2 ^ s + 4
  rw [← BitR3.rem_eq]; exact h

theorem pinEscape_of_rem {s : ℕ}
    (h : ¬ (2 ^ s < BitR3.rem s ∧ BitR3.rem s < 2 ^ s + 2 * s)) :
    ¬ (2 ^ s < seamIntegerGreedyRemainder s ∧
        seamIntegerGreedyRemainder s < 2 ^ s + 2 * s) := by
  rw [← BitR3.rem_eq]; exact h

/-! ## 3. The record gap of `[3, 2000]`, certified

The hit set of `[3, 2000]` has maximal gap `10`, realised exactly once: `502`
and `512` are hits and the nine rows between them are not.  Hence
`HitGapBoundedBy K` is false for every `K ≤ 8`. -/

section RecordGap

set_option maxRecDepth 8000000

theorem hitAt_502 : HitAt 502 := hitAt_of_rem (by decide +kernel)

theorem not_hitAt_503 : ¬ HitAt 503 := not_hitAt_of_rem (by decide +kernel)
theorem not_hitAt_504 : ¬ HitAt 504 := not_hitAt_of_rem (by decide +kernel)
theorem not_hitAt_505 : ¬ HitAt 505 := not_hitAt_of_rem (by decide +kernel)
theorem not_hitAt_506 : ¬ HitAt 506 := not_hitAt_of_rem (by decide +kernel)
theorem not_hitAt_507 : ¬ HitAt 507 := not_hitAt_of_rem (by decide +kernel)
theorem not_hitAt_508 : ¬ HitAt 508 := not_hitAt_of_rem (by decide +kernel)
theorem not_hitAt_509 : ¬ HitAt 509 := not_hitAt_of_rem (by decide +kernel)
theorem not_hitAt_510 : ¬ HitAt 510 := not_hitAt_of_rem (by decide +kernel)
theorem not_hitAt_511 : ¬ HitAt 511 := not_hitAt_of_rem (by decide +kernel)

theorem hitAt_512 : HitAt 512 := hitAt_of_rem (by decide +kernel)

/-- **The sharp negative.**  Nine consecutive rows carry no hit, so no window
of length `8` meets the hit set everywhere.  Combined with the measurement
(maximal gap `7, 9, 9, 10, 10, 10` over `[3, S]` for
`S = 100, 200, 500, 1000, 1500, 2000`), the least admissible `K` grows with the
range: the bounded-gap route to `#257` is not available. -/
theorem not_hitGapBoundedBy_eight : ¬ HitGapBoundedBy 8 := by
  intro h
  obtain ⟨t, h1, h2, h3⟩ := h 503
  interval_cases t
  · exact not_hitAt_503 h3
  · exact not_hitAt_504 h3
  · exact not_hitAt_505 h3
  · exact not_hitAt_506 h3
  · exact not_hitAt_507 h3
  · exact not_hitAt_508 h3
  · exact not_hitAt_509 h3
  · exact not_hitAt_510 h3
  · exact not_hitAt_511 h3

end RecordGap

/-! ## 4. The ceiling propagates downward across bad rows

The half point `2 ^ s` is a repelling fixed point of the row map, so a bound on
`rem` transports *down* the rows, never up.  Across a bad row the transport is
strictly contracting: it turns the ceiling `7/3` at `s + 1` into `5/3 + o(1)` at
`s`. -/

/-- **Downward transport.**  If row `s + 1` is bad and obeys the remainder
ceiling, then so does row `s` — with room to spare. -/
theorem obeysCeiling_of_succ_of_bad {s : ℕ} (hs : 5 ≤ s)
    (hbad : ¬ LargestSkipLateAt (s + 1))
    (hceil : ObeysRemainderCeiling (s + 1)) :
    ObeysRemainderCeiling s := by
  have hR : ¬ SeamGreedyUpperOrMiddleAt s hs :=
    not_upperOrMiddle_of_not_largestSkipLateAt_succ hs hbad
  have hrec := rightBranch_remainder_succ_eq hs hR
  have hpulse := seamAdjacentCut_belowPulse_le hs
  have hp2 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hlin : s < 2 ^ s := Nat.lt_two_pow_self
  unfold ObeysRemainderCeiling at hceil ⊢
  omega

/-- The iterate: a run of bad rows transports the ceiling from the top of the
run to its base. -/
theorem obeysCeiling_of_badRun :
    ∀ (k s : ℕ), 5 ≤ s →
      (∀ j : ℕ, j < k → ¬ LargestSkipLateAt (s + j + 1)) →
        ObeysRemainderCeiling (s + k) → ObeysRemainderCeiling s := by
  intro k
  induction k with
  | zero => intro s _ _ h; simpa using h
  | succ k ih =>
      intro s hs hbad h
      have hstep : ObeysRemainderCeiling (s + 1) := by
        refine ih (s + 1) (by omega) (fun j hj => ?_) ?_
        · rw [show s + 1 + j + 1 = s + (j + 1) + 1 from by omega]
          exact hbad (j + 1) (by omega)
        · rw [show s + 1 + k = s + (k + 1) from by omega]
          exact h
      exact obeysCeiling_of_succ_of_bad hs (hbad 0 (by omega)) hstep

/-- **Theorem B, with the ceiling hypothesis moved off its row.**  `Bit/R2`'s
`exists_largestSkipLateAt_of_surplus` needs `ObeysRemainderCeiling (3 * N + 2)`
exactly; downward transport across the bad run replaces that by *some* ceiling
row at or above `3 * N + 2`. -/
theorem exists_largestSkipLateAt_of_surplus_of_ceiling_above
    {N σ T : ℕ} (hN : 5 ≤ N)
    (hσ : seamIntegerGreedyRemainder N = 2 ^ N + σ) (hbig : 2 * N ≤ σ)
    (hT : 3 * N + 2 ≤ T) (hceil : ObeysRemainderCeiling T) :
    ∃ t : ℕ, N + 1 ≤ t ∧ LargestSkipLateAt t := by
  by_contra hcon
  have hbad : ∀ t : ℕ, N + 1 ≤ t → ¬ LargestSkipLateAt t :=
    fun t h1 hl => hcon ⟨t, h1, hl⟩
  have hbase : ObeysRemainderCeiling (3 * N + 2) := by
    refine obeysCeiling_of_badRun (T - (3 * N + 2)) (3 * N + 2) (by omega)
      (fun j _ => hbad _ (by omega)) ?_
    rw [show 3 * N + 2 + (T - (3 * N + 2)) = T from by omega]
    exact hceil
  obtain ⟨t, h1, _, hlate⟩ := exists_largestSkipLateAt_of_surplus hN hσ hbig hbase
  exact hbad t h1 hlate

/-! ## 5. The unconditional pin, from a bare cofinal ceiling -/

/-- The remainder ceiling `3 * rem t < 7 * 2 ^ t + 4` holds at arbitrarily
large rows.  Every *good* row satisfies it unconditionally
(`three_mul_remainder_lt_of_largestSkipLateAt`); this asks only that some row
above every bound does. -/
def CeilingCofinally : Prop :=
  ∀ N : ℕ, ∃ t : ℕ, N ≤ t ∧ ObeysRemainderCeiling t

/-- The remainder escapes the width-`2 * s` window just above the half point at
arbitrarily large rows. -/
def PinEscapesCofinally : Prop :=
  ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ 5 ≤ s ∧
    ¬ (2 ^ s < seamIntegerGreedyRemainder s ∧
        seamIntegerGreedyRemainder s < 2 ^ s + 2 * s)

/-- **The pin, unconditionally in the ceiling.**  If the remainder ceiling
holds cofinally and `1/2` is not achieved, then the remainder is trapped in the
window `(2 ^ s, 2 ^ s + 2 * s)` at *every* sufficiently large row — a window of
width `2 * s` inside a range of size `2 ^ s`.

`Bit/R2`'s `badRun_pins_remainder` gives the same conclusion at a base row `N`
from the ceiling at the paired row `3 * N + 2` together with badness of the
whole block `[N + 1, 3 * N + 2]`; here neither the pairing nor the block
hypothesis is needed. -/
theorem pinned_of_ceilingCofinally_of_not_half_mem
    (hceil : CeilingCofinally) (hnot : (1 / 2 : ℝ) ∉ mersenneAchievementSet) :
    ∃ M : ℕ, ∀ s : ℕ, M ≤ s →
      2 ^ s < seamIntegerGreedyRemainder s ∧
        seamIntegerGreedyRemainder s < 2 ^ s + 2 * s := by
  obtain ⟨N₀, hforced⟩ := BitR1.not_half_mem_iff_exists_forcedRun.mp hnot
  refine ⟨max N₀ 5, fun s hs => ?_⟩
  have hlow : 2 ^ s < seamIntegerGreedyRemainder s := by
    by_contra hle
    obtain ⟨t, h1, h2, hlate⟩ :=
      exists_largestSkipLateAt_of_remainder_le_two_pow (N := s) (by omega) (by omega)
    exact hforced t (by omega) hlate
  refine ⟨hlow, ?_⟩
  by_contra hhigh
  obtain ⟨T, hT, hTc⟩ := hceil (3 * s + 2)
  obtain ⟨t, h1, hlate⟩ :=
    exists_largestSkipLateAt_of_surplus_of_ceiling_above
      (N := s) (σ := seamIntegerGreedyRemainder s - 2 ^ s)
      (by omega) (by omega) (by omega) hT hTc
  exact hforced t (by omega) hlate

/-- **The endpoint, with the two cofinality hypotheses decoupled.**  Weaker
than `Bit/R2`'s `RemainderMissesHalfPointWindowCofinally`, which demands
the ceiling at `3 * s + 2` and the window escape at `s` for the *same* `s`. -/
theorem half_mem_of_ceilingCofinally_of_pinEscapes
    (h1 : CeilingCofinally) (h2 : PinEscapesCofinally) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  by_contra hnot
  obtain ⟨M, hpin⟩ := pinned_of_ceilingCofinally_of_not_half_mem h1 hnot
  obtain ⟨s, hs1, _, hs3⟩ := h2 M
  exact hs3 (hpin s hs1)

/-! ### The comparison with `Bit/R2`'s paired condition, formally

`RemainderMissesHalfPointWindowCofinally` implies both of the hypotheses above,
so `half_mem_of_ceilingCofinally_of_pinEscapes` subsumes
`half_mem_of_remainderMissesHalfPointWindowCofinally`.  The converse fails to be
derivable in general: the pair `(CeilingCofinally, PinEscapesCofinally)` places
no constraint tying a ceiling row to an escape row, whereas the paired condition
demands `t = 3 * s + 2` exactly. -/

theorem ceilingCofinally_of_missesWindow
    (h : RemainderMissesHalfPointWindowCofinally) : CeilingCofinally := by
  intro N
  obtain ⟨s, hs1, _, hceil, _⟩ := h N
  exact ⟨3 * s + 2, by omega, hceil⟩

theorem pinEscapesCofinally_of_missesWindow
    (h : RemainderMissesHalfPointWindowCofinally) : PinEscapesCofinally := by
  intro N
  obtain ⟨s, hs1, hs2, _, hmiss⟩ := h N
  exact ⟨s, hs1, hs2, hmiss⟩

/-! ## 6. Non-vacuity: every hypothesis realised, in the kernel -/

namespace Witness

set_option maxRecDepth 8000000

/-! ### The hit set is non-trivial in both directions

`hitAt_502`, `hitAt_512` above are hits at large rows; `not_hitAt_503 … 511` are
non-hits.  Both directions occur at arbitrarily large rows in the measurement. -/

theorem hitAt_100 : HitAt 100 := hitAt_of_rem (by decide +kernel)
theorem hitAt_1200 : HitAt 1200 := hitAt_of_rem (by decide +kernel)
theorem not_hitAt_1201 : ¬ HitAt 1201 := not_hitAt_of_rem (by decide +kernel)

/-! ### `obeysCeiling_of_succ_of_bad`: both hypotheses hold at `s = 11`

Row `12` is bad (`Bit/R2.not_largestSkipLateAt_twelve`) and obeys the ceiling
(`rem 12 = 5836`, `3 * 5836 = 17508 < 7 * 4096 + 4 = 28676`), so the downward
transport fires and delivers the ceiling at row `11`. -/

theorem obeysCeiling_12 : ObeysRemainderCeiling 12 :=
  obeysRemainderCeiling_of_rem (by decide +kernel)

theorem obeysCeiling_11 : ObeysRemainderCeiling 11 :=
  obeysCeiling_of_succ_of_bad (s := 11) (by norm_num)
    not_largestSkipLateAt_twelve obeysCeiling_12

/-- The transported bound is not the trivial one: `rem 11 = 2485` is a genuine
value strictly inside the ceiling, and row `11` is itself bad, so
`three_mul_remainder_lt_of_largestSkipLateAt` does *not* apply to it. -/
theorem obeysCeiling_11_not_from_goodRow : ¬ LargestSkipLateAt 11 :=
  not_largestSkipLateAt_eleven

/-! ### `obeysCeiling_of_badRun`: a genuine two-row run

Rows `12` and `13` are both bad, so the run `[12, 13]` transports the ceiling
from row `13` down to row `11`. -/

theorem obeysCeiling_13 : ObeysRemainderCeiling 13 :=
  obeysRemainderCeiling_of_rem (by decide +kernel)

theorem obeysCeiling_11_via_run : ObeysRemainderCeiling 11 := by
  refine obeysCeiling_of_badRun 2 11 (by norm_num) (fun j hj => ?_) obeysCeiling_13
  interval_cases j
  · exact not_largestSkipLateAt_twelve
  · exact not_largestSkipLateAt_thirteen

/-! ### `exists_largestSkipLateAt_of_surplus_of_ceiling_above`: all four
hypotheses hold at `N = 9`

`rem 9 = 541 = 2 ^ 9 + 29` with `29 ≥ 2 * 9 = 18`, and row `3 * 9 + 2 = 29`
obeys the ceiling.  The theorem then produces a late largest false rank strictly
above row `9`. -/

theorem obeysCeiling_29 : ObeysRemainderCeiling 29 :=
  obeysRemainderCeiling_of_rem (by decide +kernel)

theorem surplus_nine : seamIntegerGreedyRemainder 9 = 2 ^ 9 + 29 := by
  rw [remainder_nine]; norm_num

theorem exists_late_above_nine : ∃ t : ℕ, 9 + 1 ≤ t ∧ LargestSkipLateAt t :=
  exists_largestSkipLateAt_of_surplus_of_ceiling_above (N := 9) (σ := 29)
    (by norm_num) surplus_nine (by norm_num) (by norm_num) obeysCeiling_29

/-- The ceiling row may be taken strictly above the paired row `3 * N + 2`;
this is exactly what `Bit/R2`'s form cannot do. -/
theorem obeysCeiling_100 : ObeysRemainderCeiling 100 :=
  obeysRemainderCeiling_of_rem (by decide +kernel)

theorem exists_late_above_nine' : ∃ t : ℕ, 9 + 1 ≤ t ∧ LargestSkipLateAt t :=
  exists_largestSkipLateAt_of_surplus_of_ceiling_above (N := 9) (σ := 29)
    (by norm_num) surplus_nine (by norm_num) (by norm_num) obeysCeiling_100

/-! ### The two open cofinality hypotheses

`CeilingCofinally` and `PinEscapesCofinally` are **not proved** here.  What is
certified is that their inner predicates hold at a spread of concrete rows,
including rows far past every previously certified block. -/

theorem obeysCeiling_502 : ObeysRemainderCeiling 502 :=
  obeysRemainderCeiling_of_rem (by decide +kernel)

theorem obeysCeiling_1200 : ObeysRemainderCeiling 1200 :=
  obeysRemainderCeiling_of_rem (by decide +kernel)

theorem pinEscape_502 :
    ¬ (2 ^ 502 < seamIntegerGreedyRemainder 502 ∧
        seamIntegerGreedyRemainder 502 < 2 ^ 502 + 2 * 502) :=
  pinEscape_of_rem (by decide +kernel)

theorem pinEscape_1200 :
    ¬ (2 ^ 1200 < seamIntegerGreedyRemainder 1200 ∧
        seamIntegerGreedyRemainder 1200 < 2 ^ 1200 + 2 * 1200) :=
  pinEscape_of_rem (by decide +kernel)

/-- The pin window is not vacuously escaped: at row `8` the remainder really
does sit inside it (`rem 8 = 265`, window `(256, 272)`), so
`PinEscapesCofinally` is a genuine condition and not a tautology. -/
theorem pin_occupied_eight :
    2 ^ 8 < seamIntegerGreedyRemainder 8 ∧
      seamIntegerGreedyRemainder 8 < 2 ^ 8 + 2 * 8 := by
  have h : seamIntegerGreedyRemainder 8 = BitR3.rem 8 := (BitR3.rem_eq 8).symm
  rw [h]
  refine ⟨by decide +kernel, by decide +kernel⟩

end Witness

end ErdosProblems.RemC3
