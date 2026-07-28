/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleB2
import Erdos249257.HalfCylinderSkippedRankLimit

/-!
# Skip D4: the cofactor skip dichotomy

Angle B2 proves a contradiction from an all-right tail, the landing equation,
and the single hypothesis

  `hcof : ∀ s, D+1 ≤ s → s < D+4 → cofRanks s ⊆ seamWordSupport (seamGreedyWord s)`.

and records the measured fact that `hcof` is *not* unconditionally true.

This file proves a logical dichotomy by turning cofinal failure of `hcof` into
a sufficient condition for the positive endpoint.  It does not resolve the
branch or Erdős #257.  The key observation is that the corpus's own
consumer of skipped ranks, `half_mem_mersenneAchievementSet_of_unboundedSkippedRanks`,
asks only for

* cofinally many rows, and
* one **false** seam bit per row whose **rank tends to infinity**.

It does *not* ask for the skipped rank to be the largest false rank, and it does
*not* ask for it to be late.  Every cofactor rank of `AngleB2.cofRanks` satisfies
`s ≤ 2 * d` (`cofRanks_two_mul_ge`), so along any cofinal family of rows the
cofactor ranks already tend to infinity.  Hence:

* `half_mem_or_eventually_cofRanks_subset` — **unconditional dichotomy.**
  Either `1/2 ∈ mersenneAchievementSet`, or `hcof` holds from some row onward.
* `half_mem_or_allRight_landingExcess_two_impossible` — **conditional
  dichotomy.**  Either `1/2 ∈ mersenneAchievementSet`, or there is an
  `S` beyond which no `D` carries a final middle cell of charge `-2` with an
  all-right tail.  This disjunction does not establish its first alternative.
  Moreover direct evaluation finds no concrete `seamExcess s = 2` for
  `s ∈ [5,102]`, so the second alternative excludes no observed class.

## The assigned angle, and its sharp negative

The angle asked for a cofactor `{5,7}` extension on the stated ground that the
ranks `(2s+1)/5`, `2(s+1)/5`, `(2s+1)/7`, `2(s+1)/7` "are all LATE (`3m > 2s`)".
**That premise is false**, and this file proves it false:
`cofactorFive_not_late`, `cofactorSeven_not_late` and friends show

  `3 * ((2*s+1)/5) ≤ 2*s`   for every `s ≥ 1`,

and indeed `(2s+1)/5 < (s+1)/2` for `s ≥ 3`, so the cofactor-`5` ranks sit
*strictly below* the cofactor-`4` rank `(s+1)/2` that B2 already identified as
outside the late zone, and the cofactor-`7` ranks sit lower still.  Cofactors
`5` and `7` therefore cannot repair the `LargestSkipLateAt` route; they move in
the wrong direction.

The extension is nevertheless carried out, because the route above does not need
lateness:

* `cof35Ratchet_finite_core` — with the four cofactor-`{3,5}` ranks and *no*
  parity rank `(s+1)/2`, all `2730` joint phases die by depth `5`.
* `cof35_half_mem_or_allRight_impossible` — the same unconditional dichotomy,
  now with a certificate that never mentions `(s+1)/2`.

The second construction gives another theorem of the same conditional shape.
Neither construction proves `1/2 ∈ mersenneAchievementSet`, and neither
supplies a realised instance of the landing equation.
-/

namespace Erdos249257

namespace SkipD4

open HalfCylinderIntegerGreedy
open Filter
open scoped BigOperators

/-! ## Sharp negative: cofactors `5` and `7` are not late

`LargestSkipLateAt s` needs a false rank `d` with `2 * s < 3 * d`.  B2 noted
that the cofactor-`4` rank `(s+1)/2` fails this.  The cofactor-`5` and
cofactor-`7` ranks fail it *worse*: they lie below `(s+1)/2`. -/

/-- The cofactor-`5` odd rank is never late — for *every* `s`, with no side
condition at all. -/
theorem cofactorFive_not_late (s : ℕ) : 3 * ((2 * s + 1) / 5) ≤ 2 * s := by
  omega

/-- The cofactor-`5` even rank is never late. -/
theorem cofactorFive_even_not_late (s : ℕ) (hs : 2 ≤ s) : 3 * (2 * (s + 1) / 5) ≤ 2 * s := by
  omega

/-- The cofactor-`7` odd rank is never late. -/
theorem cofactorSeven_not_late (s : ℕ) : 3 * ((2 * s + 1) / 7) ≤ 2 * s := by
  omega

/-- The cofactor-`7` even rank is never late. -/
theorem cofactorSeven_even_not_late (s : ℕ) (hs : 1 ≤ s) : 3 * (2 * (s + 1) / 7) ≤ 2 * s := by
  omega

/-- The cofactor-`5` odd rank lies strictly below the cofactor-`4` rank
`(s+1)/2`, which B2 already ruled out of the late zone. -/
theorem cofactorFive_lt_cofactorFour (s : ℕ) (hs : 3 ≤ s) : (2 * s + 1) / 5 < (s + 1) / 2 := by
  omega

/-- The cofactor-`7` odd rank lies strictly below the cofactor-`5` odd rank. -/
theorem cofactorSeven_lt_cofactorFive (s : ℕ) (hs : 7 ≤ s) :
    (2 * s + 1) / 7 < (2 * s + 1) / 5 := by
  omega

/-- Summary of the negative: no rank obtained from a cofactor `c ≥ 4` can be
late, because `3 * ((2*s+1)/c) ≤ 3 * (2*s+1)/4 < 2*s` once `s ≥ 4`.  Stated for
the two shapes the angle proposed, uniformly in the cofactor. -/
theorem cofactor_ge_four_not_late (s c : ℕ) (hs : 4 ≤ s) (hc : 4 ≤ c) :
    3 * ((2 * s + 1) / c) ≤ 2 * s ∧ 3 * (2 * (s + 1) / c) ≤ 2 * s := by
  have h1 : (2 * s + 1) / c ≤ (2 * s + 1) / 4 := Nat.div_le_div_left hc (by omega)
  have h2 : 2 * (s + 1) / c ≤ 2 * (s + 1) / 4 := Nat.div_le_div_left hc (by omega)
  omega

/-! ## Every cofactor rank is at least half the row

This is the only size fact the skipped-rank consumer needs. -/

/-- Each of B2's cofactor ranks satisfies `s ≤ 2 * d`. -/
theorem cofRanks_two_mul_ge {s d : ℕ} (hd : d ∈ AngleB2.cofRanks s) :
    s ≤ 2 * d := by
  rcases AngleB2.cofRanks_cases hd with rfl | rfl | rfl <;> omega

/-! ## Turning a failure of `hcof` into a skipped seam bit -/

/-- If the cofactor ranks are *not* all selected at row `s`, then the seam
greedy word has an explicit false coordinate whose rank is at least `s / 2`. -/
theorem exists_skipped_bit_of_not_subset {s : ℕ} (hs : 61 ≤ s)
    (hns : ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) :
    ∃ i : Fin (s - 2), seamGreedyWord s i = false ∧ s ≤ 2 * ((i : ℕ) + 2) := by
  classical
  rw [Finset.not_subset] at hns
  obtain ⟨d, hd, hdns⟩ := hns
  have hlt : d < s := AngleB2.cofRanks_lt s hs hd
  have hge : 27 ≤ d := AngleB2.cofRanks_ge s hs hd
  have hhalf : s ≤ 2 * d := cofRanks_two_mul_ge hd
  refine ⟨⟨d - 2, by omega⟩, ?_, show s ≤ 2 * ((d - 2) + 2) by omega⟩
  by_contra hb
  have htrue : seamGreedyWord s ⟨d - 2, by omega⟩ = true := by
    cases h : seamGreedyWord s ⟨d - 2, by omega⟩ with
    | false => exact absurd h hb
    | true => rfl
  exact hdns (mem_seamWordSupport_iff.mpr
    ⟨⟨d - 2, by omega⟩, htrue, show d = (d - 2) + 2 by omega⟩)

/-! ## Cofinal cofactor skips give the half membership -/

/-- **The positive branch.**  If the cofactor ranks fail to be selected at
cofinally many rows, then `1/2` is in the Mersenne achievement set.

No lateness and no maximality is used: the corpus consumer
`half_mem_mersenneAchievementSet_of_unboundedSkippedRanks` needs only that the
skipped ranks are unbounded, and `cofRanks_two_mul_ge` supplies that. -/
theorem half_mem_of_cofinal_cofSkip
    (hskip : ∀ S : ℕ, ∃ s : ℕ, S ≤ s ∧
      ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  have hchoice : ∀ j : ℕ, ∃ s : ℕ, 61 + j ≤ s ∧
      ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := fun j => hskip (61 + j)
  choose rows hrowsBig hrowsSkip using hchoice
  have hidx : ∀ j : ℕ, ∃ i : Fin (rows j - 2),
      seamGreedyWord (rows j) i = false ∧ rows j ≤ 2 * ((i : ℕ) + 2) := by
    intro j
    exact exists_skipped_bit_of_not_subset (by have := hrowsBig j; omega) (hrowsSkip j)
  choose skip hskipFalse hskipBig using hidx
  refine half_mem_mersenneAchievementSet_of_unboundedSkippedRanks rows
    ⟨skip, ?_, ?_, hskipFalse⟩
  · refine tendsto_atTop.2 fun B => ?_
    filter_upwards [eventually_ge_atTop B] with j hj
    have := hrowsBig j
    omega
  · refine tendsto_atTop.2 fun B => ?_
    filter_upwards [eventually_ge_atTop (2 * B)] with j hj
    have h1 := hrowsBig j
    have h2 := hskipBig j
    omega

/-! ## The dichotomy -/

/-- **The unconditional cofactor skip dichotomy.**  Either `1/2` lies in the
Mersenne achievement set, or B2's hypothesis `hcof` holds at every sufficiently
large row. -/
theorem half_mem_or_eventually_cofRanks_subset :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S : ℕ, ∀ s : ℕ, S ≤ s → AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  classical
  by_cases h : ∀ S : ℕ, ∃ s : ℕ, S ≤ s ∧
      ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)
  · exact Or.inl (half_mem_of_cofinal_cofSkip h)
  · right
    obtain ⟨S, hS⟩ := not_forall.mp h
    refine ⟨S, fun s hs => ?_⟩
    by_contra hc
    exact hS ⟨s, hs, hc⟩

/-- **A dichotomy for the hypothetical all-right-tail configuration.**  Either
`1/2` is in the Mersenne achievement set, or there is a threshold `S` beyond
which no `D` carries a hypothetical final middle cell of charge `-2` with an
all-right tail.  This does not decide which alternative holds and therefore
does not resolve Erdős #257. -/
theorem half_mem_or_allRight_landingExcess_two_impossible :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S : ℕ, 60 ≤ S ∧ ∀ D : ℕ, S ≤ D →
        (∀ s : ℕ, D + 1 ≤ s →
          seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) →
        Recon257.seamExcess (D + 1) = 2 → False := by
  rcases half_mem_or_eventually_cofRanks_subset with h | ⟨S, hS⟩
  · exact Or.inl h
  · refine Or.inr ⟨max 60 S, le_max_left _ _, ?_⟩
    intro D hD hright hlanding
    have h60 : 60 ≤ D := le_trans (le_max_left 60 S) hD
    have hSD : S ≤ D := le_trans (le_max_right 60 S) hD
    exact AngleB2.allRight_landingExcess_two_impossible D h60 hright hlanding
      (fun s hs _ => hS s (by omega))

/-- The same resolution in the shape of `AngleB2.finalMiddleCell_neg_two_impossible`:
the middle-cell hypotheses themselves are contradictory beyond `S`. -/
theorem half_mem_or_finalMiddleCell_neg_two_impossible :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S : ℕ, ∀ D : ℕ, (hD : 60 ≤ D) → S ≤ D →
        ¬ (seamAdjacentCut D (by omega : 5 ≤ D)).successorCarries →
        (4 * (seamAdjacentCut D (by omega : 5 ≤ D)).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse <
          (seamAdjacentCut D (by omega : 5 ≤ D)).terminalWeight) →
        (∀ s : ℕ, D + 1 ≤ s →
          seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) →
        (4 * ((seamAdjacentCut D (by omega : 5 ≤ D)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse : ℤ) - 4 = -2) →
        False := by
  rcases half_mem_or_eventually_cofRanks_subset with h | ⟨S, hS⟩
  · exact Or.inl h
  · refine Or.inr ⟨S, ?_⟩
    intro D h60 hSD hncarry hmiddle hright hcell
    exact AngleB2.finalMiddleCell_neg_two_impossible D h60 hncarry hmiddle hright hcell
      (fun s hs _ => hS s (by omega))

/-! ## The assigned extension: cofactors `{3, 5}`, no parity rank

B2's `cofRanks` uses the cofactor-`4` rank `(s+1)/2`, which is not late.  This
section removes it and replaces it by the cofactor-`5` ranks, which are not late
either — that is the negative above — but which do carry pulse.  The point of
the exercise is that the ratchet still terminates: `cof35Ratchet_finite_core`
kills all `2730` phases by depth `5` using only genuine large divisors of
`2s+1` and `2s+2` with cofactor in `{3, 5}`.

Cofactor `7` is deliberately omitted: the numbers show it adds nothing once `5`
is present (`{3,5}` and `{3,5,7}` both reach `0` at depth `5`, and both still
have `140` classes alive at depth `3`). -/

/-- The cofactor-`3` rank at row `s`: `(2s+1)/3` when `3 ∣ 2s+1`, and
`2(s+1)/3` when `3 ∣ s+1`. -/
def cof3Rank (s : ℕ) : Finset ℕ :=
  if s % 3 = 1 then {(2 * s + 1) / 3}
  else if s % 3 = 2 then {2 * (s + 1) / 3}
  else ∅

/-- The cofactor-`5` rank at row `s`: `(2s+1)/5` when `5 ∣ 2s+1`, and
`2(s+1)/5` when `5 ∣ s+1`. -/
def cof5Rank (s : ℕ) : Finset ℕ :=
  if s % 5 = 2 then {(2 * s + 1) / 5}
  else if s % 5 = 4 then {2 * (s + 1) / 5}
  else ∅

/-- The cofactor-`{3,5}` rank set.  No parity rank `(s+1)/2`. -/
def cof35Ranks (s : ℕ) : Finset ℕ := cof3Rank s ∪ cof5Rank s

def cof3Floor (s : ℕ) : ℕ := if s % 3 = 1 then 2 else if s % 3 = 2 then 1 else 0

def cof5Floor (s : ℕ) : ℕ := if s % 5 = 2 then 2 else if s % 5 = 4 then 1 else 0

def cof35Floor (s : ℕ) : ℕ := cof3Floor s + cof5Floor s

/-! ### Location of the two rank families -/

theorem cof3Rank_lower {s d : ℕ} (hd : d ∈ cof3Rank s) : 2 * s ≤ 3 * d := by
  unfold cof3Rank at hd
  split_ifs at hd with h1 h2 <;>
    simp only [Finset.mem_singleton, Finset.notMem_empty] at hd <;> omega

theorem cof3Rank_upper {s d : ℕ} (hd : d ∈ cof3Rank s) : 3 * d ≤ 2 * s + 2 := by
  unfold cof3Rank at hd
  split_ifs at hd with h1 h2 <;>
    simp only [Finset.mem_singleton, Finset.notMem_empty] at hd <;> omega

theorem cof5Rank_lower {s d : ℕ} (hd : d ∈ cof5Rank s) : 2 * s ≤ 5 * d + 2 := by
  unfold cof5Rank at hd
  split_ifs at hd with h1 h2 <;>
    simp only [Finset.mem_singleton, Finset.notMem_empty] at hd <;> omega

theorem cof5Rank_upper {s d : ℕ} (hd : d ∈ cof5Rank s) : 5 * d ≤ 2 * s + 2 := by
  unfold cof5Rank at hd
  split_ifs at hd with h1 h2 <;>
    simp only [Finset.mem_singleton, Finset.notMem_empty] at hd <;> omega

theorem cof3Rank_disjoint_cof5Rank (s : ℕ) (hs : 2 ≤ s) :
    Disjoint (cof3Rank s) (cof5Rank s) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have h1 := cof3Rank_lower ha
  have h2 := cof5Rank_upper hb
  omega

/-- Every cofactor-`{3,5}` rank is at least `27`, hence disjoint from the eight
forced ranks. -/
theorem cof35Ranks_ge (s : ℕ) (hs : 70 ≤ s) {d : ℕ} (hd : d ∈ cof35Ranks s) : 27 ≤ d := by
  rw [cof35Ranks, Finset.mem_union] at hd
  rcases hd with h | h
  · have := cof3Rank_lower h; omega
  · have := cof5Rank_lower h; omega

theorem cof35Ranks_lt (s : ℕ) (hs : 70 ≤ s) {d : ℕ} (hd : d ∈ cof35Ranks s) : d < s := by
  rw [cof35Ranks, Finset.mem_union] at hd
  rcases hd with h | h
  · have := cof3Rank_upper h; omega
  · have := cof5Rank_upper h; omega

/-- The size fact the skipped-rank consumer needs: cofactor-`{3,5}` ranks are at
least a third of the row. -/
theorem cof35Ranks_three_mul_ge (s : ℕ) (hs : 6 ≤ s) {d : ℕ} (hd : d ∈ cof35Ranks s) :
    s ≤ 3 * d := by
  rw [cof35Ranks, Finset.mem_union] at hd
  rcases hd with h | h
  · have := cof3Rank_lower h; omega
  · have := cof5Rank_lower h; omega

theorem cof35Ranks_disjoint (s : ℕ) (hs : 70 ≤ s) :
    Disjoint ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) (cof35Ranks s) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have h27 := cof35Ranks_ge s hs hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-! ### The certified pulse of the two rank families -/

theorem cof3Floor_le_pulse (s : ℕ) : cof3Floor s ≤ ∑ d ∈ cof3Rank s, rowPulse s d := by
  have h3 : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases h3 with h | h | h
  · simp only [cof3Floor, cof3Rank, h]; norm_num
  · obtain ⟨q, rfl⟩ : ∃ q, s = 3 * q + 1 := ⟨s / 3, by omega⟩
    have e1 : (2 * (3 * q + 1) + 1) / 3 = 2 * q + 1 := by omega
    have hset : cof3Rank (3 * q + 1) = {2 * q + 1} := by
      unfold cof3Rank; rw [if_pos h, e1]
    have r1 : 2 ≤ rowPulse (3 * q + 1) (2 * q + 1) := by
      have hdv : (2 * q + 1) ∣ 2 * (3 * q + 1) + 1 := ⟨3, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold cof3Floor
    rw [if_pos h]
    omega
  · obtain ⟨q, rfl⟩ : ∃ q, s = 3 * q + 2 := ⟨s / 3, by omega⟩
    have e1 : 2 * (3 * q + 2 + 1) / 3 = 2 * q + 2 := by omega
    have hset : cof3Rank (3 * q + 2) = {2 * q + 2} := by
      unfold cof3Rank; rw [if_neg (by omega), if_pos h, e1]
    have r1 : 1 ≤ rowPulse (3 * q + 2) (2 * q + 2) := by
      have hdv : (2 * q + 2) ∣ 2 * (3 * q + 2) + 2 := ⟨3, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold cof3Floor
    rw [if_neg (by omega), if_pos h]
    omega

theorem cof5Floor_le_pulse (s : ℕ) : cof5Floor s ≤ ∑ d ∈ cof5Rank s, rowPulse s d := by
  have h5 : s % 5 = 0 ∨ s % 5 = 1 ∨ s % 5 = 2 ∨ s % 5 = 3 ∨ s % 5 = 4 := by omega
  rcases h5 with h | h | h | h | h
  · simp only [cof5Floor, cof5Rank, h]; norm_num
  · simp only [cof5Floor, cof5Rank, h]; norm_num
  · obtain ⟨q, rfl⟩ : ∃ q, s = 5 * q + 2 := ⟨s / 5, by omega⟩
    have e1 : (2 * (5 * q + 2) + 1) / 5 = 2 * q + 1 := by omega
    have hset : cof5Rank (5 * q + 2) = {2 * q + 1} := by
      unfold cof5Rank; rw [if_pos h, e1]
    have r1 : 2 ≤ rowPulse (5 * q + 2) (2 * q + 1) := by
      have hdv : (2 * q + 1) ∣ 2 * (5 * q + 2) + 1 := ⟨5, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold cof5Floor
    rw [if_pos h]
    omega
  · simp only [cof5Floor, cof5Rank, h]; norm_num
  · obtain ⟨q, rfl⟩ : ∃ q, s = 5 * q + 4 := ⟨s / 5, by omega⟩
    have e1 : 2 * (5 * q + 4 + 1) / 5 = 2 * q + 2 := by omega
    have hset : cof5Rank (5 * q + 4) = {2 * q + 2} := by
      unfold cof5Rank; rw [if_neg (by omega), if_pos h, e1]
    have r1 : 1 ≤ rowPulse (5 * q + 4) (2 * q + 2) := by
      have hdv : (2 * q + 2) ∣ 2 * (5 * q + 4) + 2 := ⟨5, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold cof5Floor
    rw [if_neg (by omega), if_pos h]
    omega

theorem cof35Floor_le_pulse (s : ℕ) (hs : 2 ≤ s) :
    cof35Floor s ≤ ∑ d ∈ cof35Ranks s, rowPulse s d := by
  rw [cof35Ranks, Finset.sum_union (cof3Rank_disjoint_cof5Rank s hs)]
  have h3 := cof3Floor_le_pulse s
  have h5 := cof5Floor_le_pulse s
  unfold cof35Floor
  omega

/-! ### The certified floor and its ratchet -/

def totalFloor35 (s : ℕ) : ℕ := Recon257.pulseFloor s + cof35Floor s

theorem one_le_totalFloor35 (s : ℕ) : 1 ≤ totalFloor35 s := by
  have := Recon257.one_le_pulseFloor s
  unfold totalFloor35
  omega

theorem totalFloor35_add_period (s : ℕ) : totalFloor35 (s + 2730) = totalFloor35 s := by
  unfold totalFloor35 cof35Floor cof3Floor cof5Floor
  rw [Recon257.pulseFloor_add_period, show (s + 2730) % 3 = s % 3 by omega,
    show (s + 2730) % 5 = s % 5 by omega]

theorem totalFloor35_le_belowPulse (s : ℕ) (hs : 70 ≤ s)
    (hcof : cof35Ranks s ⊆ seamWordSupport (seamGreedyWord s)) :
    totalFloor35 s ≤ (seamAdjacentCut s (by omega : 5 ≤ s)).belowPulse := by
  classical
  have h236 := two_three_six_mem_seamGreedySupport s (by omega)
  have h7 := seven_mem_seamGreedySupport s (by omega)
  have h14 := fourteen_mem_seamGreedySupport s (by omega)
  have h20 := twenty_mem_seamGreedySupport s (by omega)
  have h21 := twentyOne_mem_seamGreedySupport s (by omega)
  have h26 := twentySix_mem_seamGreedySupport s (by omega)
  have hsmall : ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ⊆
      seamWordSupport (seamGreedyWord s) := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h236.1
    · exact h236.2.1
    · exact h236.2.2
    · exact h7
    · exact h14
    · exact h20
    · exact h21
    · exact h26
  have hsub : (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cof35Ranks s) ⊆
      seamWordSupport (seamGreedyWord s) := Finset.union_subset hsmall hcof
  have hsum :
      ∑ d ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cof35Ranks s), rowPulse s d ≤
        ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  have hsplit :
      ∑ d ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cof35Ranks s), rowPulse s d =
        (∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d) +
          ∑ d ∈ cof35Ranks s, rowPulse s d :=
    Finset.sum_union (cof35Ranks_disjoint s hs)
  have hexp : ∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d =
      Recon257.pulseFloor s := by
    rw [Recon257.pulseFloor_eq_rowPulseSum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hcofp := cof35Floor_le_pulse s (by omega)
  change totalFloor35 s ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  unfold totalFloor35
  rw [hsplit, hexp] at hsum
  omega

def cof35Step (s b : ℕ) : ℕ :=
  if 3 * totalFloor35 s + 4 ≤ 4 * b then 4 * b - (3 * totalFloor35 s + 3) else 0

def cof35Run (D : ℕ) : ℕ → ℕ
  | 0 => 3
  | k + 1 => cof35Step (D + 1 + k) (cof35Run D k)

@[simp] theorem cof35Run_zero (D : ℕ) : cof35Run D 0 = 3 := rfl

theorem cof35Run_succ (D k : ℕ) :
    cof35Run D (k + 1) = cof35Step (D + 1 + k) (cof35Run D k) := rfl

theorem cof35Run_add_period (D k : ℕ) : cof35Run (D + 2730) k = cof35Run D k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [cof35Run_succ, cof35Run_succ, ih]
      unfold cof35Step
      rw [show D + 2730 + 1 + k = (D + 1 + k) + 2730 by ring, totalFloor35_add_period]

theorem cof35Run_add_mul_period (D k n : ℕ) : cof35Run (D + 2730 * n) k = cof35Run D k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show D + 2730 * (n + 1) = (D + 2730 * n) + 2730 by ring, cof35Run_add_period, ih]

theorem cof35Run_mod (D k : ℕ) : cof35Run D k = cof35Run (D % 2730) k := by
  conv_lhs => rw [show D = D % 2730 + 2730 * (D / 2730) by
    rw [Nat.add_comm]; exact (Nat.div_add_mod D 2730).symm]
  exact cof35Run_add_mul_period _ _ _

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/-- **The `{3,5}` ratchet also empties the survivor set.**  With the parity rank
`(s+1)/2` removed and the cofactor-`5` ranks put in its place, every one of the
`2730` joint phases is dead by depth `5`.  (Depth `3` is not enough: `140`
classes are still alive there, and adding cofactor `7` does not change that.) -/
theorem cof35Ratchet_finite_core : ∀ D < 2730, cof35Run D 5 = 0 := by
  decide +kernel

theorem cof35Ratchet_run_eq_zero (D : ℕ) : cof35Run D 5 = 0 := by
  rw [cof35Run_mod]
  exact cof35Ratchet_finite_core _ (Nat.mod_lt _ (by norm_num))

theorem cof35Step_zero (s : ℕ) : cof35Step s 0 = 0 := by
  unfold cof35Step
  rw [if_neg (by have := one_le_totalFloor35 s; omega)]

/-! ### Soundness of the `{3,5}` ratchet -/

theorem cof35Run_bound
    (D : ℕ) (hD : 70 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (hcof : ∀ s : ℕ, D + 1 ≤ s → s < D + 6 →
      cof35Ranks s ⊆ seamWordSupport (seamGreedyWord s)) :
    ∀ k, k ≤ 5 → 3 * Recon257.seamExcess (D + 1 + k) - 3 ≤ (cof35Run D k : ℤ) := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  intro k
  induction k with
  | zero =>
      intro _
      simp only [Nat.add_zero, cof35Run_zero, hlanding]
      norm_num
  | succ k ih =>
      intro hk
      have ihk := ih (by omega)
      have hs : D + 1 ≤ D + 1 + k := by omega
      have hstep := (horbit (D + 1 + k) hs).2
      have hrec : Recon257.seamExcess (D + 1 + (k + 1)) =
          4 * Recon257.seamExcess (D + 1 + k) -
            ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) - 4 := by
        simpa [Recon257.seamExcess, show D + 1 + (k + 1) = (D + 1 + k) + 1 by ring] using hstep
      have hfloor : (totalFloor35 (D + 1 + k) : ℤ) ≤
          ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) := by
        exact_mod_cast totalFloor35_le_belowPulse (D + 1 + k) (by omega)
          (hcof (D + 1 + k) (by omega) (by omega))
      have hmain : 3 * Recon257.seamExcess (D + 1 + (k + 1)) - 3 ≤
          4 * (cof35Run D k : ℤ) - (3 * (totalFloor35 (D + 1 + k) : ℤ) + 3) := by
        rw [hrec]; omega
      rw [cof35Run_succ]
      unfold cof35Step
      split_ifs with hcond
      · have hle : 3 * totalFloor35 (D + 1 + k) + 3 ≤ 4 * cof35Run D k := by omega
        have hcast :
            ((4 * cof35Run D k - (3 * totalFloor35 (D + 1 + k) + 3) : ℕ) : ℤ) =
              4 * (cof35Run D k : ℤ) - (3 * (totalFloor35 (D + 1 + k) : ℤ) + 3) := by
          push_cast [Nat.cast_sub hle]
          ring
        rw [hcast]
        exact hmain
      · have hcondZ : 4 * (cof35Run D k : ℤ) ≤ 3 * (totalFloor35 (D + 1 + k) : ℤ) + 3 := by
          have hnat : 4 * cof35Run D k ≤ 3 * totalFloor35 (D + 1 + k) + 3 := by omega
          exact_mod_cast hnat
        simp only [Nat.cast_zero]
        omega

/-- **PROVED CONDITIONAL.**  The `{3,5}` auxiliary ratchet gives a
contradiction from `hright`, `hlanding`, and the stated finite support
hypothesis, without using the parity rank.  Direct evaluation finds no
`hlanding` instance in `s ∈ [5,102]`, so this theorem excludes no audited
class. -/
theorem cof35_allRight_landingExcess_two_impossible
    (D : ℕ) (hD : 70 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (hcof : ∀ s : ℕ, D + 1 ≤ s → s < D + 6 →
      cof35Ranks s ⊆ seamWordSupport (seamGreedyWord s)) :
    False := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  have hbound := cof35Run_bound D hD hright hlanding hcof 5 le_rfl
  rw [cof35Ratchet_run_eq_zero D] at hbound
  have hpos : 0 < Recon257.seamExcess (D + 1 + 5) := by
    have := (horbit (D + 1 + 5) (by omega)).1
    simpa [Recon257.seamExcess] using this
  have hone : Recon257.seamExcess (D + 1 + 5) = 1 := by
    simp only [Nat.cast_zero] at hbound
    omega
  have hstep := (horbit (D + 1 + 5) (by omega)).2
  have hrec : Recon257.seamExcess (D + 1 + 5 + 1) =
      4 * Recon257.seamExcess (D + 1 + 5) -
        ((seamAdjacentCut (D + 1 + 5) (by omega : 5 ≤ D + 1 + 5)).belowPulse : ℤ) - 4 := by
    simpa [Recon257.seamExcess] using hstep
  have hnext : 0 < Recon257.seamExcess (D + 1 + 5 + 1) := by
    have := (horbit (D + 1 + 5 + 1) (by omega)).1
    simpa [Recon257.seamExcess] using this
  have hfloor : (Recon257.pulseFloor (D + 1 + 5) : ℤ) ≤
      ((seamAdjacentCut (D + 1 + 5) (by omega : 5 ≤ D + 1 + 5)).belowPulse : ℤ) := by
    exact_mod_cast Recon257.pulseFloor_le_belowPulse (D + 1 + 5) (by omega)
  have hone' : (1 : ℤ) ≤ (Recon257.pulseFloor (D + 1 + 5) : ℤ) := by
    exact_mod_cast Recon257.one_le_pulseFloor (D + 1 + 5)
  rw [hone] at hrec
  omega

/-! ### The `{3,5}` dichotomy -/

theorem exists_skipped_bit_of_not_cof35_subset {s : ℕ} (hs : 70 ≤ s)
    (hns : ¬ cof35Ranks s ⊆ seamWordSupport (seamGreedyWord s)) :
    ∃ i : Fin (s - 2), seamGreedyWord s i = false ∧ s ≤ 3 * ((i : ℕ) + 2) := by
  classical
  rw [Finset.not_subset] at hns
  obtain ⟨d, hd, hdns⟩ := hns
  have hlt : d < s := cof35Ranks_lt s hs hd
  have hge : 27 ≤ d := cof35Ranks_ge s hs hd
  have hthird : s ≤ 3 * d := cof35Ranks_three_mul_ge s (by omega) hd
  refine ⟨⟨d - 2, by omega⟩, ?_, show s ≤ 3 * ((d - 2) + 2) by omega⟩
  by_contra hb
  have htrue : seamGreedyWord s ⟨d - 2, by omega⟩ = true := by
    cases h : seamGreedyWord s ⟨d - 2, by omega⟩ with
    | false => exact absurd h hb
    | true => rfl
  exact hdns (mem_seamWordSupport_iff.mpr
    ⟨⟨d - 2, by omega⟩, htrue, show d = (d - 2) + 2 by omega⟩)

theorem cof35_half_mem_of_cofinal_skip
    (hskip : ∀ S : ℕ, ∃ s : ℕ, S ≤ s ∧
      ¬ cof35Ranks s ⊆ seamWordSupport (seamGreedyWord s)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  have hchoice : ∀ j : ℕ, ∃ s : ℕ, 70 + j ≤ s ∧
      ¬ cof35Ranks s ⊆ seamWordSupport (seamGreedyWord s) := fun j => hskip (70 + j)
  choose rows hrowsBig hrowsSkip using hchoice
  have hidx : ∀ j : ℕ, ∃ i : Fin (rows j - 2),
      seamGreedyWord (rows j) i = false ∧ rows j ≤ 3 * ((i : ℕ) + 2) := by
    intro j
    exact exists_skipped_bit_of_not_cof35_subset (by have := hrowsBig j; omega) (hrowsSkip j)
  choose skip hskipFalse hskipBig using hidx
  refine half_mem_mersenneAchievementSet_of_unboundedSkippedRanks rows
    ⟨skip, ?_, ?_, hskipFalse⟩
  · refine tendsto_atTop.2 fun B => ?_
    filter_upwards [eventually_ge_atTop B] with j hj
    have := hrowsBig j
    omega
  · refine tendsto_atTop.2 fun B => ?_
    filter_upwards [eventually_ge_atTop (3 * B)] with j hj
    have h1 := hrowsBig j
    have h2 := hskipBig j
    omega

/-- **The `{3,5}` dichotomy.**  Either `1/2 ∈ mersenneAchievementSet`, or the
cofactor-`{3,5}` ranks are selected at every sufficiently large row. -/
theorem cof35_half_mem_or_eventually_subset :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S : ℕ, ∀ s : ℕ, S ≤ s → cof35Ranks s ⊆ seamWordSupport (seamGreedyWord s) := by
  classical
  by_cases h : ∀ S : ℕ, ∃ s : ℕ, S ≤ s ∧
      ¬ cof35Ranks s ⊆ seamWordSupport (seamGreedyWord s)
  · exact Or.inl (cof35_half_mem_of_cofinal_skip h)
  · right
    obtain ⟨S, hS⟩ := not_forall.mp h
    refine ⟨S, fun s hs => ?_⟩
    by_contra hc
    exact hS ⟨s, hs, hc⟩

/-- **PROVED CONDITIONAL DICHOTOMY.**  Either the half point is in the
achievement set, or sufficiently late all-right tails cannot also satisfy the
uninstantiated concrete landing equation.  This does not decide which
alternative holds. -/
theorem cof35_half_mem_or_allRight_impossible :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S : ℕ, 70 ≤ S ∧ ∀ D : ℕ, S ≤ D →
        (∀ s : ℕ, D + 1 ≤ s →
          seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) →
        Recon257.seamExcess (D + 1) = 2 → False := by
  rcases cof35_half_mem_or_eventually_subset with h | ⟨S, hS⟩
  · exact Or.inl h
  · refine Or.inr ⟨max 70 S, le_max_left _ _, ?_⟩
    intro D hD hright hlanding
    have h70 : 70 ≤ D := le_trans (le_max_left 70 S) hD
    have hSD : S ≤ D := le_trans (le_max_right 70 S) hD
    exact cof35_allRight_landingExcess_two_impossible D h70 hright hlanding
      (fun s hs _ => hS s (by omega))

-- Axiom audit (verified with `#print axioms`, then removed so that
-- `lake env lean` produces empty output):
--   half_mem_of_cofinal_cofSkip                        [propext, Classical.choice, Quot.sound]
--   half_mem_or_eventually_cofRanks_subset             [propext, Classical.choice, Quot.sound]
--   half_mem_or_allRight_landingExcess_two_impossible  [propext, Classical.choice, Quot.sound]
--   half_mem_or_finalMiddleCell_neg_two_impossible     [propext, Classical.choice, Quot.sound]
--   cof35Ratchet_finite_core                           does not depend on any axioms
--   cof35_allRight_landingExcess_two_impossible        [propext, Classical.choice, Quot.sound]
--   cof35_half_mem_or_allRight_impossible              [propext, Classical.choice, Quot.sound]
-- No `sorryAx`, no `Lean.ofReduceBool`, no `native_decide`.

end SkipD4

end Erdos249257
