/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleB2
import Erdos249257.HalfCylinderLargestSkipInduction

/-!
# Angle D5: undiscounted tail mass, and the skip dichotomy it forces

## 1.  The assigned question, answered negatively

Angle B1 observed that on an all-right tail every rank in `[D+1, s)` is selected, so
the *cardinality* of the certified support grows like `s - 1 - D`, linearly and
undiscounted.  Angle B4 measured the *pulse* of that block and found it zero until
`2 * s ≥ 3 * D`.  The D5 question is whether the cardinality bound, rather than the
pulse bound, supplies the mass the ratchet needs.

It does not, and the failure is exact rather than quantitative:

* `sum_rowPulse_eq_zero_of_above_late` — a certified block of **any** cardinality
  sitting strictly above a *late* skipped rank has row pulse exactly `0`.  Not small:
  zero.  Cardinality there is worth literally nothing.
* `tailBlock_pulse_eq_zero_of_late` — in particular the whole all-right-tail block
  `Finset.Ico (D+1) s`, whose cardinality is `s - 1 - D`, is mute at every row whose
  largest false rank is late.
* `no_floor_can_stop_escaped_budget` — and in the opposite regime cardinality is
  capped: `wordPulse_le` bounds *every* below-pulse by `2 * (s - 2)`, and once the
  budget passes `4 * s` a floor of `2 * (s - 2)` still lets it grow.  So no bound
  derived from support size, however large, can kill a class after depth
  `≈ log₄ s`.

Mass is carried by *divisibility*, not by *size*: a rank `d < s` divides `2s+1` or
`2s+2` only with cofactor `≥ 3`, so `3 * d ≤ 2 * s + 2`
(`AngleB4.rowPulse_eq_zero_of_large_rank`).  Every rank above the two-thirds line is
pulse-invisible unless its cofactor is exactly `3`.

## 2.  What that leaves: the skip dichotomy

That same two-thirds line is the line in `LargestSkipLateAt`.  Reading it as an order
statement rather than an arithmetic one gives the dichotomy this wave was looking for,
and it is *provable*.  The argument is three lines: let `d` be the largest false rank of
row `s` (or none, in which case the row is full); if `d` is beyond the line the row is
late; otherwise every rank beyond the line exceeds `d`, and every rank strictly above
the largest false rank is present by definition.

**At the two-thirds line** (`cof3_dichotomy`, unconditional for `s ≥ 5`):

  `cof3Ranks s ⊆ seamWordSupport (seamGreedyWord s)  ∨  LargestSkipLateAt s`

where `cof3Ranks s` is the set of **cofactor-three** ranks — `(2s+1)/3` when
`s ≡ 1 (mod 3)`, `2(s+1)/3` when `s ≡ 2 (mod 3)`.  This is the exact converse of the
repo's own `late_firstCrossing_boundary`, which says a late largest skip can only stop
being late at a row where it *is* a cofactor-three rank.

**At the one-half line** (`cofRanks_mid_dichotomy`, unconditional for `s ≥ 61`):

  `AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)  ∨  LargestSkipMidAt s`

where `LargestSkipMidAt s := ∃ d, IsLargestFalseRank (seamGreedyWord s) d ∧ s < 2 * d`.
Here the left disjunct is **exactly B2's hypothesis `hcof`**, half rank and all.

## 3.  Which cofactor ranks each line can deliver

* At the two-thirds line the half rank `(s+1)/2` is unreachable, and this is sharp:
  `half_rank_never_late` shows `2 * s < 3 * ((s+1)/2)` is **false** for every `s ≥ 3`.
  B2's hint to look for late cofactors `5, 7` is refuted by the same inequality — a
  rank with cofactor `c ≥ 4` satisfies `4 * m ≤ 2s + 2`, hence `3 * m ≤ 2 * s` for
  `s ≥ 4` (`only_cofactor_three_is_late`).  **`3` is the only late cofactor there is**,
  and `cofRanks_subset_insert_half` shows the half rank is the only member of
  `AngleB2.cofRanks` the two-thirds line misses.
* At the one-half line *every* cofactor rank clears the boundary (`cofRanks_mid`): the
  two cofactor-three ranks clear it by about `s/3`, and the half rank clears it by
  exactly `1`, since `2 * ((s+1)/2) = s + 1` for odd `s`.  That single unit is the whole
  difference between the two lines.

## 4.  The finite conditional disjunction

* `allRight_landingExcess_two_midSkip` — **PROVED conditionally for every
  `D ≥ 60`**, a hypothetical final
  middle cell of charge `-2` at rank `D` with an all-right tail forces
  `LargestSkipMidAt s` at one of the three explicit rows `D+1, D+2, D+3`.  No residual
  hypothesis and no residual residue class: either the cofactor ranks are selected at
  all three rows, and the auxiliary AngleB2 ratchet reaches zero in all `2730`
  phases at depth `3`, or a row carries a mid-late largest skip.  This is B2's `hcof`
  discharged into a genuine disjunction.  The landing equation has no
  concrete instance in the audited range `s ∈ [5,102]`, so this theorem
  excludes no observed class.
* `half_mem_mersenneAchievementSet_of_largestSkipMidStepSocket` — the one-half
  **step socket**, if supplied at every required row, reaches the same endpoint
  as the two-thirds one.  The three-row disjunction above does not supply that
  cofinal socket.  Nothing in
  `HalfCylinderLargestSkipInduction`'s fan-in uses the constant `3/2`:
  `SeamGreedyUnboundedSkippedRanksAlong` only needs the skipped rank to tend to
  infinity, and `s < 2 * d` forces that just as well.  The whole route — base row `14`,
  `U`/`M` reset, `R` preservation, compactness — transcribes verbatim.

## 5.  The two-thirds line on its own, quantified

For the record of what the *strictly weaker* two-thirds certificate buys, the
cofactor-three floor `pulseFloor + cof3Floor` (with `cof3Floor = ![0,2,1]` indexed by
`s % 3`) is run through B2's ratchet:

* `cof3Ratchet_finite_core` — `∀ D < 2730, D % 21 = 20 ∨ cof3Run D 6 = 0`
  (kernel-checked), i.e. `2600` of the `2730` phases die by depth `6`;
* `allRight_landingExcess_two_lateSkip` — hence if `D % 21 ≠ 20` then
  `LargestSkipLateAt s` holds at one of the six rows `s ∈ [D+1, D+6]`.

**MEASURED:** `87` of the `130` phases `D ≡ 20 (mod 21)` remain nonzero at
depth `6` of the cofactor-three auxiliary ratchet.  No theorem here says all
`87` remain nonzero at every later depth.  For phases not killed at depth `6`,
the two-thirds line yields only `allRight_landingExcess_two_lateSkip_or_halfSkip`.  The
one-half dichotomy of §2 removes that residue entirely.

-/

namespace Erdos249257

namespace D5

open HalfCylinderIntegerGreedy
open scoped BigOperators

/-! ## 1.  Cardinality is not mass -/

/-- **Undiscounted cardinality is worth exactly zero.**  A certified block of ranks of
*any* size, sitting strictly above a late skipped rank `d` and below the row index,
contributes row pulse `0`.  This is the D5 question answered: the linear growth of the
all-right-tail support carries no mass whatsoever in the late regime. -/
theorem sum_rowPulse_eq_zero_of_above_late
    {s d : ℕ} (hd2 : 2 ≤ d) (hlate : 2 * s < 3 * d) (T : Finset ℕ)
    (hT : ∀ e ∈ T, d < e ∧ e < s) :
    ∑ e ∈ T, rowPulse s e = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  obtain ⟨h1, h2⟩ := hT e he
  exact rowPulse_eq_zero_of_late_strictSuffix hd2 h1 h2 hlate

/-- The all-right-tail block of `AngleB4.tailPulse`, of cardinality `s - 1 - D`, is
mute at every row whose largest false rank is late — a second, hypothesis-independent
reason for `AngleB4.tailPulse_eq_zero_of_two_mul_le`. -/
theorem tailBlock_pulse_eq_zero_of_late
    {D s d : ℕ} (hd2 : 2 ≤ d) (hdD : d ≤ D) (hlate : 2 * s < 3 * d) :
    ∑ e ∈ Finset.Ico (D + 1) s, rowPulse s e = 0 := by
  refine sum_rowPulse_eq_zero_of_above_late hd2 hlate _ ?_
  intro e he
  have := Finset.mem_Ico.mp he
  exact ⟨by omega, this.2⟩

/-- **Cardinality is capped where it is not zero.**  `wordPulse_le` bounds every
below-pulse by `2 * (s - 2)`, i.e. by twice the *full* row cardinality.  Once the
ratchet budget exceeds `4 * s` even that maximal floor lets it grow past `4 * (s+1)`.
So no support-size argument can kill a class after depth `≈ log₄ s`. -/
theorem no_floor_can_stop_escaped_budget
    (s b F : ℕ) (hs : 6 ≤ s) (hb : 4 * s ≤ b) (hF : F ≤ 2 * (s - 2)) :
    4 * (s + 1) ≤ 4 * b - (3 * F + 3) := by
  omega

/-- The universal cap really is the true below-pulse cap. -/
theorem belowPulse_le (s : ℕ) (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) := by
  change wordPulse s (seamGreedyWord s).toNatWord ≤ 2 * (s - 2)
  exact wordPulse_le _ _

/-! ## 2.  Only cofactor three is late -/

/-- **`3` is the only late cofactor.**  A rank `m` with `c * m ≤ 2 * s + 2` for some
`c ≥ 4` — i.e. any divisor of `2s+1` or `2s+2` whose cofactor is at least four — sits
below the two-thirds line, hence is never a late rank. -/
theorem only_cofactor_three_is_late
    {s m c : ℕ} (hs : 4 ≤ s) (hc : 4 ≤ c) (hcm : c * m ≤ 2 * s + 2) :
    ¬ 2 * s < 3 * m := by
  have h4 : 4 * m ≤ c * m := Nat.mul_le_mul_right _ hc
  omega

/-- The half rank `(s+1)/2` is never late.  This refutes any attempt to obtain it from
a two-thirds-boundary largest-skip argument. -/
theorem half_rank_never_late (s : ℕ) (hs : 3 ≤ s) : ¬ 2 * s < 3 * ((s + 1) / 2) := by
  omega

/-! ## 3.  Every row has a largest false rank, or is full -/

/-- Either the row is completely filled, or it has a largest false rank. -/
theorem exists_isLargestFalseRank_or_full {s : ℕ} (b : SeamRowWord s) :
    (∀ e : ℕ, 2 ≤ e → e < s → e ∈ seamWordSupport b) ∨
      ∃ d : ℕ, IsLargestFalseRank b d := by
  classical
  by_cases h : ∀ e : ℕ, 2 ≤ e → e < s → e ∈ seamWordSupport b
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨e, he2, hes, henot⟩ := h
    set F : Finset ℕ := (Finset.Ico 2 s).filter (fun x => x ∉ seamWordSupport b) with hFdef
    have hmemF : ∀ x : ℕ, x ∈ F ↔ (2 ≤ x ∧ x < s) ∧ x ∉ seamWordSupport b := by
      intro x
      simp only [hFdef, Finset.mem_filter, Finset.mem_Ico]
    have hne : F.Nonempty := ⟨e, (hmemF e).mpr ⟨⟨he2, hes⟩, henot⟩⟩
    refine ⟨F.max' hne, ?_, ?_, ?_, ?_⟩
    · exact ((hmemF _).mp (F.max'_mem hne)).1.1
    · exact ((hmemF _).mp (F.max'_mem hne)).1.2
    · exact ((hmemF _).mp (F.max'_mem hne)).2
    · intro f hf hfs
      by_contra hfnot
      have hd2 : 2 ≤ F.max' hne := ((hmemF _).mp (F.max'_mem hne)).1.1
      have : f ∈ F := (hmemF f).mpr ⟨⟨by omega, hfs⟩, hfnot⟩
      have := F.le_max' f this
      omega

/-! ## 4.  The cofactor-three ranks and the skip dichotomy -/

/-- The **cofactor-three ranks** at row `s`: the unique divisor of `2s+1` or `2s+2`
with cofactor exactly three.  These are precisely the ranks that are simultaneously
*late* (`2 * s < 3 * m`) and *audible* (`rowPulse s m ≠ 0`). -/
def cof3Ranks (s : ℕ) : Finset ℕ :=
  if s % 3 = 1 then {(2 * s + 1) / 3}
  else if s % 3 = 2 then {2 * (s + 1) / 3}
  else ∅

theorem cof3Ranks_spec (s : ℕ) (hs : 5 ≤ s) {m : ℕ} (hm : m ∈ cof3Ranks s) :
    2 ≤ m ∧ m < s ∧ 2 * s < 3 * m := by
  unfold cof3Ranks at hm
  split_ifs at hm with h1 h2 <;>
    simp only [Finset.mem_singleton, Finset.notMem_empty] at hm
  · subst hm; omega
  · subst hm; omega

theorem cof3Ranks_ge_27 (s : ℕ) (hs : 41 ≤ s) {m : ℕ} (hm : m ∈ cof3Ranks s) : 27 ≤ m := by
  have := cof3Ranks_spec s (by omega) hm
  omega

/-- **The skip dichotomy.**  At every row, either all cofactor-three ranks are
selected by the greedy, or the row has a late largest skip.  Unconditional. -/
theorem cof3_dichotomy (s : ℕ) (hs : 5 ≤ s) :
    cof3Ranks s ⊆ seamWordSupport (seamGreedyWord s) ∨ LargestSkipLateAt s := by
  rcases exists_isLargestFalseRank_or_full (seamGreedyWord s) with hfull | ⟨d, hd⟩
  · left
    intro m hm
    obtain ⟨h2, hlt, _⟩ := cof3Ranks_spec s hs hm
    exact hfull m h2 hlt
  · by_cases hlate : 2 * s < 3 * d
    · exact Or.inr ⟨d, hd, hlate⟩
    · left
      intro m hm
      obtain ⟨h2, hlt, hmlate⟩ := cof3Ranks_spec s hs hm
      exact hd.2.2.2 m (by omega) hlt

/-- The half rank is the *only* member of `AngleB2.cofRanks` outside `cof3Ranks`. -/
theorem cofRanks_subset_insert_half (s : ℕ) :
    AngleB2.cofRanks s ⊆ insert ((s + 1) / 2) (cof3Ranks s) := by
  intro m hm
  have h6 : s % 6 = 0 ∨ s % 6 = 1 ∨ s % 6 = 2 ∨ s % 6 = 3 ∨ s % 6 = 4 ∨ s % 6 = 5 := by
    omega
  unfold AngleB2.cofRanks at hm
  unfold cof3Ranks
  simp only [Finset.mem_insert]
  rcases h6 with h | h | h | h | h | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)] at hm
    simp at hm
  · rw [if_pos h] at hm
    rw [if_pos (by omega : s % 3 = 1)]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
    tauto
  · rw [if_neg (by omega), if_pos h] at hm
    rw [if_neg (by omega), if_pos (by omega : s % 3 = 2)]
    simp only [Finset.mem_singleton] at hm ⊢
    tauto
  · rw [if_neg (by omega), if_neg (by omega), if_pos h] at hm
    simp only [Finset.mem_singleton] at hm
    tauto
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h] at hm
    rw [if_pos (by omega : s % 3 = 1)]
    simp only [Finset.mem_singleton] at hm ⊢
    tauto
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos h] at hm
    rw [if_neg (by omega), if_pos (by omega : s % 3 = 2)]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
    tauto

/-! ## 4b.  The one-half line: the dichotomy that reaches *every* cofactor rank

The two-thirds line was chosen because it is the line in `LargestSkipLateAt`.  But the
order argument of `cof3_dichotomy` works at **any** line: if the largest false rank `d`
of row `s` satisfies `2 * d ≤ s`, then every rank `m` with `s < 2 * m` and `m < s` is
present.  And *all three* of `AngleB2.cofRanks` clear the one-half line — including the
half rank `(s+1)/2`, which clears it by exactly one (`2 * ((s+1)/2) = s + 1` for odd
`s`).  So at the one-half line the dichotomy delivers B2's hypothesis `hcof` in full,
and B2's ratchet then kills **every** residue class at depth three. -/

/-- Row `s` has a largest false rank strictly beyond one half of the row.  The
one-half analogue of `LargestSkipLateAt`; strictly weaker, hence strictly easier to
produce. -/
def LargestSkipMidAt (s : ℕ) : Prop :=
  ∃ d : ℕ, IsLargestFalseRank (seamGreedyWord s) d ∧ s < 2 * d

theorem largestSkipMidAt_of_largestSkipLateAt {s : ℕ} (h : LargestSkipLateAt s) :
    LargestSkipMidAt s := by
  obtain ⟨d, hd, hlate⟩ := h
  exact ⟨d, hd, by omega⟩

/-- **Every cofactor rank clears the one-half line.**  The two cofactor-three ranks
clear it by `s/3`; the half rank clears it by exactly `1`. -/
theorem cofRanks_mid (s : ℕ) (_hs : 5 ≤ s) {d : ℕ} (hd : d ∈ AngleB2.cofRanks s) :
    s < 2 * d := by
  have h6 : s % 6 = 0 ∨ s % 6 = 1 ∨ s % 6 = 2 ∨ s % 6 = 3 ∨ s % 6 = 4 ∨ s % 6 = 5 := by
    omega
  unfold AngleB2.cofRanks at hd
  rcases h6 with h | h | h | h | h | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)] at hd
    simp at hd
  · rw [if_pos h] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> omega
  · rw [if_neg (by omega), if_pos h] at hd
    simp only [Finset.mem_singleton] at hd
    subst hd; omega
  · rw [if_neg (by omega), if_neg (by omega), if_pos h] at hd
    simp only [Finset.mem_singleton] at hd
    subst hd; omega
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h] at hd
    simp only [Finset.mem_singleton] at hd
    subst hd; omega
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos h] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> omega

/-- **The one-half skip dichotomy.**  At every row from `61` on, either *all* of
`AngleB2.cofRanks` — the two cofactor-three ranks *and* the half rank — are selected by
the greedy, or the row has a largest false rank beyond one half of the row.
Unconditional. -/
theorem cofRanks_mid_dichotomy (s : ℕ) (hs : 61 ≤ s) :
    AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) ∨ LargestSkipMidAt s := by
  rcases exists_isLargestFalseRank_or_full (seamGreedyWord s) with hfull | ⟨d, hd⟩
  · left
    intro m hm
    have h27 := AngleB2.cofRanks_ge s (by omega) hm
    exact hfull m (by omega) (AngleB2.cofRanks_lt s (by omega) hm)
  · by_cases hmid : s < 2 * d
    · exact Or.inr ⟨d, hd, hmid⟩
    · left
      intro m hm
      have h1 := cofRanks_mid s (by omega) hm
      exact hd.2.2.2 m (by omega) (AngleB2.cofRanks_lt s (by omega) hm)

/-! ## 5.  The certified cofactor-three floor -/

/-- The pulse the cofactor-three ranks are guaranteed to contribute, indexed by
`s % 3`: `![0, 2, 1]`. -/
def cof3Floor (s : ℕ) : ℕ :=
  if s % 3 = 1 then 2 else if s % 3 = 2 then 1 else 0

theorem cof3Floor_le_cof3Pulse (s : ℕ) (hs : 5 ≤ s) :
    cof3Floor s ≤ ∑ d ∈ cof3Ranks s, rowPulse s d := by
  have h3 : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases h3 with h | h | h
  · simp only [cof3Floor, cof3Ranks, h]
    norm_num
  · obtain ⟨q, rfl⟩ : ∃ q, s = 3 * q + 1 := ⟨s / 3, by omega⟩
    have e1 : (2 * (3 * q + 1) + 1) / 3 = 2 * q + 1 := by omega
    have hset : cof3Ranks (3 * q + 1) = {2 * q + 1} := by
      unfold cof3Ranks; rw [if_pos h, e1]
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
    have hset : cof3Ranks (3 * q + 2) = {2 * q + 2} := by
      unfold cof3Ranks; rw [if_neg (by omega), if_pos h, e1]
    have r1 : 1 ≤ rowPulse (3 * q + 2) (2 * q + 2) := by
      have hdv : (2 * q + 2) ∣ 2 * (3 * q + 2) + 2 := ⟨3, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold cof3Floor
    rw [if_neg (by omega), if_pos h]
    omega

/-- The certified floor of this angle: eight forced ranks plus the cofactor-three
ranks.  Strictly weaker than `AngleB2.totalFloor` — it drops the half rank. -/
def totalFloor3 (s : ℕ) : ℕ := Recon257.pulseFloor s + cof3Floor s

theorem one_le_totalFloor3 (s : ℕ) : 1 ≤ totalFloor3 s := by
  have := Recon257.one_le_pulseFloor s
  unfold totalFloor3
  omega

theorem totalFloor3_add_period (s : ℕ) : totalFloor3 (s + 2730) = totalFloor3 s := by
  unfold totalFloor3 cof3Floor
  rw [Recon257.pulseFloor_add_period, show (s + 2730) % 3 = s % 3 by omega]

theorem cof3Ranks_disjoint (s : ℕ) (hs : 41 ≤ s) :
    Disjoint ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) (cof3Ranks s) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have h27 := cof3Ranks_ge_27 s hs hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem totalFloor3_le_belowPulse (s : ℕ) (hs : 61 ≤ s)
    (hcof : cof3Ranks s ⊆ seamWordSupport (seamGreedyWord s)) :
    totalFloor3 s ≤ (seamAdjacentCut s (by omega : 5 ≤ s)).belowPulse := by
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
  have hsub : (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cof3Ranks s) ⊆
      seamWordSupport (seamGreedyWord s) := Finset.union_subset hsmall hcof
  have hsum :
      ∑ d ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cof3Ranks s), rowPulse s d ≤
        ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  have hsplit :
      ∑ d ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cof3Ranks s), rowPulse s d =
        (∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d) +
          ∑ d ∈ cof3Ranks s, rowPulse s d :=
    Finset.sum_union (cof3Ranks_disjoint s (by omega))
  have hexp : ∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d =
      Recon257.pulseFloor s := by
    rw [Recon257.pulseFloor_eq_rowPulseSum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hcofp := cof3Floor_le_cof3Pulse s (by omega)
  change totalFloor3 s ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  unfold totalFloor3
  rw [hsplit, hexp] at hsum
  omega

/-! ## 6.  The cofactor-three ratchet -/

/-- One step of the cofactor-three ratchet.  `0` is the absorbing dead state. -/
def cof3Step (s b : ℕ) : ℕ :=
  if 3 * totalFloor3 s + 4 ≤ 4 * b then 4 * b - (3 * totalFloor3 s + 3) else 0

/-- The orbit of the integer budget `3 * E - 3` from the landing rank `D + 1`. -/
def cof3Run (D : ℕ) : ℕ → ℕ
  | 0 => 3
  | k + 1 => cof3Step (D + 1 + k) (cof3Run D k)

@[simp] theorem cof3Run_zero (D : ℕ) : cof3Run D 0 = 3 := rfl

theorem cof3Run_succ (D k : ℕ) :
    cof3Run D (k + 1) = cof3Step (D + 1 + k) (cof3Run D k) := rfl

theorem cof3Run_add_period (D k : ℕ) : cof3Run (D + 2730) k = cof3Run D k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [cof3Run_succ, cof3Run_succ, ih]
      unfold cof3Step
      rw [show D + 2730 + 1 + k = (D + 1 + k) + 2730 by ring, totalFloor3_add_period]

theorem cof3Run_add_mul_period (D k n : ℕ) :
    cof3Run (D + 2730 * n) k = cof3Run D k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show D + 2730 * (n + 1) = (D + 2730 * n) + 2730 by ring, cof3Run_add_period, ih]

theorem cof3Run_mod (D k : ℕ) : cof3Run D k = cof3Run (D % 2730) k := by
  conv_lhs => rw [show D = D % 2730 + 2730 * (D / 2730) by
    rw [Nat.add_comm]; exact (Nat.div_add_mod D 2730).symm]
  exact cof3Run_add_mul_period _ _ _

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
/-- **PROVED for the auxiliary budget.**  For every phase outside
`D ≡ 20 (mod 21)`, `cof3Run D 6 = 0`; this covers `2600` of the `2730` joint
phases using no half rank.  It does not by itself empty any concrete survivor
class: the connection to the seam orbit additionally requires `hright`,
`hlanding`, and a finite support hypothesis. -/
theorem cof3Ratchet_finite_core : ∀ D < 2730, D % 21 = 20 ∨ cof3Run D 6 = 0 := by
  decide +kernel

theorem cof3Ratchet_run_eq_zero (D : ℕ) (h : D % 21 ≠ 20) : cof3Run D 6 = 0 := by
  have hdvd : (21 : ℕ) ∣ 2730 := ⟨130, by norm_num⟩
  have hmod : D % 2730 % 21 = D % 21 := Nat.mod_mod_of_dvd D hdvd
  rw [cof3Run_mod]
  rcases cof3Ratchet_finite_core _ (Nat.mod_lt _ (by norm_num : 0 < 2730)) with h1 | h1
  · rw [hmod] at h1
    exact absurd h1 h
  · exact h1

theorem cof3Step_zero (s : ℕ) : cof3Step s 0 = 0 := by
  unfold cof3Step
  rw [if_neg (by have := one_le_totalFloor3 s; omega)]

/-- The cofactor-three ratchet is dominated by B2's full cofactor ratchet: dropping
the half rank can only weaken the exclusion. -/
theorem cofRun_le_cof3Run (D k : ℕ) : AngleB2.cofRun D k ≤ cof3Run D k := by
  induction k with
  | zero => simp [AngleB2.cofRun]
  | succ k ih =>
      rw [cof3Run_succ, AngleB2.cofRun_succ]
      have hfl : totalFloor3 (D + 1 + k) ≤ AngleB2.totalFloor (D + 1 + k) := by
        unfold totalFloor3 AngleB2.totalFloor cof3Floor AngleB2.cofFloor
        split_ifs <;> omega
      unfold cof3Step AngleB2.cofStep
      split_ifs with h1 h2 h2 <;> omega

/-! ## 7.  Soundness -/

theorem cof3Run_bound
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (hcof : ∀ s : ℕ, D + 1 ≤ s → s < D + 7 →
      cof3Ranks s ⊆ seamWordSupport (seamGreedyWord s)) :
    ∀ k, k ≤ 6 → 3 * Recon257.seamExcess (D + 1 + k) - 3 ≤ (cof3Run D k : ℤ) := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  intro k
  induction k with
  | zero =>
      intro _
      simp only [Nat.add_zero, cof3Run_zero, hlanding]
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
      have hfloor : (totalFloor3 (D + 1 + k) : ℤ) ≤
          ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) := by
        exact_mod_cast totalFloor3_le_belowPulse (D + 1 + k) (by omega)
          (hcof (D + 1 + k) (by omega) (by omega))
      have hmain : 3 * Recon257.seamExcess (D + 1 + (k + 1)) - 3 ≤
          4 * (cof3Run D k : ℤ) - (3 * (totalFloor3 (D + 1 + k) : ℤ) + 3) := by
        rw [hrec]; omega
      rw [cof3Run_succ]
      unfold cof3Step
      split_ifs with hcond
      · have hle : 3 * totalFloor3 (D + 1 + k) + 3 ≤ 4 * cof3Run D k := by omega
        have hcast :
            ((4 * cof3Run D k - (3 * totalFloor3 (D + 1 + k) + 3) : ℕ) : ℤ) =
              4 * (cof3Run D k : ℤ) - (3 * (totalFloor3 (D + 1 + k) : ℤ) + 3) := by
          push_cast [Nat.cast_sub hle]
          ring
        rw [hcast]
        exact hmain
      · have hcondZ : 4 * (cof3Run D k : ℤ) ≤ 3 * (totalFloor3 (D + 1 + k) : ℤ) + 3 := by
          have hnat : 4 * cof3Run D k ≤ 3 * totalFloor3 (D + 1 + k) + 3 := by omega
          exact_mod_cast hnat
        simp only [Nat.cast_zero]
        omega

/-- The negative branch of the dichotomy, run to depth six, is contradictory for every
class outside `D ≡ 20 (mod 21)`. -/
theorem cof3_allRight_impossible
    (D : ℕ) (hD : 60 ≤ D) (h21 : D % 21 ≠ 20)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (hcof : ∀ s : ℕ, D + 1 ≤ s → s < D + 7 →
      cof3Ranks s ⊆ seamWordSupport (seamGreedyWord s)) :
    False := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  have hbound := cof3Run_bound D hD hright hlanding hcof 6 le_rfl
  rw [cof3Ratchet_run_eq_zero D h21] at hbound
  have hpos : 0 < Recon257.seamExcess (D + 1 + 6) := by
    have := (horbit (D + 1 + 6) (by omega)).1
    simpa [Recon257.seamExcess] using this
  have hone : Recon257.seamExcess (D + 1 + 6) = 1 := by
    simp only [Nat.cast_zero] at hbound
    omega
  have hstep := (horbit (D + 1 + 6) (by omega)).2
  have hrec : Recon257.seamExcess (D + 1 + 6 + 1) =
      4 * Recon257.seamExcess (D + 1 + 6) -
        ((seamAdjacentCut (D + 1 + 6) (by omega : 5 ≤ D + 1 + 6)).belowPulse : ℤ) - 4 := by
    simpa [Recon257.seamExcess] using hstep
  have hnext : 0 < Recon257.seamExcess (D + 1 + 6 + 1) := by
    have := (horbit (D + 1 + 6 + 1) (by omega)).1
    simpa [Recon257.seamExcess] using this
  have hfloor : (Recon257.pulseFloor (D + 1 + 6) : ℤ) ≤
      ((seamAdjacentCut (D + 1 + 6) (by omega : 5 ≤ D + 1 + 6)).belowPulse : ℤ) := by
    exact_mod_cast Recon257.pulseFloor_le_belowPulse (D + 1 + 6) (by omega)
  have hone' : (1 : ℤ) ≤ (Recon257.pulseFloor (D + 1 + 6) : ℤ) := by
    exact_mod_cast Recon257.one_le_pulseFloor (D + 1 + 6)
  rw [hone] at hrec
  omega

/-! ## 8.  The finite conditional dichotomy -/

/-- **PROVED CONDITIONAL.**  Within the hypothetical configuration, the
cofactor hypothesis is replaced by a finite disjunction.  For every `D ≥ 60`,
a final middle cell of charge `-2` at
rank `D` with an all-right tail forces a largest false rank beyond one half of the row,
at one of the three explicit rows `D+1, D+2, D+3`.

Inside those assumptions, either the cofactor ranks are selected at all
three rows — and then `AngleB2.allRight_landingExcess_two_impossible` is a
contradiction — or a row has a
mid-late largest skip.  This conclusion is confined to one three-row window and
does not supply the step socket required for the endpoint theorem.  Direct
evaluation finds no `hlanding` instance in `s ∈ [5,102]`, so this theorem
excludes no audited class. -/
theorem allRight_landingExcess_two_midSkip
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ s : ℕ, D + 1 ≤ s ∧ s < D + 4 ∧ LargestSkipMidAt s := by
  by_contra hcon
  push Not at hcon
  refine AngleB2.allRight_landingExcess_two_impossible D hD hright hlanding ?_
  intro s h1 h2
  rcases cofRanks_mid_dichotomy s (by omega) with h | h
  · exact h
  · exact absurd h (hcon s h1 h2)

/-- **PROVED CONDITIONAL.**  For every residue phase outside
`D ≡ 20 (mod 21)`, a hypothetical final middle cell of charge `-2` at rank
`D ≥ 60` with an all-right tail forces a
late largest skip** at one of the six explicit rows `D+1, …, D+6`.  No residual
hypothesis is used.  The conclusion still assumes the uninstantiated landing
equation, so it excludes no audited class. -/
theorem allRight_landingExcess_two_lateSkip
    (D : ℕ) (hD : 60 ≤ D) (h21 : D % 21 ≠ 20)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ s : ℕ, D + 1 ≤ s ∧ s < D + 7 ∧ LargestSkipLateAt s := by
  by_contra hcon
  push Not at hcon
  refine cof3_allRight_impossible D hD h21 hright hlanding ?_
  intro s h1 h2
  rcases cof3_dichotomy s (by omega) with h | h
  · exact h
  · exact absurd h (hcon s h1 h2)

/-- **PROVED CONDITIONAL DICHOTOMY.**  Assuming the all-right tail and the
uninstantiated landing equation, `D` either lies in the
`D ≡ 20 (mod 21)` phase or produces a late largest skip. -/
theorem allRight_landingExcess_two_dichotomy
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    D % 21 = 20 ∨ ∃ s : ℕ, D + 1 ≤ s ∧ s < D + 7 ∧ LargestSkipLateAt s := by
  by_cases h : D % 21 = 20
  · exact Or.inl h
  · exact Or.inr (allRight_landingExcess_two_lateSkip D hD h hright hlanding)

/-- **PROVED CONDITIONAL DISJUNCTION.**  On the all-right tail with landing
excess `2`, at one of the three rows `D+1, D+2, D+3`
either the row has a late largest skip — the positive branch, in exactly the
vocabulary of `HalfCylinderLargestSkipInduction` — or the **half rank** `(s+1)/2` is
skipped.  By `half_rank_never_late` the second alternative is genuinely outside the
reach of any two-thirds-boundary argument, so this is the sharp statement of what
remains within those assumptions.  No landing instance is known in the audited
range. -/
theorem allRight_landingExcess_two_lateSkip_or_halfSkip
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ s : ℕ, D + 1 ≤ s ∧ s < D + 4 ∧
      (LargestSkipLateAt s ∨
        ((s + 1) / 2 ∈ AngleB2.cofRanks s ∧
          (s + 1) / 2 ∉ seamWordSupport (seamGreedyWord s))) := by
  by_contra hcon
  push Not at hcon
  refine AngleB2.allRight_landingExcess_two_impossible D hD hright hlanding ?_
  intro s h1 h2 m hm
  obtain ⟨hnotlate, hhalf⟩ := hcon s h1 h2
  have hm' := cofRanks_subset_insert_half s hm
  simp only [Finset.mem_insert] at hm'
  rcases hm' with rfl | hm3
  · exact hhalf hm
  · rcases cof3_dichotomy s (by omega) with h | h
    · exact h hm3
    · exact absurd h hnotlate

/-! ## 9.  The one-half producer reaches the same endpoint

`HalfCylinderLargestSkipInduction` builds the fan-in from `LargestSkipLateAt` to
`1/2 ∈ mersenneAchievementSet`.  Nothing in that fan-in needs the two-thirds constant:
`SeamGreedyUnboundedSkippedRanksAlong` only asks that the skipped rank tend to infinity,
and `s < 2 * d` forces `d > s / 2 → ∞` just as well as `2 * s < 3 * d` does.  The whole
route is therefore available at the one-half line, which is the line the dichotomy of
§4b actually certifies. -/

section MidSocket

open Set Filter

/-- The one-half analogue of `LargestSkipLateStepSocket`: before a mid-late largest
false rank can cross the one-half boundary, the concrete successor must take an upper
or middle branch. -/
def LargestSkipMidStepSocket : Prop :=
  ∀ (s d : ℕ) (hs : 14 ≤ s),
    IsLargestFalseRank (seamGreedyWord s) d →
      s < 2 * d →
        s + 1 < 2 * d ∨ SeamGreedyUpperOrMiddleAt s (by omega)

/-- The row-fourteen base, inherited from `largestSkipLateAt_fourteen`. -/
theorem largestSkipMidAt_fourteen : LargestSkipMidAt 14 :=
  largestSkipMidAt_of_largestSkipLateAt largestSkipLateAt_fourteen

theorem LargestSkipMidStepSocket.largestSkipMidAt_succ
    (hstep : LargestSkipMidStepSocket)
    {s : ℕ} (hs : 14 ≤ s) (hmid : LargestSkipMidAt s) :
    LargestSkipMidAt (s + 1) := by
  obtain ⟨d, hmax, hmargin⟩ := hmid
  let hs5 : 5 ≤ s := by omega
  by_cases hUM : SeamGreedyUpperOrMiddleAt s hs5
  · refine ⟨s,
      seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle s hs5 hUM, ?_⟩
    omega
  · have hmargin' : s + 1 < 2 * d := by
      rcases hstep s d hs hmax hmargin with hnext | hproducer
      · exact hnext
      · exact False.elim (hUM hproducer)
    have hcarry : ¬ (seamAdjacentCut s hs5).successorCarries := by
      intro hcarry
      exact hUM (Or.inl hcarry)
    have hright : (seamAdjacentCut s hs5).terminalWeight ≤
        4 * (seamAdjacentCut s hs5).remainder +
          (seamPerturbedFamily s (by omega)).gap -
          (seamAdjacentCut s hs5).belowPulse := by
      apply Nat.le_of_not_gt
      intro hmiddle
      exact hUM (Or.inr ⟨hcarry, hmiddle⟩)
    exact ⟨d, hmax.seamGreedyWord_succ_of_rightBranch hs5 hcarry hright, hmargin'⟩

theorem largestSkipMidAt_of_stepSocket
    (hstep : LargestSkipMidStepSocket) (s : ℕ) (hs : 14 ≤ s) :
    LargestSkipMidAt s := by
  induction s, hs using Nat.le_induction with
  | base => exact largestSkipMidAt_fourteen
  | succ s hs ih => exact hstep.largestSkipMidAt_succ hs ih

/-- The one-half invariant supplies cofinal skipped ranks in exactly the format the
existing compactness theorem consumes.  Only `d > s / 2 → ∞` is used, never the
two-thirds constant. -/
theorem seamGreedyUnboundedSkippedRanksAlong_of_largestSkipMidStepSocket
    (hstep : LargestSkipMidStepSocket) :
    SeamGreedyUnboundedSkippedRanksAlong (fun j : ℕ => 14 + j) := by
  classical
  have hmid : ∀ j : ℕ, LargestSkipMidAt (14 + j) := fun j =>
    largestSkipMidAt_of_stepSocket hstep (14 + j) (by omega)
  choose rank hrank using hmid
  let skip : ∀ j : ℕ, Fin ((14 + j) - 2) := fun j =>
    ⟨rank j - 2, by
      rcases (hrank j).1 with ⟨_hd2, hds, _hdnot, _hfull⟩
      omega⟩
  refine ⟨skip, ?_, ?_, ?_⟩
  · simpa [Nat.add_comm] using tendsto_add_atTop_nat 14
  · apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (2 * B)] with j hj
    rcases (hrank j).1 with ⟨hd2, _hds, _hdnot, _hfull⟩
    have hmargin := (hrank j).2
    have hrankEq : (skip j : ℕ) + 2 = rank j := by
      dsimp [skip]
      omega
    rw [hrankEq]
    omega
  · intro j
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    rcases (hrank j).1 with ⟨hd2, _hds, hdnot, _hfull⟩
    have hrankEq : rank j = (skip j : ℕ) + 2 := by
      dsimp [skip]
      omega
    have hmem : rank j ∈ seamWordSupport (seamGreedyWord (14 + j)) :=
      mem_seamWordSupport_iff.mpr ⟨skip j, htrue, hrankEq⟩
    exact hdnot hmem

/-- **The one-half socket is sufficient for the `#257` half-membership endpoint.**
Same conclusion as
`half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket`, from the one-half
line instead of the two-thirds line. -/
theorem half_mem_mersenneAchievementSet_of_largestSkipMidStepSocket
    (hstep : LargestSkipMidStepSocket) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_unboundedSkippedRanks (fun j : ℕ => 14 + j)
    (seamGreedyUnboundedSkippedRanksAlong_of_largestSkipMidStepSocket hstep)

end MidSocket

/-!
## Closing note

Four things are settled here.

1.  **The D5 question is answered negatively, exactly.**  Undiscounted cardinality
    carries no mass: `sum_rowPulse_eq_zero_of_above_late` shows a certified block of
    arbitrary size above a late skip has row pulse `0`, and
    `no_floor_can_stop_escaped_budget` shows that in the other regime the universal
    cardinality cap `2 * (s - 2)` is already too small.  Combining B1's linear support
    growth with B4's `transportedFloor` cannot work — not because the bound is loose,
    but because the quantity is zero.

2.  **The skip dichotomy is true, in two forms, and both are proved.**  At the
    two-thirds line it certifies exactly the cofactor-three ranks (`cof3_dichotomy`),
    and `half_rank_never_late` with `only_cofactor_three_is_late` show that is sharp:
    `3` is the only cofactor whose rank lies beyond `2s/3`.  At the one-half line it
    certifies *all* of `AngleB2.cofRanks` (`cofRanks_mid_dichotomy`), because the half
    rank clears `s/2` by exactly one unit.  The whole gap between B2's hypothesis and
    what a largest-skip argument can supply is that one unit.

3.  **The cofactor hypothesis becomes a finite conditional disjunction.**
    `allRight_landingExcess_two_midSkip`: for *every* `D ≥ 60`, a hypothetical final
    middle cell of charge `-2` with an all-right tail forces `LargestSkipMidAt s` at one
    of `D+1, D+2, D+3`.  B2's residual hypothesis `hcof` is gone — it is now one side of
    a proved disjunction whose other side is a producer predicate at one of
    three rows, not a cofinal producer.  The landing premise has no audited
    instance, so this is not a concrete class exclusion.

4.  **The producer format is adequate.**
    `half_mem_mersenneAchievementSet_of_largestSkipMidStepSocket` reaches
    `1/2 ∈ mersenneAchievementSet` from the one-half line, so nothing is lost by moving
    off the two-thirds line: `SeamGreedyUnboundedSkippedRanksAlong` never used the
    constant, only that the skipped rank tends to infinity.

What is **not** proved is `1/2 ∈ mersenneAchievementSet` itself.  Both endpoint routes
consume a *step socket* — a statement at every row `s ≥ 14` — while
`allRight_landingExcess_two_midSkip` produces `LargestSkipMidAt` at three rows of one
class.  On an all-right tail that cannot be upgraded by propagation:
`IsLargestFalseRank.extend_true` freezes the largest false rank at a constant `d`, so
`s < 2 * d` necessarily fails by row `2 * d ≤ 2 * D`.  The witness produced here is a
*finite* skip witness, not a cofinal one, and closing that gap is the first-crossing
socket — unchanged in kind from before, but now needed only at the one-half boundary,
where the successor has to move the line by one unit per row instead of two thirds of
one.

Axiom audit (checked with `#print axioms`, then removed so that `lake env lean` on this
file produces empty output): `cof3Ratchet_finite_core` depends on **no axioms at all**
— it is a pure kernel evaluation — and `cof3_dichotomy`, `cofRanks_mid_dichotomy`,
`allRight_landingExcess_two_midSkip`, `allRight_landingExcess_two_lateSkip`,
`allRight_landingExcess_two_dichotomy`,
`allRight_landingExcess_two_lateSkip_or_halfSkip` and
`half_mem_mersenneAchievementSet_of_largestSkipMidStepSocket` depend only on
`propext, Classical.choice, Quot.sound`.  No `sorry`, no `native_decide`, no new axiom.
-/

end D5

end Erdos249257
