import Erdos249257.BooleanMobiusSkipRow
import Erdos249257.HalfCutLocator

/-!
# Recycling an above-half support through its first crossing

A finite positive-rank Boolean--Möbius support above one half has a first
selected rank at which its real Mersenne value crosses one half.  The strict
prefix before that rank is a skipped core: it is below one half and its deficit
is smaller than the weight of the crossing rank.  The skipped-core constructor
therefore turns it into an exact quotient row.

This is an unconditional sign-recycling step.  It does not assert that the
new endpoint is larger than the old one; that quantitative crossing-location
question is kept separate.
-/

namespace Erdos249257

open scoped BigOperators

/-- Ranks of `E` at which its inclusive ordered prefix is already above one
half. -/
def localMersenneCrossingRanks (E : Finset ℕ) : Finset ℕ :=
  E.filter fun c ↦
    (1 / 2 : ℚ) < localMersennePrefixValue (E.filter fun d ↦ d ≤ c)

/-- A finite positive-rank support above one half has a first crossing rank.
The prefix before that rank is strictly below one half, and adding the
crossing rank crosses strictly above one half. -/
theorem exists_first_localMersenne_crossing
    {E : Finset ℕ}
    (hE : ∀ d ∈ E, 2 ≤ d)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ,
      c ∈ E ∧
      4 ≤ c ∧
      localMersennePrefixValue (E.filter fun d ↦ d < c) < (1 / 2 : ℚ) ∧
      (1 / 2 : ℚ) <
        localMersennePrefixValue (insert c (E.filter fun d ↦ d < c)) := by
  classical
  have hEnonempty : E.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at habove
    simp [localMersennePrefixValue] at habove
    norm_num at habove
  let m := E.max' hEnonempty
  have hmE : m ∈ E := Finset.max'_mem E hEnonempty
  have hprefixMax : E.filter (fun d ↦ d ≤ m) = E := by
    apply Finset.filter_eq_self.2
    intro d hd
    exact Finset.le_max' E d hd
  have hcrossNonempty : (localMersenneCrossingRanks E).Nonempty := by
    refine ⟨m, ?_⟩
    simp only [localMersenneCrossingRanks, Finset.mem_filter]
    exact ⟨hmE, by simpa [hprefixMax] using habove⟩
  let c := (localMersenneCrossingRanks E).min' hcrossNonempty
  have hcCross : c ∈ localMersenneCrossingRanks E :=
    Finset.min'_mem _ hcrossNonempty
  have hcData := Finset.mem_filter.mp hcCross
  have hcE : c ∈ E := hcData.1
  have hcAbove :
      (1 / 2 : ℚ) < localMersennePrefixValue (E.filter fun d ↦ d ≤ c) :=
    hcData.2
  let D := E.filter fun d ↦ d < c
  have hcNotD : c ∉ D := by simp [D]
  have hInclusive : E.filter (fun d ↦ d ≤ c) = insert c D := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_insert, D]
    constructor
    · rintro ⟨hdE, hdc⟩
      by_cases hdcEq : d = c
      · exact Or.inl hdcEq
      · exact Or.inr ⟨hdE, by omega⟩
    · rintro (rfl | ⟨hdE, hdc⟩)
      · exact ⟨hcE, le_rfl⟩
      · exact ⟨hdE, hdc.le⟩
  have hDle : localMersennePrefixValue D ≤ (1 / 2 : ℚ) := by
    by_contra hnot
    have hDabove : (1 / 2 : ℚ) < localMersennePrefixValue D :=
      lt_of_not_ge hnot
    have hDnonempty : D.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h] at hDabove
      simp [localMersennePrefixValue] at hDabove
      norm_num at hDabove
    let e := D.max' hDnonempty
    have heD : e ∈ D := Finset.max'_mem D hDnonempty
    have heE : e ∈ E := (Finset.mem_filter.mp heD).1
    have hec : e < c := (Finset.mem_filter.mp heD).2
    have hprefixE : E.filter (fun d ↦ d ≤ e) = D := by
      ext d
      constructor
      · intro hd
        have hdData := Finset.mem_filter.mp hd
        exact Finset.mem_filter.mpr ⟨hdData.1, hdData.2.trans_lt hec⟩
      · intro hd
        have hdData := Finset.mem_filter.mp hd
        exact Finset.mem_filter.mpr
          ⟨hdData.1, Finset.le_max' D d hd⟩
    have heCross : e ∈ localMersenneCrossingRanks E := by
      simp only [localMersenneCrossingRanks, Finset.mem_filter]
      exact ⟨heE, by simpa [hprefixE] using hDabove⟩
    have hce : c ≤ e := Finset.min'_le _ _ heCross
    omega
  have hDzero : 0 ∉ D := by
    intro hzero
    have hzeroE : 0 ∈ E := (Finset.mem_filter.mp hzero).1
    have := hE 0 hzeroE
    omega
  have hDne : localMersennePrefixValue D ≠ (1 / 2 : ℚ) := by
    intro heq
    have hodd := finiteErdosSum_den_odd D hDzero
    rw [← localMersennePrefixValue_eq_finiteErdosSum, heq] at hodd
    obtain ⟨k, hk⟩ := hodd
    norm_num at hk
    omega
  have hDbelow : localMersennePrefixValue D < (1 / 2 : ℚ) :=
    lt_of_le_of_ne hDle hDne
  have hcFour : 4 ≤ c := by
    by_contra hnot
    have hcLe : c ≤ 3 := by omega
    let F := E.filter fun d ↦ d ≤ c
    have hFsub : F ⊆ ({2, 3} : Finset ℕ) := by
      intro d hd
      have hdData := Finset.mem_filter.mp hd
      have hdTwo := hE d hdData.1
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hFle : localMersennePrefixValue F ≤
        localMersennePrefixValue ({2, 3} : Finset ℕ) := by
      unfold localMersennePrefixValue
      apply Finset.sum_le_sum_of_subset_of_nonneg hFsub
      intro d hd _hdF
      exact (mersenneWeightRat_pos (n := d) (by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        omega)).le
    have h23 : localMersennePrefixValue ({2, 3} : Finset ℕ) <
        (1 / 2 : ℚ) := by
      norm_num [localMersennePrefixValue, mersenneWeightRat]
    have : localMersennePrefixValue F < (1 / 2 : ℚ) := hFle.trans_lt h23
    exact (not_lt_of_ge hcAbove.le) (by simpa [F] using this)
  refine ⟨c, hcE, hcFour, ?_, ?_⟩
  · simpa [D] using hDbelow
  · have hcrossD :
        (1 / 2 : ℚ) < localMersennePrefixValue (insert c D) := by
      rw [← hInclusive]
      exact hcAbove
    simpa [D] using hcrossD

/-- **Above-support recycling.**  If a finite positive-rank support bounded by
`n` lies above one half, its first crossing rank supplies an unconditional
skipped-core exact row.  The recycled crossing rank lies between `4` and `n`.
-/
theorem exists_skippedCoreExactRow_of_value_above
    {E : Finset ℕ} {n : ℕ}
    (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ,
      4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2) := by
  obtain ⟨c, hcE, hcFour, hbelow, hcross⟩ :=
    exists_first_localMersenne_crossing
      (fun d hd ↦ (hE d hd).1) habove
  let D := E.filter fun d ↦ d < c
  have hD : ∀ d ∈ D, 2 ≤ d ∧ d < c := by
    intro d hd
    have hdData := Finset.mem_filter.mp hd
    exact ⟨(hE d hdData.1).1, hdData.2⟩
  have hcNotD : c ∉ D := by simp [D]
  have hinsert :
      localMersennePrefixValue (insert c D) =
        localMersennePrefixValue D + mersenneWeightRat c := by
    unfold localMersennePrefixValue
    rw [Finset.sum_insert hcNotD]
    ring
  have hskip :
      (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c := by
    have hcrossD :
        (1 / 2 : ℚ) < localMersennePrefixValue (insert c D) := by
      simpa [D] using hcross
    rw [hinsert] at hcrossD
    linarith
  refine ⟨c, hcFour, (hE c hcE).2, ?_⟩
  exact exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCore
    hcFour hD (by simpa [D] using hbelow) hskip

/-! ## Strict progress for sharp skipped-core repairs -/

/-- First-crossing data can be consumed directly by the skipped-core exact-row
constructor.  This is the nonexistential form of the recycling step. -/
theorem exactLocalMersenneHalfRow_of_first_localMersenne_crossing
    {E : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hE : ∀ d ∈ E, 2 ≤ d)
    (hbelow :
      localMersennePrefixValue (E.filter fun d ↦ d < c) < (1 / 2 : ℚ))
    (hcross :
      (1 / 2 : ℚ) <
        localMersennePrefixValue
          (insert c (E.filter fun d ↦ d < c))) :
    ExactLocalMersenneHalfRow (2 * c - 2) := by
  let D := E.filter fun d ↦ d < c
  have hD : ∀ d ∈ D, 2 ≤ d ∧ d < c := by
    intro d hd
    have hdData := Finset.mem_filter.mp hd
    exact ⟨hE d hdData.1, hdData.2⟩
  have hcNotD : c ∉ D := by simp [D]
  have hinsert :
      localMersennePrefixValue (insert c D) =
        localMersennePrefixValue D + mersenneWeightRat c := by
    unfold localMersennePrefixValue
    rw [Finset.sum_insert hcNotD]
    ring
  have hskip :
      (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c := by
    have hcrossD :
        (1 / 2 : ℚ) < localMersennePrefixValue (insert c D) := by
      simpa [D] using hcross
    rw [hinsert] at hcrossD
    linarith
  exact exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCore
    hc hD (by simpa [D] using hbelow) hskip

/-- A sharp skipped-core repair cannot recycle at the same endpoint.  The
`c-2`-bit capacity builds an exact row at `2c-2` using no new rank at or below
`c`.  If that row is below one half, it is returned as a below-half exact row.
If it is above one half, its first crossing is strictly later than `c`, and
recycling there produces an exact row whose endpoint is strictly larger than
`2c-2`.

This theorem consumes the sharp capacity inequality; it does not assert that
the inequality holds for every skipped core. -/
theorem skippedCoreSharpCapacity_below_or_strictly_laterExactRow
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hsharp : localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    (∃ E : Finset ℕ,
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * c - 2) ∧
      localPrefixQuotient E (2 * c - 2) =
        2 ^ ((2 * c - 2) - 1) - 1 ∧
      localMersennePrefixValue E < (1 / 2 : ℚ)) ∨
    ∃ e : ℕ,
      c < e ∧
      e ≤ 2 * c - 2 ∧
      2 * c - 2 < 2 * e - 2 ∧
      ExactLocalMersenneHalfRow (2 * e - 2) := by
  classical
  obtain ⟨E, hDE, hnew, hE, hquot⟩ :=
    exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity
      hc hD hbelow hsharp
  have hzero : 0 ∉ E := by
    intro hzero
    have := (hE 0 hzero).1
    omega
  have hne : localMersennePrefixValue E ≠ (1 / 2 : ℚ) := by
    intro heq
    have hodd := finiteErdosSum_den_odd E hzero
    rw [← localMersennePrefixValue_eq_finiteErdosSum, heq] at hodd
    obtain ⟨k, hk⟩ := hodd
    norm_num at hk
    omega
  rcases lt_or_gt_of_ne hne with hEbelow | hEabove
  · exact Or.inl ⟨E, hE, hquot, hEbelow⟩
  · obtain ⟨e, heE, heFour, heBelow, heCross⟩ :=
      exists_first_localMersenne_crossing
        (fun d hd ↦ (hE d hd).1) hEabove
    have heLater : c < e := by
      by_contra hnot
      have heLe : e ≤ c := by omega
      let F := insert e (E.filter fun d ↦ d < e)
      have hFsub : F ⊆ D := by
        intro d hdF
        simp only [F, Finset.mem_insert, Finset.mem_filter] at hdF
        rcases hdF with hdeq | ⟨hdE, hde⟩
        · have heD : e ∈ D := by
            by_contra heD
            have := hnew e heE heD
            omega
          simpa [hdeq] using heD
        · by_contra hdD
          have := hnew d hdE hdD
          omega
      have hFle : localMersennePrefixValue F ≤
          localMersennePrefixValue D := by
        unfold localMersennePrefixValue
        apply Finset.sum_le_sum_of_subset_of_nonneg hFsub
        intro d hdD _hdF
        have hd2 : 2 ≤ d := (hD d hdD).1
        exact (mersenneWeightRat_pos (n := d) (by omega)).le
      have hFabove : (1 / 2 : ℚ) < localMersennePrefixValue F := by
        simpa [F] using heCross
      linarith
    have heUpper : e ≤ 2 * c - 2 := (hE e heE).2
    refine Or.inr ⟨e, heLater, heUpper, by omega, ?_⟩
    exact exactLocalMersenneHalfRow_of_first_localMersenne_crossing
      heFour (fun d hd ↦ (hE d hd).1) heBelow heCross

end Erdos249257
