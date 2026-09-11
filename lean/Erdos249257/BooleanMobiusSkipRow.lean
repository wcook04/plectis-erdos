import Erdos249257.BooleanMobiusSkippedCoreExactRow
import Erdos249257.BooleanMobiusCofinalExactRows

/-!
# Exact quotient rows supplied by skipped cores

`BooleanMobiusSkippedCoreExactRow` proves that the quotient defect left by a
finite skipped core fits in the pure binary window at endpoint `2c - 2`.
This module turns that Boolean word into an actual finite support and hence
into an `ExactLocalMersenneHalfRow`.
-/

namespace Erdos249257

open scoped BigOperators

/-! ## Turning a least-significant-digit-first word into an upper support -/

/-- The support encoded by a least-significant-digit-first word whose top
rank is `M`.  The head controls rank `M`, the next digit rank `M-1`, and so
on. -/
def upperSupportFromWord : ℕ → List ℕ → Finset ℕ
  | _, [] => ∅
  | M, b :: y =>
      if b = 1 then
        insert M (upperSupportFromWord (M - 1) y)
      else
        upperSupportFromWord (M - 1) y

theorem upperSupportFromWord_le_top
    {M : ℕ} {y : List ℕ} {d : ℕ}
    (hd : d ∈ upperSupportFromWord M y) :
    d ≤ M := by
  induction y generalizing M with
  | nil => simp [upperSupportFromWord] at hd
  | cons b y ih =>
      rw [upperSupportFromWord] at hd
      split at hd
      · rw [Finset.mem_insert] at hd
        rcases hd with rfl | hd
        · exact le_rfl
        · exact (ih hd).trans (Nat.sub_le M 1)
      · exact (ih hd).trans (Nat.sub_le M 1)

/-- A word of length at most `M` uses only the final `y.length` positive
ranks ending at `M`. -/
theorem upperSupportFromWord_lower_bound
    {M : ℕ} {y : List ℕ} (hyM : y.length ≤ M)
    {d : ℕ} (hd : d ∈ upperSupportFromWord M y) :
    M + 1 - y.length ≤ d := by
  induction y generalizing M with
  | nil => simp [upperSupportFromWord] at hd
  | cons b y ih =>
      have hM : 1 ≤ M := by simp at hyM; omega
      have hyPred : y.length ≤ M - 1 := by simp at hyM; omega
      rw [upperSupportFromWord] at hd
      split at hd
      · rw [Finset.mem_insert] at hd
        rcases hd with rfl | hd
        · simp at hyM ⊢
        · have h := ih hyPred hd
          simp at hyM ⊢
          omega
      · have h := ih hyPred hd
        simp at hyM ⊢
        omega

/-! ## Pure upper-half quotient coins -/

/-- In the pure upper window, the quotient sum of the support encoded by a
Boolean word is exactly the binary value of that word. -/
theorem localPrefixQuotient_upperSupportFromWord
    {M : ℕ} {y : List ℕ}
    (hyM : y.length ≤ M)
    (hybool : ∀ b ∈ y, b = 0 ∨ b = 1)
    (hlower : M + 1 - y.length > M / 2)
    (hlower2 : 2 ≤ M + 1 - y.length) :
    localPrefixQuotient (upperSupportFromWord M y) M =
      Nat.ofDigits 2 y := by
  induction y generalizing M with
  | nil => simp [upperSupportFromWord, localPrefixQuotient]
  | cons b y ih =>
      have hM : 1 ≤ M := by simp at hyM; omega
      have hyPred : y.length ≤ M - 1 := by simp at hyM; omega
      have hboolHead : b = 0 ∨ b = 1 := hybool b (by simp)
      have hboolTail : ∀ z ∈ y, z = 0 ∨ z = 1 := by
        intro z hz
        exact hybool z (by simp [hz])
      have hlowerPred : (M - 1) + 1 - y.length > (M - 1) / 2 := by
        simp at hlower ⊢
        omega
      have hlower2Pred : 2 ≤ (M - 1) + 1 - y.length := by
        simp at hlower2 ⊢
        omega
      have htailTop : M ∉ upperSupportFromWord (M - 1) y := by
        intro hmem
        have := upperSupportFromWord_le_top hmem
        omega
      have htailBounds : ∀ d ∈ upperSupportFromWord (M - 1) y,
          2 ≤ d ∧ M / 2 < d ∧ d ≤ M - 1 := by
        intro d hd
        have hdlo := upperSupportFromWord_lower_bound hyPred hd
        have hdhi := upperSupportFromWord_le_top hd
        constructor
        · exact hlower2Pred.trans hdlo
        constructor
        · have : (M - 1) + 1 - y.length > M / 2 := by
            simp at hlower ⊢
            omega
          exact this.trans_le hdlo
        · exact hdhi
      have htailShift :
          ∑ d ∈ upperSupportFromWord (M - 1) y,
              localMersenneQuotient M d =
            2 * localPrefixQuotient (upperSupportFromWord (M - 1) y)
              (M - 1) := by
        rw [localPrefixQuotient, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        obtain ⟨hd2, hdhalf, hdPred⟩ := htailBounds d hd
        rw [localMersenneQuotient_eq_two_pow_sub_of_half_lt hd2 hdhalf
          (hdPred.trans (Nat.sub_le M 1))]
        have hdhalfPred : (M - 1) / 2 < d := by omega
        rw [localMersenneQuotient_eq_two_pow_sub_of_half_lt hd2 hdhalfPred hdPred]
        have hexp : M - d = ((M - 1) - d) + 1 := by omega
        rw [hexp, pow_succ]
        omega
      have ih' := ih hyPred hboolTail hlowerPred hlower2Pred
      rcases hboolHead with rfl | rfl
      · rw [upperSupportFromWord, if_neg (by omega)]
        change (∑ d ∈ upperSupportFromWord (M - 1) y,
            localMersenneQuotient M d) = Nat.ofDigits 2 (0 :: y)
        rw [htailShift, ih']
        simp [Nat.ofDigits]
      · rw [upperSupportFromWord, if_pos rfl, localPrefixQuotient,
          Finset.sum_insert htailTop]
        have hqtop : localMersenneQuotient M M = 1 := by
          rw [localMersenneQuotient_eq_two_pow_sub_of_half_lt
            (by omega : 2 ≤ M) (by omega) le_rfl]
          simp
        rw [hqtop, htailShift, ih']
        simp [Nat.ofDigits]

/-! ## The exact-row adapter -/

/-- **Skipped-core exact row.**  A finite Boolean support strictly below one
half whose deficit is already smaller than the next rank produces an exact
finite quotient row at endpoint `2c-2`. -/
theorem exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCore
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    ExactLocalMersenneHalfRow (2 * c - 2) := by
  let M := 2 * c - 2
  obtain ⟨y, hylen, hybool, hyvalue⟩ :=
    exists_upperHalfBooleanWord_of_skippedCore hc hD hbelow hskip
  let H := upperSupportFromWord M y
  refine ⟨D ∪ H, ?_, ?_⟩
  · intro d hd
    rw [Finset.mem_union] at hd
    rcases hd with hdD | hdH
    · have hdcore := hD d hdD
      exact ⟨hdcore.1, by omega⟩
    · have hdlo := upperSupportFromWord_lower_bound
          (M := M) (y := y) (by simp [M, hylen]; omega) hdH
      have hdhi := upperSupportFromWord_le_top hdH
      constructor
      · simp [M, hylen] at hdlo
        omega
      · exact hdhi
  · have hdisj : Disjoint D H := by
      rw [Finset.disjoint_left]
      intro d hdD hdH
      have hdlo := upperSupportFromWord_lower_bound
        (M := M) (y := y) (by simp [M, hylen]; omega) hdH
      have hdlt := (hD d hdD).2
      simp [M, hylen] at hdlo
      omega
    have hunion : localPrefixQuotient (D ∪ H) M =
        localPrefixQuotient D M + localPrefixQuotient H M := by
      unfold localPrefixQuotient
      rw [Finset.sum_union hdisj]
    have hH : localPrefixQuotient H M = Nat.ofDigits 2 y := by
      apply localPrefixQuotient_upperSupportFromWord
      · simp [M, hylen]
        omega
      · exact hybool
      · simp [M, hylen]
        omega
      · simp [M, hylen]
        omega
    have hDadm : localPrefixQuotient D M ≤ 2 ^ (M - 1) - 1 := by
      have hscaled := scaled_localMersennePrefixValue
        (D := D) (M := M) (fun d hd ↦ (hD d hd).1)
      have hpowPos : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
      have hlt := mul_lt_mul_of_pos_left hbelow hpowPos
      rw [hscaled] at hlt
      have hFnonneg : 0 ≤ localFractionMass D M := by
        unfold localFractionMass
        exact Finset.sum_nonneg fun d hd ↦
          (localMersenneFraction_pos (M := M) (hD d hd).1).le
      have hq : (localPrefixQuotient D M : ℚ) < (2 : ℚ) ^ (M - 1) := by
        have hhalf : (2 : ℚ) ^ M * (1 / 2 : ℚ) =
            (2 : ℚ) ^ (M - 1) := by
          have hMpos : 1 ≤ M := by dsimp [M]; omega
          calc
            (2 : ℚ) ^ M * (1 / 2 : ℚ) =
                2 ^ ((M - 1) + 1) * (1 / 2 : ℚ) := by congr 2 <;> omega
            _ = (2 : ℚ) ^ (M - 1) := by rw [pow_succ]; ring
        rw [hhalf] at hlt
        linarith
      have hqNat : localPrefixQuotient D M < 2 ^ (M - 1) := by
        exact_mod_cast hq
      omega
    have hsuffix : localPrefixQuotient D M + localBinarySuffix D 1 M =
        2 ^ (M - 1) - 1 := by
      unfold localBinarySuffix
      have hMpos : 1 ≤ M := by dsimp [M]; omega
      have hpowOne : 1 ≤ 2 ^ (M - 1) :=
        Nat.one_le_pow _ _ (by norm_num)
      have hQpow : localPrefixQuotient D M < 2 ^ (M - 1) := by omega
      omega
    rw [hunion, hH, hyvalue]
    simpa [M] using hsuffix

/-! ## Strict upper fills from the sharp skipped-core capacity -/

/-- If the skipped-core suffix fits in only `c-2` bits, its exact repair can
be placed strictly above rank `c`.  This is the support-separation form needed
by the first-crossing consumer: every newly inserted rank is larger than the
crossing rank that supplied the core.

The premise is deliberately the sharp integer inequality itself.  The weaker
skipped-core estimate currently proves only `c-1`-bit capacity. -/
theorem exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hsharp : localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, d ∉ D → c < d) ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * c - 2) ∧
      localPrefixQuotient E (2 * c - 2) =
        2 ^ ((2 * c - 2) - 1) - 1 := by
  let M := 2 * c - 2
  obtain ⟨y, hylen, hybool, hyvalue⟩ :=
    exists_boolean_word_of_lt_two_pow hsharp
  let H := upperSupportFromWord M y
  refine ⟨D ∪ H, Finset.subset_union_left, ?_, ?_, ?_⟩
  · intro d hdE hdD
    have hdH : d ∈ H := by
      rw [Finset.mem_union] at hdE
      exact hdE.resolve_left hdD
    have hdlo := upperSupportFromWord_lower_bound
      (M := M) (y := y) (by simp [M, hylen]; omega) hdH
    simp [M, hylen] at hdlo
    omega
  · intro d hd
    rw [Finset.mem_union] at hd
    rcases hd with hdD | hdH
    · have hdcore := hD d hdD
      exact ⟨hdcore.1, by omega⟩
    · have hdlo := upperSupportFromWord_lower_bound
          (M := M) (y := y) (by simp [M, hylen]; omega) hdH
      have hdhi := upperSupportFromWord_le_top hdH
      constructor
      · simp [M, hylen] at hdlo
        omega
      · simpa [M] using hdhi
  · have hdisj : Disjoint D H := by
      rw [Finset.disjoint_left]
      intro d hdD hdH
      have hdlo := upperSupportFromWord_lower_bound
        (M := M) (y := y) (by simp [M, hylen]; omega) hdH
      have hdlt := (hD d hdD).2
      simp [M, hylen] at hdlo
      omega
    have hunion : localPrefixQuotient (D ∪ H) M =
        localPrefixQuotient D M + localPrefixQuotient H M := by
      unfold localPrefixQuotient
      rw [Finset.sum_union hdisj]
    have hH : localPrefixQuotient H M = Nat.ofDigits 2 y := by
      apply localPrefixQuotient_upperSupportFromWord
      · simp [M, hylen]
        omega
      · exact hybool
      · simp [M, hylen]
        omega
      · simp [M, hylen]
        omega
    have hDadm : localPrefixQuotient D M ≤ 2 ^ (M - 1) - 1 := by
      have hscaled := scaled_localMersennePrefixValue
        (D := D) (M := M) (fun d hd ↦ (hD d hd).1)
      have hpowPos : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
      have hlt := mul_lt_mul_of_pos_left hbelow hpowPos
      rw [hscaled] at hlt
      have hFnonneg : 0 ≤ localFractionMass D M := by
        unfold localFractionMass
        exact Finset.sum_nonneg fun d hd ↦
          (localMersenneFraction_pos (M := M) (hD d hd).1).le
      have hq : (localPrefixQuotient D M : ℚ) < (2 : ℚ) ^ (M - 1) := by
        have hhalf : (2 : ℚ) ^ M * (1 / 2 : ℚ) =
            (2 : ℚ) ^ (M - 1) := by
          have hMpos : 1 ≤ M := by dsimp [M]; omega
          calc
            (2 : ℚ) ^ M * (1 / 2 : ℚ) =
                2 ^ ((M - 1) + 1) * (1 / 2 : ℚ) := by
                  congr 2 <;> omega
            _ = (2 : ℚ) ^ (M - 1) := by rw [pow_succ]; ring
        rw [hhalf] at hlt
        linarith
      have hqNat : localPrefixQuotient D M < 2 ^ (M - 1) := by
        exact_mod_cast hq
      omega
    have hsuffix : localPrefixQuotient D M + localBinarySuffix D 1 M =
        2 ^ (M - 1) - 1 := by
      unfold localBinarySuffix
      have hMpos : 1 ≤ M := by dsimp [M]; omega
      have hpowOne : 1 ≤ 2 ^ (M - 1) :=
        Nat.one_le_pow _ _ (by norm_num)
      have hQpow : localPrefixQuotient D M < 2 ^ (M - 1) := by omega
      omega
    rw [hunion, hH, hyvalue]
    simpa [M] using hsuffix

/-- The strict upper fill is, in particular, an exact local half row. -/
theorem exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hsharp : localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    ExactLocalMersenneHalfRow (2 * c - 2) := by
  obtain ⟨E, _hDE, _hnew, hE, hquot⟩ :=
    exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity
      hc hD hbelow hsharp
  exact ⟨E, hE, hquot⟩

/-- A strict upper fill agrees with its skipped core through rank `c`.
This is the exact prefix identity used to force any later crossing rank to be
strictly larger than `c`. -/
theorem strictUpperFill_filter_le_eq_core
    {D E : Finset ℕ} {c : ℕ}
    (hD : ∀ d ∈ D, d < c)
    (hDE : D ⊆ E)
    (hnew : ∀ d ∈ E, d ∉ D → c < d) :
    E.filter (fun d ↦ d ≤ c) = D := by
  ext d
  constructor
  · intro hd
    have hdData := Finset.mem_filter.mp hd
    by_contra hdD
    exact (not_lt_of_ge hdData.2) (hnew d hdData.1 hdD)
  · intro hdD
    exact Finset.mem_filter.mpr ⟨hDE hdD, (hD d hdD).le⟩

end Erdos249257
