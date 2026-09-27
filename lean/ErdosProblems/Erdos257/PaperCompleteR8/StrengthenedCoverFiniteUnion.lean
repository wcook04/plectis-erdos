import ErdosProblems.Erdos257.PaperCompleteR8.WeightedFiniteUnion
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Literal finite-union closure of the historical strengthened-cover class

Interleaving unchanged exponents need not preserve the geometric budget.
We halve each exponent before interleaving. Integer incidence counts still
have the same majorant, and each new cost is at most three times its old cost.
This proves class closure, not merely closure of the irrationality conclusion.
The factor 3 is a crude closure constant; this file does not prove the sharper
1 + sqrt 2 estimate.

This file does not import PositiveWeightPadding.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Lowering a positive exponent preserves a positive majorant of integer counts. -/
theorem nat_rpow_half_le (n : ℕ) {α : ℝ} (hα : 0 < α) :
    (n : ℝ) ^ (α / 2) ≤ (n : ℝ) ^ α := by
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow (ne_of_gt hα),
      Real.zero_rpow (ne_of_gt (half_pos hα))]
  · exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) (by linarith)

def interleavedCover (C D : PositiveCoverData) : PositiveCoverData where
  frame := fun n => (if n % 2 = 0 then C else D).frame (n / 2)
  exponent := fun n => (if n % 2 = 0 then C else D).exponent (n / 2) / 2
  coefficient := fun n => (if n % 2 = 0 then C else D).coefficient (n / 2)
  frame_positive := fun n => (if n % 2 = 0 then C else D).frame_positive (n / 2)
  exponent_bounds := by
    intro n
    have h := (if n % 2 = 0 then C else D).exponent_bounds (n / 2)
    constructor <;> linarith
  coefficient_nonneg := fun n =>
    (if n % 2 = 0 then C else D).coefficient_nonneg (n / 2)
  column_summable := fun n =>
    (if n % 2 = 0 then C else D).column_summable (n / 2)
  majorises := by
    intro n k hk
    exact (nat_rpow_half_le _
      ((if n % 2 = 0 then C else D).exponent_bounds (n / 2)).1).trans
      ((if n % 2 = 0 then C else D).majorises (n / 2) k hk)

@[simp] theorem interleavedCover_frame_even (C D : PositiveCoverData) (j : ℕ) :
    (interleavedCover C D).frame (2 * j) = C.frame j := by
  simp [interleavedCover]

@[simp] theorem interleavedCover_frame_odd (C D : PositiveCoverData) (j : ℕ) :
    (interleavedCover C D).frame (2 * j + 1) = D.frame j := by
  simp [interleavedCover, Nat.add_div]

theorem interleavedCover_host (C D : PositiveCoverData) :
    (interleavedCover C D).host = C.host ∪ D.host := by
  ext a
  constructor
  · rintro ⟨n, hn⟩
    by_cases h : n % 2 = 0
    · exact Or.inl ⟨n / 2, by simpa [interleavedCover, h] using hn⟩
    · exact Or.inr ⟨n / 2, by simpa [interleavedCover, h] using hn⟩
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact ⟨2 * j, by simpa using hj⟩
    · exact ⟨2 * j + 1, by simpa using hj⟩

/-- The denominator loss on halving an exponent is at most three. -/
theorem half_exponent_cover_cost_le (c α : ℝ) (hc : 0 ≤ c)
    (hα : 0 < α) (hα1 : α ≤ 1) (n j : ℕ) (hn : n + 1 ≤ 2 * (j + 1)) :
    c * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * (α / 2)) / ((2 : ℝ) ^ (α / 2) - 1) ≤
      3 * (c * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * α) / ((2 : ℝ) ^ α - 1)) := by
  let x : ℝ := (2 : ℝ) ^ (α / 2)
  have hx : 1 < x := Real.one_lt_rpow (by norm_num) (half_pos hα)
  have hx2 : x ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show α / 2 ≤ 1 by linarith)
    simpa [x] using h
  have hxx : x * x = (2 : ℝ) ^ α := by
    dsimp [x]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hnR : ((n + 1 : ℕ) : ℝ) ≤ 2 * ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have he : ((n + 1 : ℕ) : ℝ) * (α / 2) ≤ ((j + 1 : ℕ) : ℝ) * α := by
    nlinarith [mul_le_mul_of_nonneg_right hnR hα.le]
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  let A : ℝ := c * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * α)
  have hA : 0 ≤ A := mul_nonneg hc (Real.rpow_nonneg (by norm_num) _)
  have hd : 0 < (2 : ℝ) ^ α - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hα)
  have hquad : (2 : ℝ) ^ α - 1 ≤ 3 * (x - 1) := by
    rw [← hxx]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx2)]
  calc
    _ ≤ A / (x - 1) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp hc) (sub_nonneg.mpr hx.le)
    _ ≤ (3 * A) / ((2 : ℝ) ^ α - 1) := by
      apply (div_le_div_iff₀ (sub_pos.mpr hx) hd).2
      have h := mul_le_mul_of_nonneg_left hquad hA
      nlinarith only [h]
    _ = 3 * (A / ((2 : ℝ) ^ α - 1)) := by ring

theorem interleavedCover_strengthened (C D : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) (hD : D.StrengthenedCostSummable) :
    (interleavedCover C D).StrengthenedCostSummable := by
  let K : ℕ → ℝ := fun n => (interleavedCover C D).cost n *
    (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * (interleavedCover C D).exponent n) /
      ((2 : ℝ) ^ (interleavedCover C D).exponent n - 1)
  have hK : ∀ n, 0 ≤ K n := by
    intro n
    exact div_nonneg (mul_nonneg (positiveCover_cost_nonneg _ n)
      (Real.rpow_nonneg (by norm_num) _))
      (sub_pos.mpr (Real.one_lt_rpow (by norm_num) ((interleavedCover C D).exponent_bounds n).1)).le
  change Summable K
  apply Summable.even_add_odd
  · apply Summable.of_nonneg_of_le (fun j => hK (2 * j)) _ (hC.mul_left 3)
    intro j
    have h := half_exponent_cover_cost_le (C.cost j) (C.exponent j)
      (positiveCover_cost_nonneg C j) (C.exponent_bounds j).1 (C.exponent_bounds j).2
      (2 * j) j (by omega)
    simpa [K, interleavedCover, PositiveCoverData.cost] using h
  · apply Summable.of_nonneg_of_le (fun j => hK (2 * j + 1)) _ (hD.mul_left 3)
    intro j
    have h := half_exponent_cover_cost_le (D.cost j) (D.exponent j)
      (positiveCover_cost_nonneg D j) (D.exponent_bounds j).1 (D.exponent_bounds j).2
      (2 * j + 1) j (by omega)
    simpa [K, interleavedCover, PositiveCoverData.cost, Nat.add_div] using h

theorem hasStrengthenedPositiveCover_union {A B : Set ℕ}
    (hA : HasStrengthenedPositiveCover A) (hB : HasStrengthenedPositiveCover B) :
    HasStrengthenedPositiveCover (A ∪ B) := by
  obtain ⟨C, hAC, hC⟩ := hA
  obtain ⟨D, hBD, hD⟩ := hB
  refine ⟨interleavedCover C D, ?_, interleavedCover_strengthened C D hC hD⟩
  rw [interleavedCover_host]
  exact Set.union_subset_union hAC hBD

theorem hasStrengthenedPositiveCover_mono {A B : Set ℕ} (hBA : B ⊆ A)
    (hA : HasStrengthenedPositiveCover A) : HasStrengthenedPositiveCover B := by
  obtain ⟨C, hAC, hC⟩ := hA
  exact ⟨C, hBA.trans hAC, hC⟩

theorem finitePrimeWeighted_finset (b : ℕ) (F : Finset ℕ) :
    FinitePrimeWeighted b (F : Set ℕ) := by
  classical
  refine ⟨{2}, by simp, ?_, ?_⟩
  · intro p hp
    have hp2 : p = 2 := by simpa using hp
    subst p
    exact Nat.prime_two
  · apply summable_of_ne_finset_zero (s := F)
    intro a ha
    simp only [Set.indicator_of_notMem ha]

/-- The class named in the short note; positivity belongs to its weighted part. -/
def MixedSupportClass (A : Set ℕ) : Prop :=
  ∃ E V : Set ℕ, A ⊆ E ∪ V ∧ 0 ∉ E ∧ FinitePrimeWeighted 2 E ∧
    HasStrengthenedPositiveCover V

theorem mixedSupportClass_mono {A B : Set ℕ} (hBA : B ⊆ A)
    (hA : MixedSupportClass A) : MixedSupportClass B := by
  obtain ⟨E, V, hA, hE0, hE, hV⟩ := hA
  exact ⟨E, V, hBA.trans hA, hE0, hE, hV⟩

theorem mixedSupportClass_union {A B : Set ℕ}
    (hA : MixedSupportClass A) (hB : MixedSupportClass B) : MixedSupportClass (A ∪ B) := by
  obtain ⟨E, V, hAEV, hE0, hE, hV⟩ := hA
  obtain ⟨F, W, hBFW, hF0, hF, hW⟩ := hB
  refine ⟨E ∪ F, V ∪ W, ?_, ?_, finitePrimeWeighted_union 2 (by norm_num) hE hF,
    hasStrengthenedPositiveCover_union hV hW⟩
  · intro a ha
    rcases ha with ha | ha
    · rcases hAEV ha with ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inr (Or.inl ha)
    · rcases hBFW ha with ha | ha
      · exact Or.inl (Or.inr ha)
      · exact Or.inr (Or.inr ha)
  · exact fun h => h.elim hE0 hF0

theorem mixedSupportClass_adjoin_finset {A : Set ℕ} (hA : MixedSupportClass A)
    (F : Finset ℕ) (hF : 0 ∉ F) : MixedSupportClass (A ∪ (F : Set ℕ)) := by
  obtain ⟨E, V, hAEV, hE0, hE, hV⟩ := hA
  refine ⟨E ∪ (F : Set ℕ), V, ?_, ?_,
    finitePrimeWeighted_union 2 (by norm_num) hE (finitePrimeWeighted_finset 2 F), hV⟩
  · intro a ha
    rcases ha with ha | ha
    · exact (hAEV ha).elim (fun h => Or.inl (Or.inl h)) Or.inr
    · exact Or.inl (Or.inr ha)
  · exact fun h => h.elim hE0 hF

end ErdosProblems.Erdos257.PaperCompleteR8
end
