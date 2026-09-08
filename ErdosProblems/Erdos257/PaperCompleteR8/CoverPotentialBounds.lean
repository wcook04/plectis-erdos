import ErdosProblems.Erdos257.PaperCompleteR8.KernelRecurrence

/-!
# Summability and means of the ACTUAL positive-cover potentials

Uncompiled r8-upgrade proof candidates. Every summability condition here is
derived from PositiveCoverData and its displayed cost, before an interchange.
No extra incidence-majorisation premise or uniform positive exponent is assumed.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset Filter
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Reciprocal column cost is nonnegative, including conductor zero. -/
theorem positiveCover_cost_nonneg (C : PositiveCoverData) (j : ℕ) : 0 ≤ C.cost j := by
  apply tsum_nonneg
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · exact div_nonneg (C.coefficient_nonneg j d hd) (Nat.cast_nonneg d)

def coverBase (C : PositiveCoverData) (j : ℕ) : ℝ := (2 : ℝ) ^ C.exponent j

theorem coverBase_gt_one (C : PositiveCoverData) (j : ℕ) : 1 < coverBase C j :=
  Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr
    (Or.inl ⟨by norm_num, (C.exponent_bounds j).1⟩)

theorem coverBase_le_two (C : PositiveCoverData) (j : ℕ) : coverBase C j ≤ 2 := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (C.exponent_bounds j).2
  simpa only [Real.rpow_one] using h

def coverPotential (C : PositiveCoverData) (j N : ℕ) : ℝ :=
  divisorPotential (coverBase C j) (C.coefficient j) N

theorem coverPotential_nonneg (C : PositiveCoverData) (j N : ℕ) : 0 ≤ coverPotential C j N :=
  divisorPotential_nonneg _ (coverBase_gt_one C j) _ (C.coefficient_nonneg j) N

/-- A pointwise summable envelope for a single column. -/
theorem coverPotential_le_cost (C : PositiveCoverData) (j N : ℕ) :
    coverPotential C j N ≤ (2 * (N : ℝ) + 1) * (C.cost j / (coverBase C j - 1)) := by
  let B := coverBase C j
  have hB : 1 < B := coverBase_gt_one C j
  have hs := summable_divisorPotential_terms B hB (C.coefficient j)
    (C.coefficient_nonneg j) (C.column_summable j) N
  have ht : Summable (fun d : ℕ =>
      (2 * (N : ℝ) + 1) * ((C.coefficient j d / (d : ℝ)) / (B - 1))) :=
    ((C.column_summable j).div_const (B - 1)).mul_left (2 * (N : ℝ) + 1)
  have hbnd : ∀ d : ℕ,
      C.coefficient j d * kernelWeight B d N ≤
        (2 * (N : ℝ) + 1) * ((C.coefficient j d / (d : ℝ)) / (B - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [kernelWeight]
    · have h := mul_le_mul_of_nonneg_left
        (kernelWeight_le_pointwise_majorant B hB d N hd) (C.coefficient_nonneg j d hd)
      simp only [div_eq_mul_inv, mul_inv_rev] at h ⊢
      convert h using 1 <;> ring
  have h := Summable.tsum_le_tsum hbnd hs ht
  rw [tsum_mul_left, tsum_div_const] at h
  exact h

/-- Finite estimate (S) summed over a genuine PositiveCoverData column. -/
theorem dyadicMean_coverPotential_le (C : PositiveCoverData) (j L R M : ℕ)
    (hL : 0 < L) (hM : 0 < M) :
    dyadicMean L R M (coverPotential C j) ≤
      (1 + 4 * (L : ℝ) / M) * (C.cost j / (coverBase C j - 1)) := by
  let B := coverBase C j
  let K : ℝ := 1 + 4 * (L : ℝ) / M
  let u : ℕ → ℕ → ℝ := fun d N => C.coefficient j d * kernelWeight B d N
  have hB : 1 < B := coverBase_gt_one C j
  have hB2 : B ≤ 2 := coverBase_le_two C j
  have hu : ∀ N : ℕ, Summable (fun d => u d N) :=
    summable_divisorPotential_terms B hB (C.coefficient j)
      (C.coefficient_nonneg j) (C.column_summable j)
  have hdom : Summable (fun d : ℕ => K * ((C.coefficient j d / (d : ℝ)) / (B - 1))) :=
    ((C.column_summable j).div_const (B - 1)).mul_left K
  have hnonneg : ∀ d N, 0 ≤ u d N := by
    intro d N
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [u, kernelWeight]
    · exact mul_nonneg (C.coefficient_nonneg j d hd) (kernelWeight_nonneg hB d N)
  have hpoint : ∀ d : ℕ,
      dyadicMean L R M (u d) ≤ K * ((C.coefficient j d / (d : ℝ)) / (B - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [u, kernelWeight, dyadicMean, progressionMean]
    · rw [show u d = (fun N => C.coefficient j d * kernelWeight B d N) from rfl,
        dyadicMean_const_mul]
      have h := mul_le_mul_of_nonneg_left
        (dyadicMean_kernelWeight_le B hB hB2 L d R M hL hd hM)
        (C.coefficient_nonneg j d hd)
      dsimp only [K]
      simp only [div_eq_mul_inv, mul_inv_rev] at h ⊢
      convert h using 1 <;> ring
  have hs : Summable (fun d => dyadicMean L R M (u d)) :=
    Summable.of_nonneg_of_le
      (fun d => dyadicMean_nonneg L R M (u d) (hnonneg d)) hpoint hdom
  have h := Summable.tsum_le_tsum hpoint hs hdom
  rw [tsum_dyadicMean u hu L R M, tsum_mul_left, tsum_div_const] at h
  exact h

/-- Dyadic threshold at paper index j+1. -/
def coverThreshold (ε : ℝ) (j : ℕ) : ℝ := ε * ((2 : ℝ) ^ (j + 1))⁻¹

theorem coverThreshold_pos {ε : ℝ} (hε : 0 < ε) (j : ℕ) : 0 < coverThreshold ε j :=
  mul_pos hε (inv_pos.mpr (pow_pos (by norm_num) _))

theorem summable_coverThreshold (ε : ℝ) : Summable (coverThreshold ε) := by
  have hgeo : Summable (fun j : ℕ => ((2 : ℝ)⁻¹) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h := hgeo.mul_left (ε * (2 : ℝ)⁻¹)
  apply h.congr
  intro j
  simp only [coverThreshold, pow_succ, mul_inv, inv_pow]
  ring

theorem tsum_coverThreshold (ε : ℝ) : (∑' j, coverThreshold ε j) = ε := by
  unfold coverThreshold
  rw [tsum_mul_left, tsum_inv_pow_succ (by norm_num : (1 : ℝ) < 2)]
  norm_num

def coverScale (C : PositiveCoverData) (ε : ℝ) (j : ℕ) : ℝ :=
  coverThreshold ε j ^ (-C.exponent j)

def coverScaledCost (C : PositiveCoverData) (ε : ℝ) (j : ℕ) : ℝ :=
  coverScale C ε j * (C.cost j / (coverBase C j - 1))

theorem coverScale_pos (C : PositiveCoverData) {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    0 < coverScale C ε j := Real.rpow_pos_of_pos (coverThreshold_pos hε j) _

theorem coverScaledCost_nonneg (C : PositiveCoverData) {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    0 ≤ coverScaledCost C ε j :=
  mul_nonneg (coverScale_pos C hε j).le
    (div_nonneg (positiveCover_cost_nonneg C j) (sub_pos.mpr (coverBase_gt_one C j)).le)

/-- The exact reindexing of the printed cost; no inverse-exponent factor is lost. -/
theorem coverScale_eq (C : PositiveCoverData) {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    coverScale C ε j = ε ^ (-C.exponent j) *
      (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) := by
  have hq : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := pow_nonneg (by norm_num) _
  have hp : (((2 : ℝ) ^ (j + 1)) ^ C.exponent j) =
      (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  unfold coverScale coverThreshold
  rw [Real.mul_rpow hε.le (inv_nonneg.mpr hq), Real.inv_rpow hq,
    Real.rpow_neg hq, inv_inv, hp]

/-- The displayed strengthened cost supplies all scaled test summability. -/
theorem summable_coverScaledCost (C : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) {ε : ℝ} (hε : 0 < ε) :
    Summable (coverScaledCost C ε) := by
  let a : ℕ → ℝ := fun j =>
    C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) / (coverBase C j - 1)
  have ha : Summable a := hC
  have hn : ∀ j, 0 ≤ a j := by
    intro j
    exact div_nonneg (mul_nonneg (positiveCover_cost_nonneg C j)
      (Real.rpow_nonneg (by norm_num) _)) (sub_pos.mpr (coverBase_gt_one C j)).le
  have hdom : Summable (fun j => max 1 ε⁻¹ * a j) := ha.mul_left _
  apply Summable.of_nonneg_of_le (coverScaledCost_nonneg C hε) _ hdom
  intro j
  have heq : coverScaledCost C ε j = ε ^ (-C.exponent j) * a j := by
    unfold coverScaledCost
    rw [coverScale_eq C hε]
    dsimp [a]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (rpow_neg_le_max_one_inv hε (C.exponent_bounds j).1 (C.exponent_bounds j).2) (hn j)

/-- Tail test made from the actual cover potential, not a free error stream. -/
def coverTailTest (C : PositiveCoverData) (ε : ℝ) (J N : ℕ) : ℝ :=
  ∑' k : ℕ, coverScale C ε (k + J) * coverPotential C (k + J) N

theorem coverTailTest_nonneg (C : PositiveCoverData) {ε : ℝ} (hε : 0 < ε) (J N : ℕ) :
    0 ≤ coverTailTest C ε J N :=
  tsum_nonneg fun k => mul_nonneg (coverScale_pos C hε (k + J)).le
    (coverPotential_nonneg C (k + J) N)

theorem summable_coverTailTest_terms (C : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) {ε : ℝ} (hε : 0 < ε) (J N : ℕ) :
    Summable (fun k : ℕ => coverScale C ε (k + J) * coverPotential C (k + J) N) := by
  have hs : Summable (fun k => coverScaledCost C ε (k + J)) :=
    (summable_nat_add_iff J).mpr (summable_coverScaledCost C hC hε)
  have hdom := hs.mul_left (2 * (N : ℝ) + 1)
  apply Summable.of_nonneg_of_le _ _ hdom
  · intro k
    exact mul_nonneg (coverScale_pos C hε (k + J)).le (coverPotential_nonneg C (k + J) N)
  · intro k
    have h := mul_le_mul_of_nonneg_left (coverPotential_le_cost C (k + J) N)
      (coverScale_pos C hε (k + J)).le
    convert h using 1 <;> simp only [coverScaledCost] <;> ring

/-- The actual countable test is controlled on ANY common observation schedule. -/
theorem dyadicMean_coverTailTest_le (C : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) {ε : ℝ} (hε : 0 < ε)
    (J L R M : ℕ) (hL : 0 < L) (hM : 0 < M) :
    dyadicMean L R M (coverTailTest C ε J) ≤
      (1 + 4 * (L : ℝ) / M) * (∑' k, coverScaledCost C ε (k + J)) := by
  let u : ℕ → ℕ → ℝ := fun k N => coverScale C ε (k + J) * coverPotential C (k + J) N
  let K : ℝ := 1 + 4 * (L : ℝ) / M
  have hu : ∀ N, Summable (fun k => u k N) := summable_coverTailTest_terms C hC hε J
  have hcost : Summable (fun k => coverScaledCost C ε (k + J)) :=
    (summable_nat_add_iff J).mpr (summable_coverScaledCost C hC hε)
  have hdom : Summable (fun k => K * coverScaledCost C ε (k + J)) := hcost.mul_left K
  have hpoint : ∀ k, dyadicMean L R M (u k) ≤ K * coverScaledCost C ε (k + J) := by
    intro k
    change dyadicMean L R M (fun N => coverScale C ε (k + J) * coverPotential C (k + J) N) ≤ _
    rw [dyadicMean_const_mul]
    have h := mul_le_mul_of_nonneg_left
      (dyadicMean_coverPotential_le C (k + J) L R M hL hM) (coverScale_pos C hε (k + J)).le
    convert h using 1 <;> dsimp [K, coverScaledCost] <;> ring
  have hleft : Summable (fun k => dyadicMean L R M (u k)) := by
    refine Summable.of_nonneg_of_le ?_ hpoint hdom
    intro k
    exact dyadicMean_nonneg L R M (u k) (fun N =>
      mul_nonneg (coverScale_pos C hε (k + J)).le (coverPotential_nonneg C (k + J) N))
  have hh := Summable.tsum_le_tsum hpoint hleft hdom
  rw [tsum_dyadicMean u hu L R M, tsum_mul_left] at hh
  exact hh

end ErdosProblems.Erdos257.PaperCompleteR8
end
