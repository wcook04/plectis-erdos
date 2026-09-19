import ErdosProblems.Erdos257.CoverIndependentPeriodicMean
import ErdosProblems.Erdos257.PaperCompleteR7.CoverKernel

/-!
# Finite positive-cover logarithmic budget

The scalar logarithmic bound is combined with actual divisor-majorant
averaging. Frames may overlap: only domination of the incidence count by
the sum of frame counts is used. The family and each divisor majorant are
finite. This does not assert the countable-cover obstruction or construct
the infinite class-separating host.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

/-- A finite weighted cover has a frame at least as large as its weight share. -/
theorem exists_frame_ge_weight_share (J : Finset ℕ) (η u : ℕ → ℝ) (t : ℝ)
    (hJ : J.Nonempty) (hη : ∑ j ∈ J, η j = 1)
    (hcover : t ≤ ∑ j ∈ J, u j) :
    ∃ j ∈ J, η j * t ≤ u j := by
  by_contra h
  push_neg at h
  have hs := Finset.sum_lt_sum_of_nonempty hJ h
  have heq : (∑ j ∈ J, η j * t) = t := by rw [← Finset.sum_mul, hη, one_mul]
  rw [heq] at hs
  exact (not_lt_of_ge hcover) hs

/-- The finite-family pointwise lower bound, before averaging. -/
theorem finite_cover_log_pointwise (J : Finset ℕ) (η α : ℕ → ℝ)
    (f : ℕ) (g : ℕ → ℕ) (hJ : J.Nonempty)
    (hη : ∑ j ∈ J, η j = 1) (hηpos : ∀ j ∈ J, 0 < η j)
    (hα : ∀ j ∈ J, 0 < α j ∧ α j ≤ 1)
    (hcover : f ≤ ∑ j ∈ J, g j) :
    Real.exp 1 * Real.log (f : ℝ) ≤
      ∑ j ∈ J, (g j : ℝ) ^ α j / (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
  have hden : ∀ j ∈ J, 0 < (2 : ℝ) ^ α j - 1 := by
    intro j hj
    have hh := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (hα j hj).1
    linarith
  have hnonneg : ∀ j ∈ J,
      0 ≤ (g j : ℝ) ^ α j / (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
    intro j hj
    exact div_nonneg (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_pos_of_pos (hηpos j hj) _).le) (hden j hj).le
  by_cases hf : f = 0
  · simp only [hf, Nat.cast_zero, Real.log_zero, mul_zero]
    exact Finset.sum_nonneg hnonneg
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hf)
  have hcov : (f : ℝ) ≤ ∑ j ∈ J, (g j : ℝ) := by exact_mod_cast hcover
  obtain ⟨j, hj, hshare⟩ := exists_frame_ge_weight_share J η (fun j => (g j : ℝ)) f hJ hη hcov
  have hratio : (f : ℝ) ≤ (g j : ℝ) / η j :=
    (le_div_iff₀ (hηpos j hj)).2 (by simpa [mul_comm] using hshare)
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg f) hratio (hα j hj).1.le
  rw [Real.div_rpow (Nat.cast_nonneg _) (hηpos j hj).le (α j)] at hp
  exact (exp_one_mul_log_le_rpow_div hf1 (hα j hj).1 (hα j hj).2).trans
    ((div_le_div_of_nonneg_right hp (hden j hj).le).trans
      (Finset.single_le_sum hnonneg hj))

/-- Literal overlapping frame coverage gives the incidence-count hypothesis. -/
theorem divisor_count_le_sum_of_frame_cover (F J : Finset ℕ)
    (G : ℕ → Finset ℕ) (hcover : F ⊆ J.biUnion G) (n : ℕ) :
    (F.filter (fun a => a ∣ n)).card ≤
      ∑ j ∈ J, ((G j).filter (fun a => a ∣ n)).card := by
  classical
  have hsub : F.filter (fun a => a ∣ n) ⊆
      J.biUnion (fun j => (G j).filter (fun a => a ∣ n)) := by
    intro a ha
    obtain ⟨haF, had⟩ := Finset.mem_filter.mp ha
    obtain ⟨j, hj, haG⟩ := Finset.mem_biUnion.mp (hcover haF)
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨haG, had⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- Actual finite divisor-majorant costs bound every finite logarithmic mean.
No logarithmic bound or periodic-limit assertion is assumed. -/
theorem finite_cover_log_mean_le_cost
    (J : Finset ℕ) (η α : ℕ → ℝ) (f : ℕ → ℕ) (g : ℕ → ℕ → ℕ)
    (D : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (X : ℕ)
    (hX : 0 < X) (hJ : J.Nonempty)
    (hη : ∑ j ∈ J, η j = 1) (hηpos : ∀ j ∈ J, 0 < η j)
    (hα : ∀ j ∈ J, 0 < α j ∧ α j ≤ 1)
    (hD : ∀ j ∈ J, ∀ d ∈ D j, 0 < d)
    (hc : ∀ j ∈ J, ∀ d ∈ D j, 0 ≤ c j d)
    (hcover : ∀ n, f n ≤ ∑ j ∈ J, g j n)
    (hmaj : ∀ j ∈ J, ∀ n, 0 < n →
      (g j n : ℝ) ^ α j ≤ ∑ d ∈ (D j).filter (fun d => d ∣ n), c j d) :
    (∑ n ∈ Finset.Icc 1 X, Real.exp 1 * Real.log (f n : ℝ)) / X ≤
      ∑ j ∈ J, divisorMajorantCost (D j) (c j) /
        (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
  have hden : ∀ j ∈ J, 0 < (2 : ℝ) ^ α j - 1 := by
    intro j hj
    have hh := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (hα j hj).1
    linarith
  have hpoint := fun n => finite_cover_log_pointwise J η α (f n)
    (fun j => g j n) hJ hη hηpos hα (hcover n)
  calc
    _ ≤ (∑ n ∈ Finset.Icc 1 X, ∑ j ∈ J,
        (g j n : ℝ) ^ α j / (η j ^ α j) / ((2 : ℝ) ^ α j - 1)) / X :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun n _ => hpoint n))
        (Nat.cast_nonneg X)
    _ = ∑ j ∈ J, ((∑ n ∈ Finset.Icc 1 X, (g j n : ℝ) ^ α j) / X) /
        (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_div, ← Finset.sum_div]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have hav := cesaro_le_divisorMajorantCost (fun n => (g j n : ℝ) ^ α j)
        (D j) (c j) X hX (hD j hj) (hc j hj)
        (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (hmaj j hj)
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hav (Real.rpow_pos_of_pos (hηpos j hj) _).le)
        (hden j hj).le

/-- The finite-family first-logarithmic-moment obstruction for literal
finite supports and overlapping finite divisor frames. -/
theorem finite_frame_cover_log_mean_le_cost
    (F J : Finset ℕ) (G D : ℕ → Finset ℕ) (η α : ℕ → ℝ)
    (c : ℕ → ℕ → ℝ) (X : ℕ) (hX : 0 < X) (hJ : J.Nonempty)
    (hη : ∑ j ∈ J, η j = 1) (hηpos : ∀ j ∈ J, 0 < η j)
    (hα : ∀ j ∈ J, 0 < α j ∧ α j ≤ 1)
    (hD : ∀ j ∈ J, ∀ d ∈ D j, 0 < d)
    (hc : ∀ j ∈ J, ∀ d ∈ D j, 0 ≤ c j d)
    (hcover : F ⊆ J.biUnion G)
    (hmaj : ∀ j ∈ J, ∀ n, 0 < n →
      (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j ≤
        ∑ d ∈ (D j).filter (fun d => d ∣ n), c j d) :
    (∑ n ∈ Finset.Icc 1 X,
      Real.exp 1 * Real.log ((F.filter (fun a => a ∣ n)).card : ℝ)) / X ≤
      ∑ j ∈ J, divisorMajorantCost (D j) (c j) /
        (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
  exact finite_cover_log_mean_le_cost J η α
    (fun n => (F.filter (fun a => a ∣ n)).card)
    (fun j n => ((G j).filter (fun a => a ∣ n)).card)
    D c X hX hJ hη hηpos hα hD hc
    (fun n => divisor_count_le_sum_of_frame_cover F J G hcover n) hmaj

end ErdosProblems.Erdos257.PaperCompleteR8
end
