/- Copyright (c) 2026 Will Cook. Released under Apache 2.0. -/
import Mathlib
/-! Independent expanded statement and elementary proof of the policy contract.
No corpus definition appears in its type and no statement hole is used.
This is a development assurance unit, not a new registered problem result. -/
open Filter Topology Finset
namespace ErdosProblems.ExternalVerification
theorem feedbackPolicy_preserves_sum
    {A M d : ℕ → ℕ} {w lo hi : ℕ → ℝ} {y : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hlo : ∀ n, 0 ≤ lo n)
    (hvanish : Tendsto hi atTop (𝓝 0))
    (hstep : ∀ n, d n ≤ A n ∧
      (M n : ℤ) ∣ ((∑ i ∈ range n, d i : ℕ) : ℤ) + (d n : ℤ) ∧
      lo (n + 1) ≤ (y - ∑ i ∈ range n, (d i : ℝ) * w i) - (d n : ℝ) * w n ∧
      (y - ∑ i ∈ range n, (d i : ℝ) * w i) - (d n : ℝ) * w n ≤ hi (n + 1)) :
    (∀ n, d n ≤ A n) ∧
      (∀ n, (M n : ℤ) ∣ ((∑ i ∈ range (n + 1), d i : ℕ) : ℤ)) ∧
      HasSum (fun n => (d n : ℝ) * w n) y := by
  have hb : ∀ n, 0 ≤ y - ∑ i ∈ range (n + 1), (d i : ℝ) * w i ∧
      y - ∑ i ∈ range (n + 1), (d i : ℝ) * w i ≤ hi (n + 1) := by
    intro n
    have hs := hstep n
    rw [sum_range_succ]
    constructor <;> linarith [hlo (n + 1), hs.2.2.1, hs.2.2.2]
  refine ⟨fun n => (hstep n).1, ?_, ?_⟩
  · intro n
    simpa only [sum_range_succ, Nat.cast_add] using (hstep n).2.1
  · have hr : Tendsto
        (fun n => y - ∑ i ∈ range (n + 1), (d i : ℝ) * w i) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hvanish.comp (tendsto_add_atTop_nat 1))
        (fun n => (hb n).1) (fun n => (hb n).2)
    have ht : Tendsto (fun n => y - (y - ∑ i ∈ range (n + 1), (d i : ℝ) * w i))
        atTop (𝓝 (y - 0)) := tendsto_const_nhds.sub hr
    have ht' : Tendsto (fun n => ∑ i ∈ range (n + 1), (d i : ℝ) * w i)
        atTop (𝓝 y) := by
      simpa only [sub_sub_cancel, sub_zero] using ht
    rw [hasSum_iff_tendsto_nat_of_nonneg
      (fun n => mul_nonneg (Nat.cast_nonneg _) (hw n))]
    exact (tendsto_add_atTop_iff_nat 1).mp ht'
end ErdosProblems.ExternalVerification
