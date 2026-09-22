import ErdosProblems.Erdos243.PaperCompleteR20.CutoffWeightAnalytic
import Mathlib.Order.LiminfLimsup

/-!
# Erdős 243: literal lower density and partial summation

This file connects the paper's literal lower-limit hypothesis to the geometric
cutoff selector and records the finite Abel identity used in the converse of
`res:weights`.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

/-- The literal lower density from `res:weights`, kept in `ENNReal` so prefix
masses are allowed a priori to be infinite. -/
def PrefixLowerDensityZero (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) : Prop :=
  Filter.liminf (fun X : ℕ => cutoffPrefixMass u w X / (X : ℝ≥0∞)) atTop = 0

/-- A zero lower limit supplies the cofinal geometric cutoffs used by the
constructive proof. -/
theorem geometricPrefixVanish_of_liminf_eq_zero
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞)
    (hlim : PrefixLowerDensityZero u w) : GeometricPrefixVanish u w := by
  intro k N
  let δ : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ (k + 1))⁻¹
  have hδ : 0 < δ := by
    dsimp [δ]
    exact ENNReal.inv_pos.mpr (by simp)
  by_contra hnone
  push_neg at hnone
  have hevent : ∀ᶠ Y : ℕ in atTop,
      δ ≤ cutoffPrefixMass u w Y / (Y : ℝ≥0∞) := by
    filter_upwards [eventually_ge_atTop (max N 1)] with Y hY
    have hNY : N ≤ Y := (le_max_left N 1).trans hY
    have hYpos : 0 < Y := by omega
    have hnot : ¬ cutoffPrefixMass u w Y / (Y : ℝ≥0∞) ≤ δ := by
      intro hratio
      exact (not_le_of_gt (hnone Y hNY))
        ((ENNReal.div_le_iff (by exact_mod_cast hYpos.ne') (by simp)).mp hratio)
    exact (not_le.mp hnot).le
  have hle : δ ≤ Filter.liminf
      (fun Y : ℕ => cutoffPrefixMass u w Y / (Y : ℝ≥0∞)) atTop :=
    Filter.le_liminf_of_le (by isBoundedDefault) hevent
  rw [hlim] at hle
  exact (not_lt_of_ge hle) hδ

/-- Literal lower density zero implies the full forward admissible-weight
conclusion of the paper. -/
theorem exists_admissible_real_weight_of_liminf_eq_zero
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0) (hu : ∀ j, 0 < u j)
    (hlim : PrefixLowerDensityZero u (fun j => (w j : ℝ≥0∞))) :
    ∃ f : ℝ → ℝ,
      AntitoneOn f (Ici 1) ∧
      (∀ t : ℝ, 1 ≤ t → 0 ≤ f t) ∧
      PaperCompleteR11.IntegralUnbounded f ∧
      Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ)) :=
  exists_admissible_real_weight_of_geometricPrefixVanish u w hu
    (geometricPrefixVanish_of_liminf_eq_zero u _ hlim)

/-- Prefix sum of a nonnegative sequence through index `n`. -/
def finitePrefix (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (n + 1), a r

/-- Finite Abel summation in the exact endpoint convention needed for the
reverse implication. -/
theorem finite_partial_summation (a f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n * f n) =
      finitePrefix a N * f N +
        ∑ n ∈ Finset.range N, finitePrefix a n * (f n - f (n + 1)) := by
  induction N with
  | zero => simp [finitePrefix]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [finitePrefix, Finset.sum_range_succ]
      ring

/-- The elementary telescoping identity underlying the lower bound in the
paper's converse argument. -/
theorem weighted_difference_telescopes (f : ℕ → ℝ) (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) * f N +
        ∑ n ∈ Finset.range N, (n + 1 : ℕ) * (f n - f (n + 1)) =
      ∑ n ∈ Finset.range (N + 1), f n := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      norm_num at ih ⊢
      linarith

/-- A uniform linear lower bound for prefix mass forces every finite weighted
partial sum to dominate the corresponding samples of a nonnegative antitone
weight.  This is the quantitative core of the reverse implication. -/
theorem linear_prefix_forces_sample_bound
    (a f : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ n, 0 ≤ a n) (hf : Antitone f) (hfnn : ∀ n, 0 ≤ f n)
    (hprefix : ∀ n, c * (n + 1) ≤ finitePrefix a n) (N : ℕ) :
    c * (∑ n ∈ Finset.range (N + 1), f n) ≤
      ∑ n ∈ Finset.range (N + 1), a n * f n := by
  rw [finite_partial_summation, ← weighted_difference_telescopes f N,
    mul_add, Finset.mul_sum]
  apply add_le_add
  · simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using
      mul_le_mul_of_nonneg_right (hprefix N) (hfnn N)
  · apply Finset.sum_le_sum
    intro n hn
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using
      mul_le_mul_of_nonneg_right (hprefix n) (sub_nonneg.mpr (hf (Nat.le_succ n)))

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.geometricPrefixVanish_of_liminf_eq_zero
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.finite_partial_summation
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.weighted_difference_telescopes

end ErdosProblems.Erdos243.PaperCompleteR20
