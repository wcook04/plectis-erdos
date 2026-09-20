import Mathlib

/-!
# Erdős 243: cutoff-weight construction, Tonelli core

This file formalises the nonnegative double-sum calculation at the heart of
short-paper `res:weights`.  Given integer cutoffs `X k`, the cutoff weight
at height `x` is

`sum_k 1_{x <= X k} / X k`.

The main theorem identifies its weighted mass exactly with the sum of the
normalised prefix masses.  Hence any summable sequence of cutoff-density
bounds produces a finite weighted mass.  Extended nonnegative reals retain
the paper's a-priori possibility that a prefix mass is infinite.

This is the constructive Tonelli seam, not yet the whole paper lemma: selecting
cutoffs from the liminf hypothesis, converting the weight to a finite real
function on `[1, infinity)`, and proving its improper integral diverges remain
separate steps.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open scoped BigOperators ENNReal

/-- One cutoff contribution to the weight at the integer height `x`. -/
def cutoffAtom (X : ℕ → ℕ) (k x : ℕ) : ℝ≥0∞ :=
  if x ≤ X k then (X k : ℝ≥0∞)⁻¹ else 0

/-- The cutoff weight `sum_k 1_{x <= X_k} / X_k`. -/
def cutoffWeight (X : ℕ → ℕ) (x : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, cutoffAtom X k x

/-- Prefix mass of the points whose integer locations are at most `Y`.
The value lies in `ENNReal`, so no local finiteness is assumed. -/
def cutoffPrefixMass (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (Y : ℕ) : ℝ≥0∞ :=
  ∑' j : ℕ, if u j ≤ Y then w j else 0

/-- Increasing the height can only decrease the cutoff weight. -/
theorem cutoffWeight_antitone (X : ℕ → ℕ) : Antitone (cutoffWeight X) := by
  intro x y hxy
  apply ENNReal.tsum_le_tsum
  intro k
  unfold cutoffAtom
  by_cases hy : y ≤ X k
  · have hx : x ≤ X k := hxy.trans hy
    simp [hy, hx]
  · simp [hy]

/-- Exact Tonelli identity for the cutoff construction.  This is valid even
when either side is infinite. -/
theorem weighted_cutoffWeight_eq_normalized_prefixMass
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (X : ℕ → ℕ) :
    (∑' j : ℕ, w j * cutoffWeight X (u j)) =
      ∑' k : ℕ, cutoffPrefixMass u w (X k) * (X k : ℝ≥0∞)⁻¹ := by
  calc
    (∑' j : ℕ, w j * cutoffWeight X (u j)) =
        ∑' j : ℕ, ∑' k : ℕ, w j * cutoffAtom X k (u j) := by
      apply tsum_congr
      intro j
      rw [cutoffWeight, ← ENNReal.tsum_mul_left]
    _ = ∑' k : ℕ, ∑' j : ℕ, w j * cutoffAtom X k (u j) :=
      ENNReal.tsum_comm
    _ = ∑' k : ℕ, cutoffPrefixMass u w (X k) * (X k : ℝ≥0∞)⁻¹ := by
      apply tsum_congr
      intro k
      rw [cutoffPrefixMass, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro j
      unfold cutoffAtom
      by_cases hj : u j ≤ X k <;> simp [hj]

/-- A summable sequence of normalised prefix-mass bounds controls the full
weighted mass of the cutoff construction. -/
theorem weighted_cutoffWeight_le_of_prefixMass
    (u : ℕ → ℕ) (w b : ℕ → ℝ≥0∞) (X : ℕ → ℕ)
    (hX : ∀ k, 0 < X k)
    (hmass : ∀ k, cutoffPrefixMass u w (X k) ≤ b k * (X k : ℝ≥0∞)) :
    (∑' j : ℕ, w j * cutoffWeight X (u j)) ≤ ∑' k : ℕ, b k := by
  rw [weighted_cutoffWeight_eq_normalized_prefixMass]
  apply ENNReal.tsum_le_tsum
  intro k
  calc
    cutoffPrefixMass u w (X k) * (X k : ℝ≥0∞)⁻¹ ≤
        (b k * (X k : ℝ≥0∞)) * (X k : ℝ≥0∞)⁻¹ :=
      mul_le_mul_right' (hmass k) _
    _ = b k := by
      rw [mul_assoc, ENNReal.mul_inv_cancel]
      · simp
      · exact_mod_cast (hX k).ne'
      · simp

/-- The geometric cutoff choice used in the paper gives weighted mass at most
one as soon as the `k`-th normalised prefix mass is at most `2^-(k+1)`. -/
theorem weighted_cutoffWeight_le_one_of_geometric_prefixMass
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (X : ℕ → ℕ)
    (hX : ∀ k, 0 < X k)
    (hmass : ∀ k, cutoffPrefixMass u w (X k) ≤
      ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ * (X k : ℝ≥0∞)) :
    (∑' j : ℕ, w j * cutoffWeight X (u j)) ≤ 1 := by
  have hle := weighted_cutoffWeight_le_of_prefixMass u w
    (fun k => ((2 : ℝ≥0∞) ^ (k + 1))⁻¹) X hX hmass
  calc
    (∑' j : ℕ, w j * cutoffWeight X (u j)) ≤
        ∑' k : ℕ, ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ := hle
    _ = 1 := by
      simp_rw [ENNReal.inv_pow]
      rw [ENNReal.tsum_geometric_add_one]
      norm_num [ENNReal.one_sub_inv_two]
      exact ENNReal.inv_mul_cancel (by norm_num) (by simp)

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.cutoffWeight_antitone
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.weighted_cutoffWeight_eq_normalized_prefixMass
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.weighted_cutoffWeight_le_one_of_geometric_prefixMass

end ErdosProblems.Erdos243.PaperCompleteR20
