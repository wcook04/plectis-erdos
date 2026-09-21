import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# First-entry strips in a nested finite family

A point contributes to every later set after its first appearance. This
finite identity separates cancellation in the common interior from the
three moving boundary strips of a cubic difference.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators

def entryStrip {α : Type*} [DecidableEq α] (T : ℕ → Finset α) : ℕ → Finset α
  | 0 => T 0
  | n + 1 => T (n + 1) \ T n

theorem sum_entryStrips {α : Type*} [DecidableEq α]
    (T : ℕ → Finset α) (hT : Monotone T) (f : α → ℝ) (n : ℕ) :
    (∑ s ∈ Finset.range (n + 1), ∑ x ∈ entryStrip T s, f x) =
      ∑ x ∈ T n, f x := by
  induction n with
  | zero => simp [entryStrip]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simpa only [entryStrip, add_comm] using
      (Finset.sum_sdiff (f := f) (hT (Nat.le_succ n)))

/-- Exact first-entry decomposition with the suffix starting at the entry index. -/
theorem nested_finite_strip_decomposition {α : Type*} [DecidableEq α]
    (T : ℕ → Finset α) (hT : Monotone T) (F : ℕ → α → ℝ) (σ : ℕ) :
    (∑ ν ∈ Finset.range (σ + 1), ∑ x ∈ T ν, F ν x) =
      ∑ s ∈ Finset.range (σ + 1), ∑ x ∈ entryStrip T s,
        ∑ ν ∈ Finset.Icc s σ, F ν x := by
  calc
    (∑ ν ∈ Finset.range (σ + 1), ∑ x ∈ T ν, F ν x) =
        ∑ ν ∈ Finset.range (σ + 1), ∑ s ∈ Finset.range (ν + 1),
          ∑ x ∈ entryStrip T s, F ν x := by
      apply Finset.sum_congr rfl
      intro ν _
      exact (sum_entryStrips T hT (F ν) ν).symm
    _ = ∑ s ∈ Finset.range (σ + 1), ∑ ν ∈ Finset.Ico s (σ + 1),
        ∑ x ∈ entryStrip T s, F ν x := by
      simpa only [Nat.Ico_zero_eq_range] using
        (Finset.sum_Ico_Ico_comm 0 (σ + 1)
          (fun s ν => ∑ x ∈ entryStrip T s, F ν x)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      simp only [Finset.Ico_add_one_right_eq_Icc]

/-- With constant point weights, the cubic interior cancels and the three
boundary-strip coefficients are exactly minus one, two, minus one. -/
theorem cubic_difference_boundary_strips {α : Type*} [DecidableEq α]
    (T : ℕ → Finset α) (hT : Monotone T) (w : α → ℝ) :
    (∑ x ∈ T 0, w x) - 3 * (∑ x ∈ T 1, w x) +
        3 * (∑ x ∈ T 2, w x) - (∑ x ∈ T 3, w x) =
      -(∑ x ∈ T 1 \ T 0, w x) + 2 * (∑ x ∈ T 2 \ T 1, w x) -
        (∑ x ∈ T 3 \ T 2, w x) := by
  have h01 := Finset.sum_sdiff (f := w) (hT (by decide : (0 : ℕ) ≤ 1))
  have h12 := Finset.sum_sdiff (f := w) (hT (by decide : (1 : ℕ) ≤ 2))
  have h23 := Finset.sum_sdiff (f := w) (hT (by decide : (2 : ℕ) ≤ 3))
  linarith

#print axioms nested_finite_strip_decomposition
#print axioms cubic_difference_boundary_strips

end ErdosProblems.Erdos269.PaperCompleteR20
