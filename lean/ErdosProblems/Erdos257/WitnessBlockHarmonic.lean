import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal mass of the cofactors congruent to one

Grouping each positive integer with the first member of its length-`Q`
block gives an explicit finite lower bound for the progression `1 mod Q`.
-/

noncomputable section
namespace ErdosProblems.Erdos257
open Finset

/-- Reciprocal mass of the positive progression terms at most `N` (`N ≥ 1`). -/
def progressionHarmonicMass (Q N : ℕ) : ℝ :=
  ∑ j ∈ range ((N - 1) / Q + 1), (1 : ℝ) / (Q * j + 1)

theorem quotient_fiber_card_le (Q N j : ℕ) (hQ : 0 < Q) :
    ((range N).filter (fun n => n / Q = j)).card ≤ Q := by
  have hsub : (range N).filter (fun n => n / Q = j) ⊆ Ico (j * Q) (j * Q + Q) := by
    intro n hn
    have hj := (mem_filter.mp hn).2
    have hmod := Nat.mod_lt n hQ
    have hid := Nat.mod_add_div n Q
    rw [hj] at hid
    rw [Nat.mul_comm Q j] at hid
    exact mem_Ico.mpr (by omega)
  simpa using card_le_card hsub

/-- Each denominator belongs to a block of at most `Q` denominators and is
at least the first denominator in that block. -/
theorem harmonicMass_le_mul_progression (Q N : ℕ) (hQ : 0 < Q) :
    (∑ n ∈ range N, (1 : ℝ) / (n + 1)) ≤
      (Q : ℝ) * progressionHarmonicMass Q N := by
  classical
  have hmap : ∀ n ∈ range N, n / Q ∈ range ((N - 1) / Q + 1) := by
    intro n hn
    have hle : n ≤ N - 1 := by have := mem_range.mp hn; omega
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hle))
  calc
    (∑ n ∈ range N, (1 : ℝ) / (n + 1)) ≤
        ∑ n ∈ range N, (1 : ℝ) / (Q * ((n / Q : ℕ) : ℝ) + 1) := by
      apply sum_le_sum
      intro n hn
      apply one_div_le_one_div_of_le (by positivity)
      have hd := Nat.mul_div_le n Q
      exact_mod_cast (by omega : Q * (n / Q) + 1 ≤ n + 1)
    _ = ∑ j ∈ range ((N - 1) / Q + 1),
        ∑ n ∈ (range N).filter (fun n => n / Q = j),
          (1 : ℝ) / (Q * j + 1) := (sum_fiberwise_of_maps_to' hmap _).symm
    _ ≤ ∑ j ∈ range ((N - 1) / Q + 1),
        (Q : ℝ) * ((1 : ℝ) / (Q * j + 1)) := by
      apply sum_le_sum
      intro j hj
      simp only [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast quotient_fiber_card_le Q N j hQ
      · positivity
    _ = (Q : ℝ) * progressionHarmonicMass Q N := by
      rw [progressionHarmonicMass, mul_sum]

/-- The real harmonic mass at `2^r` is at least `r log 2`. -/
theorem log_two_mul_le_dyadic_harmonic (r : ℕ) :
    (r : ℝ) * Real.log 2 ≤ ∑ n ∈ range (2 ^ r), (1 : ℝ) / (n + 1) := by
  have hlo : Real.log ((2 : ℝ) ^ r) ≤ Real.log (((2 ^ r : ℕ) + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  rw [Real.log_pow] at hlo
  have hh := log_add_one_le_harmonic (2 ^ r)
  exact hlo.trans (by simpa [harmonic, Rat.cast_sum, one_div] using hh)

/-- An explicit lower bound uniform in the cutoff exponent. -/
theorem dyadic_progressionHarmonicMass_lower (Q r : ℕ) (hQ : 0 < Q) :
    (r : ℝ) * Real.log 2 / Q ≤ progressionHarmonicMass Q (2 ^ r) := by
  apply (div_le_iff₀ (by exact_mod_cast hQ : (0 : ℝ) < Q)).mpr
  simpa [mul_comm] using (log_two_mul_le_dyadic_harmonic r).trans
    (harmonicMass_le_mul_progression Q (2 ^ r) hQ)

/-- The elementary constant form used in the finite witness comparison. -/
theorem dyadic_progressionHarmonicMass_half_lower (Q r : ℕ) (hQ : 0 < Q) :
    (r : ℝ) / (2 * Q) ≤ progressionHarmonicMass Q (2 ^ r) := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  calc
    (r : ℝ) / (2 * Q) = ((r : ℝ) * (1 / 2)) / Q := by ring
    _ ≤ (r : ℝ) * Real.log 2 / Q := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity))
        (by positivity)
    _ ≤ _ := dyadic_progressionHarmonicMass_lower Q r hQ

#print axioms harmonicMass_le_mul_progression
#print axioms dyadic_progressionHarmonicMass_lower
#print axioms dyadic_progressionHarmonicMass_half_lower

end ErdosProblems.Erdos257
end
