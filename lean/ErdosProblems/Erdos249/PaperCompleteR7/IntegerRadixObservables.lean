import ErdosProblems.Erdos249.PaperCompleteR7.RationalObservableClassification

/-!
# Integer-radix totient observables

This module generalizes the analytic part of the bounded-residue theorem from
binary denominators to any integer radix at least two. The original binary
declarations remain the public compatibility interface.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables

open scoped BigOperators

/-- The positive-index totient observable in an integer radix. -/
noncomputable def positiveRadixValue (B : ℕ) (f : ℕ → ℚ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, (f (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1)

/-- The geometric series controlling every bounded radix observable. -/
theorem summable_radix_geometric (B : ℕ) (hB : 2 ≤ B) :
    Summable (fun n : ℕ => (1 / (B : ℝ)) ^ n) := by
  have hBreal : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  exact summable_geometric_of_lt_one (by positivity)
    (by rw [div_lt_one (by linarith : (0 : ℝ) < B)]; linarith)

/-- The same geometric series has its usual closed value. -/
theorem tsum_radix_geometric (B : ℕ) (hB : 2 ≤ B) :
    (∑' n : ℕ, (1 / (B : ℝ)) ^ n) = (B : ℝ) / ((B : ℝ) - 1) := by
  have hBreal : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hpos : (0 : ℝ) < (B : ℝ) := by linarith
  rw [tsum_geometric_of_lt_one (by positivity)
    (by rw [div_lt_one hpos]; linarith)]
  field_simp

/-- A uniformly bounded integer word has a convergent radix value. -/
theorem summable_radix_terms (B : ℕ) (hB : 2 ≤ B)
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C) :
    Summable (fun n : ℕ => (a n : ℝ) / (B : ℝ) ^ n) := by
  have hgeo : Summable (fun n : ℕ => C * (1 / (B : ℝ)) ^ n) :=
    (summable_radix_geometric B hB).mul_left C
  apply Summable.of_norm_bounded (g := fun n : ℕ => C * (1 / (B : ℝ)) ^ n)
    hgeo
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (B : ℝ) ^ n)]
  rw [div_pow]
  simp only [one_pow, mul_one_div]
  exact div_le_div_of_nonneg_right (hC n) (by positivity)

#print axioms tsum_radix_geometric
#print axioms summable_radix_terms

end ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables
