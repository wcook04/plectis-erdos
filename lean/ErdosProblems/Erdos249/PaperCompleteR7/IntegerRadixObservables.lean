import ErdosProblems.Erdos249.PaperCompleteR7.RationalObservableClassification

/-!
# Integer-radix totient observables

This module generalizes the analytic part of the bounded-residue theorem from
binary denominators to any integer radix at least two. The original binary
declarations remain the public compatibility interface.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables

open scoped BigOperators
open ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables

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

/-- A finite-residue observable has a convergent positive-index radix value. -/
theorem summable_positive_terms (B : ℕ) (hB : 2 ≤ B)
    (m : ℕ) (hm : 0 < m) (f : ℕ → ℚ) :
    Summable (fun n : ℕ =>
      (f (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1)) := by
  let C : ℝ := ∑ i ∈ Finset.range m, |(f i : ℝ)|
  have hbound (n : ℕ) : |(f (Nat.totient (n + 1) % m) : ℝ)| ≤ C :=
    Finset.single_le_sum (fun i _ => abs_nonneg (f i : ℝ))
      (Finset.mem_range.mpr (Nat.mod_lt _ hm))
  have hgeo : Summable (fun n : ℕ => (C / (B : ℝ)) * (1 / (B : ℝ)) ^ n) :=
    (summable_radix_geometric B hB).mul_left _
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (C / (B : ℝ)) * (1 / (B : ℝ)) ^ n) hgeo ?_
  intro n
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  calc
    ‖(f (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1)‖
        = |(f (Nat.totient (n + 1) % m) : ℝ)| / (B : ℝ) ^ (n + 1) := by
          simp only [Real.norm_eq_abs, abs_div,
            abs_of_pos (pow_pos hBpos (n + 1))]
    _ ≤ C / (B : ℝ) ^ (n + 1) :=
      div_le_div_of_nonneg_right (hbound n) (by positivity)
    _ = (C / (B : ℝ)) * (1 / (B : ℝ)) ^ n := by
      rw [pow_succ, div_pow]
      field_simp
      simp

/-- Exact rational case of the all-integer-base observable classification. -/
theorem positiveRadixValue_eq_of_even_constant
    (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : 1 ≤ k)
    (f : ℕ → ℚ) (c : ℚ)
    (hc : ∀ r, r < 2 ^ k → r % 2 = 0 → f r = c) :
    positiveRadixValue B f (2 ^ k) =
      ((B : ℝ) + 1) / (B : ℝ) ^ 2 * (f 1 : ℝ) +
        (c : ℝ) / ((B : ℝ) ^ 2 * ((B : ℝ) - 1)) := by
  have hBreal : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hB0 : (B : ℝ) ≠ 0 := by linarith
  have hB1 : (B : ℝ) - 1 ≠ 0 := by linarith
  have hm : 0 < 2 ^ k := by positivity
  have hm2 : 1 < 2 ^ k := by
    have h := two_le_two_pow hk
    omega
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ =>
      (f (Nat.totient (n + 1) % 2 ^ k) : ℝ) / (B : ℝ) ^ (n + 1)) 2
    (summable_positive_terms B hB (2 ^ k) hm f)
  have htail :
      (∑' n : ℕ,
        (f (Nat.totient (n + 2 + 1) % 2 ^ k) : ℝ) /
          (B : ℝ) ^ (n + 2 + 1)) =
        (c : ℝ) / ((B : ℝ) ^ 2 * ((B : ℝ) - 1)) := by
    calc
      (∑' n : ℕ,
          (f (Nat.totient (n + 2 + 1) % 2 ^ k) : ℝ) /
            (B : ℝ) ^ (n + 2 + 1))
          = ∑' n : ℕ, ((c : ℝ) / (B : ℝ) ^ 3) *
              (1 / (B : ℝ)) ^ n := by
                apply tsum_congr
                intro n
                rw [hc _ (Nat.mod_lt _ hm)
                  (totient_mod_two_pow_even hk (by omega))]
                rw [show n + 2 + 1 = 3 + n by omega, pow_add, div_pow]
                field_simp
                ring
      _ = ((c : ℝ) / (B : ℝ) ^ 3) *
          ((B : ℝ) / ((B : ℝ) - 1)) := by
            rw [tsum_mul_left, tsum_radix_geometric B hB]
      _ = (c : ℝ) / ((B : ℝ) ^ 2 * ((B : ℝ) - 1)) := by
            field_simp
  have hprefix :
      (∑ n ∈ Finset.range 2,
        (f (Nat.totient (n + 1) % 2 ^ k) : ℝ) / (B : ℝ) ^ (n + 1)) =
      (f 1 : ℝ) / (B : ℝ) + (f 1 : ℝ) / (B : ℝ) ^ 2 := by
    norm_num [Finset.sum_range_succ, Nat.mod_eq_of_lt hm2,
      show Nat.totient 2 = 1 by decide]
  rw [htail, hprefix] at hsplit
  unfold positiveRadixValue
  rw [← hsplit]
  field_simp

#print axioms tsum_radix_geometric
#print axioms summable_radix_terms
#print axioms summable_positive_terms
#print axioms positiveRadixValue_eq_of_even_constant

end ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables
