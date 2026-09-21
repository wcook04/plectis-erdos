-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Tactic

/-!
# Factorial carries and the first derivative

These finite identities retain the endpoint terms. Passing to infinite sums,
the arbitrary-order jet construction, Hausdorff dimension and the sharp
interior threshold are ordinary arguments in the synthesis paper; they are
not asserted to be formalised here.
-/

namespace ErdosProblems.Synthesis.FactorialJet

open Finset

/-- The factorial carry which preserves the value of the infinite EGF at one. -/
def carry (b : ℕ → ℚ) (n : ℕ) : ℚ := (n + 1) * b n - b (n + 1)

theorem carry_scaled (b : ℕ → ℚ) (n : ℕ) :
    carry b n / (n + 1).factorial =
      b n / n.factorial - b (n + 1) / (n + 1).factorial := by
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnp : (n + 1 : ℚ) ≠ 0 := by positivity
  simp only [carry, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

/-- Finite value identity, with its nonzero endpoint term. -/
theorem sum_carry (b : ℕ → ℚ) (N : ℕ) :
    ∑ n ∈ range N, carry b n / (n + 1).factorial =
      b 0 - b N / N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih, carry_scaled]
      ring

/-- Finite first-derivative identity. Its extra sum is the independent
quantity made available by a carry, after the endpoint tends to zero. -/
theorem sum_weighted_carry (b : ℕ → ℚ) (N : ℕ) :
    ∑ n ∈ range N, (n + 1) * (carry b n / (n + 1).factorial) =
      (∑ n ∈ range N, b n / n.factorial) - N * (b N / N.factorial) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih, sum_range_succ, carry_scaled]
      push_cast
      ring

/-- Integer carries retain divisibility; no convergence premise is used. -/
theorem dvd_carry (b : ℕ → ℤ) (q : ℤ) (n : ℕ)
    (h : q ∣ b n) (h' : q ∣ b (n + 1)) :
    q ∣ (n + 1 : ℤ) * b n - b (n + 1) :=
  dvd_sub (dvd_mul_of_dvd_right h _) h'

end ErdosProblems.Synthesis.FactorialJet
