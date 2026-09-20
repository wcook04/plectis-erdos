import Mathlib

/-!
# Erdős 243: integer finite differences for the cubic-rate bridge

This file isolates the discrete integrality step in the proof of the paper's
cubic-rate theorem.  Once the analytic comparison with the rising-factorial
model shows that a sufficiently high finite difference tends to zero, its
integer values force it to vanish identically on a tail.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

/-- The forward difference of an integer sequence. -/
def intForwardDiff (u : ℕ → ℤ) (n : ℕ) : ℤ := u (n + 1) - u n

/-- Iterated integer forward differences. -/
def iterIntForwardDiff : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, u => u
  | k + 1, u => intForwardDiff (iterIntForwardDiff k u)

@[simp] theorem iterIntForwardDiff_zero (u : ℕ → ℤ) :
    iterIntForwardDiff 0 u = u := rfl

@[simp] theorem iterIntForwardDiff_succ (k : ℕ) (u : ℕ → ℤ) :
    iterIntForwardDiff (k + 1) u = intForwardDiff (iterIntForwardDiff k u) := rfl

/-- An integer sequence whose real casts tend to zero is eventually zero. -/
theorem eventually_eq_zero_of_intCast_tendsto_zero
    (u : ℕ → ℤ)
    (h : Tendsto (fun n => (u n : ℝ)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, u n = 0 := by
  have hlo : ∀ᶠ n in atTop, (-1 : ℝ) < (u n : ℝ) :=
    (tendsto_order.1 h).1 (-1) (by norm_num)
  have hhi : ∀ᶠ n in atTop, (u n : ℝ) < 1 :=
    (tendsto_order.1 h).2 1 (by norm_num)
  filter_upwards [hlo, hhi] with n hnlo hnhi
  have hnlo' : (-1 : ℤ) < u n := by exact_mod_cast hnlo
  have hnhi' : u n < (1 : ℤ) := by exact_mod_cast hnhi
  omega

/-- The exact integrality conclusion used after the analytic finite-difference
estimate in the cubic-rate argument. -/
theorem eventually_iterIntForwardDiff_eq_zero
    (u : ℕ → ℤ) (k : ℕ)
    (h : Tendsto (fun n => (iterIntForwardDiff k u n : ℝ)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, iterIntForwardDiff k u n = 0 :=
  eventually_eq_zero_of_intCast_tendsto_zero (iterIntForwardDiff k u) h

/-- A vanishing forward difference makes an integer sequence constant on a
tail. -/
theorem eventually_constant_of_forwardDiff_eventually_zero
    (u : ℕ → ℤ) (h : ∀ᶠ n in atTop, intForwardDiff u n = 0) :
    ∃ N : ℕ, ∀ n, N ≤ n → u n = u N := by
  obtain ⟨N, hN⟩ := (eventually_atTop.1 h)
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => simp
  | succ d ih =>
      have hz := hN (N + d) (by omega)
      simp only [intForwardDiff] at hz
      have hstep : u (N + d + 1) = u (N + d) := by omega
      rw [show N + (d + 1) = N + d + 1 by omega, hstep, ih (by omega)]

/-- If the fourth integer difference tends to zero, the third difference is
constant on a tail.  This is the first exact algebraic output of the paper's
integer finite-difference extraction. -/
theorem third_difference_eventually_constant_of_fourth_tendsto_zero
    (C : ℕ → ℤ)
    (h : Tendsto (fun n => (iterIntForwardDiff 4 C n : ℝ)) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N := by
  apply eventually_constant_of_forwardDiff_eventually_zero
  simpa [iterIntForwardDiff] using eventually_iterIntForwardDiff_eq_zero C 4 h

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.eventually_eq_zero_of_intCast_tendsto_zero
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.third_difference_eventually_constant_of_fourth_tendsto_zero

end ErdosProblems.Erdos243.PaperCompleteR20
