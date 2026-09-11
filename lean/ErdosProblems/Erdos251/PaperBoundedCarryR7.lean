import ErdosProblems.Erdos251.PaperCoreR7
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The long record's bounded recurring-values countermodel

Target: `xr:boundedpolignac`, including the complete infinite tails.
This is NEW proof source, not a compilation receipt.

The factorial occurrences in the paper are read with their stated range
k >= 3. The distinct logarithmically growing countermodel `res:polignacfail`
is NOT claimed by this bounded construction.
-/

open Filter Topology
open scoped BigOperators

namespace ErdosProblems.Erdos251.PaperR7

noncomputable section

/-- The special indices of the printed bounded construction. -/
def IsFactorialSpike (n : ℕ) : Prop := ∃ k : ℕ, 3 ≤ k ∧ n = k.factorial

/-- U_0=4; at factorials k! with k>=3 the carry is 6, otherwise it is 4. -/
def factorialCarry (n : ℕ) : ℤ := by
  classical
  exact if IsFactorialSpike n then 6 else 4

/-- a_0 is unused. At every positive index this is 2 U_(n-1) - U_n. -/
def factorialCarryDigit (n : ℕ) : ℤ :=
  if n = 0 then 0 else 2 * factorialCarry (n - 1) - factorialCarry n

theorem factorial_spike_ge_six {n : ℕ} (hn : IsFactorialSpike n) : 6 ≤ n := by
  obtain ⟨k, hk, rfl⟩ := hn
  simpa using Nat.factorial_le hk

theorem factorial_spike_mod_two {n : ℕ} (hn : IsFactorialSpike n) : n % 2 = 0 := by
  obtain ⟨k, hk, rfl⟩ := hn
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_factorial (by decide) (by omega))

theorem not_factorial_spike_zero : ¬ IsFactorialSpike 0 := by
  intro h
  have := factorial_spike_ge_six h
  omega

theorem not_factorial_spike_predecessor {n : ℕ} (hn : IsFactorialSpike n) :
    ¬ IsFactorialSpike (n - 1) := by
  intro hp
  have h6 := factorial_spike_ge_six hn
  have h0 := factorial_spike_mod_two hn
  have h1 := factorial_spike_mod_two hp
  omega

@[simp] theorem factorialCarry_zero : factorialCarry 0 = 4 := by
  simp [factorialCarry, not_factorial_spike_zero]

theorem factorialCarry_bounds (n : ℕ) :
    (4 : ℤ) ≤ factorialCarry n ∧ factorialCarry n ≤ 6 := by
  classical
  unfold factorialCarry
  split_ifs <;> norm_num

theorem factorialCarryDigit_mem (n : ℕ) (hn : 1 ≤ n) :
    factorialCarryDigit n = 2 ∨ factorialCarryDigit n = 4 ∨ factorialCarryDigit n = 8 := by
  classical
  have hn0 : n ≠ 0 := by omega
  by_cases hs : IsFactorialSpike n
  · have hp := not_factorial_spike_predecessor hs
    left
    simp [factorialCarryDigit, hn0, factorialCarry, hs, hp]
  · by_cases hp : IsFactorialSpike (n - 1)
    · right; right
      simp [factorialCarryDigit, hn0, factorialCarry, hs, hp]
    · right; left
      simp [factorialCarryDigit, hn0, factorialCarry, hs, hp]

theorem factorialCarryDigit_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < factorialCarryDigit n := by
  rcases factorialCarryDigit_mem n hn with h | h | h <;> omega

theorem factorialCarryDigit_at_factorial (k : ℕ) (hk : 3 ≤ k) :
    factorialCarryDigit k.factorial = 2 := by
  classical
  have hs : IsFactorialSpike k.factorial := ⟨k, hk, rfl⟩
  have hp := not_factorial_spike_predecessor hs
  simp [factorialCarryDigit, Nat.factorial_ne_zero, factorialCarry, hs, hp]

/-- There is no factorial strictly between k! and (k+1)!, in particular
2 k! is not one when k >= 3. -/
theorem not_factorial_spike_twice (k : ℕ) (hk : 3 ≤ k) :
    ¬ IsFactorialSpike (2 * k.factorial) := by
  rintro ⟨j, _hj, hjeq⟩
  have hkpos : 0 < k.factorial := Nat.factorial_pos k
  have hkj : k.factorial < j.factorial := by omega
  have hjlt : k < j := (Nat.factorial_lt (by omega : 0 < k)).mp hkj
  have hstep : (k + 1).factorial ≤ j.factorial :=
    Nat.factorial_le (by omega)
  rw [Nat.factorial_succ] at hstep
  nlinarith

theorem factorialCarryDigit_at_twice_factorial (k : ℕ) (hk : 3 ≤ k) :
    factorialCarryDigit (2 * k.factorial) = 4 := by
  classical
  have hpos : 0 < k.factorial := Nat.factorial_pos k
  have hs := not_factorial_spike_twice k hk
  have hp : ¬ IsFactorialSpike (2 * k.factorial - 1) := by
    intro h
    have hm := factorial_spike_mod_two h
    omega
  simp [factorialCarryDigit, show 2 * k.factorial ≠ 0 by omega,
    factorialCarry, hs, hp]

/-- Both values occur cofinally at indices divisible by every fixed positive
t. Cofinality supplies infinitely many indices, not just one residue hit. -/
theorem factorialCarryDigit_recurring_multiples (t N : ℕ) (ht : 0 < t) :
    ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧
      factorialCarryDigit i = 2 ∧ factorialCarryDigit j = 4 := by
  let k := max 3 (max t (N + 1))
  have hk3 : 3 ≤ k := le_max_left _ _
  have hkt : t ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
  have hkN : N + 1 ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
  have hfac : k ≤ k.factorial := Nat.self_le_factorial k
  have hd : t ∣ k.factorial := Nat.dvd_factorial ht hkt
  refine ⟨k.factorial, 2 * k.factorial, by omega, by omega, hd, ?_,
    factorialCarryDigit_at_factorial k hk3,
    factorialCarryDigit_at_twice_factorial k hk3⟩
  exact dvd_mul_of_dvd_right hd 2

/-- Finite real telescope for an arbitrary shifted complete tail. -/
theorem factorialCarry_partial_telescope (N m : ℕ) :
    ∑ j ∈ Finset.range m, (factorialCarryDigit (N + j + 1) : ℝ) / 2 ^ (j + 1) =
      (factorialCarry N : ℝ) - (factorialCarry (N + m) : ℝ) / 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hd : (factorialCarryDigit (N + m + 1) : ℝ) =
        2 * (factorialCarry (N + m) : ℝ) - factorialCarry (N + m + 1) := by
      simp [factorialCarryDigit, show N + m + 1 ≠ 0 by omega]
    rw [hd, pow_succ]
    rw [show N + (m + 1) = N + m + 1 by omega]
    field_simp
    ring

/-- Boundedness removes the homogeneous recurrence term. -/
theorem factorialCarry_terminal_tendsto_zero (N : ℕ) :
    Tendsto (fun m : ℕ => (factorialCarry (N + m) : ℝ) / 2 ^ m)
      atTop (𝓝 0) := by
  have h0 : Tendsto (fun m : ℕ => (m : ℝ) ^ 0 / 2 ^ m) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num)
  have h6 : Tendsto (fun m : ℕ => (6 : ℝ) / 2 ^ m) atTop (𝓝 0) := by
    simpa using h0.const_mul 6
  apply squeeze_zero (g := fun m : ℕ => (6 : ℝ) / 2 ^ m) ?_ ?_ h6
  · intro m
    have hn : (0 : ℝ) ≤ (factorialCarry (N + m) : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 4) (factorialCarry_bounds _).1)
    exact div_nonneg hn (by positivity)
  · intro m
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (factorialCarry_bounds (N + m)).2

/-- Every actual complete tail of this countermodel equals its integer
carry. No `tsum` value for a divergent series is used. -/
theorem factorialCarry_hasSum_tail (N : ℕ) :
    HasSum (fun j : ℕ => (factorialCarryDigit (N + j + 1) : ℝ) / 2 ^ (j + 1))
      (factorialCarry N : ℝ) := by
  have hnonneg : ∀ j : ℕ, 0 ≤ (factorialCarryDigit (N + j + 1) : ℝ) / 2 ^ (j + 1) := by
    intro j
    have hp : (0 : ℝ) ≤ (factorialCarryDigit (N + j + 1) : ℝ) := by
      exact_mod_cast (factorialCarryDigit_pos _ (by omega)).le
    exact div_nonneg hp (by positivity)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hlim := (tendsto_const_nhds (x := (factorialCarry N : ℝ))).sub
    (factorialCarry_terminal_tendsto_zero N)
  simpa only [factorialCarry_partial_telescope, sub_zero] using hlim

/-- All components of long-record `xr:boundedpolignac` in one statement. -/
theorem bounded_recurring_values_countermodel :
    (∀ n, 1 ≤ n → factorialCarryDigit n = 2 ∨
      factorialCarryDigit n = 4 ∨ factorialCarryDigit n = 8) ∧
    (∀ k, 3 ≤ k → factorialCarryDigit k.factorial = 2 ∧
      factorialCarryDigit (2 * k.factorial) = 4) ∧
    (∀ t, 0 < t → ∀ N, ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧
      factorialCarryDigit i = 2 ∧ factorialCarryDigit j = 4) ∧
    HasSum (fun j : ℕ => (factorialCarryDigit (j + 1) : ℝ) / 2 ^ (j + 1)) 4 ∧
    (∀ N, HasSum (fun j : ℕ =>
      (factorialCarryDigit (N + j + 1) : ℝ) / 2 ^ (j + 1)) (factorialCarry N : ℝ)) := by
  refine ⟨factorialCarryDigit_mem, ?_, ?_, ?_, factorialCarry_hasSum_tail⟩
  · intro k hk
    exact ⟨factorialCarryDigit_at_factorial k hk,
      factorialCarryDigit_at_twice_factorial k hk⟩
  · intro t ht N
    exact factorialCarryDigit_recurring_multiples t N ht
  · simpa using factorialCarry_hasSum_tail 0

end
end ErdosProblems.Erdos251.PaperR7
