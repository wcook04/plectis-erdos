import Mathlib

/-!
# Finite algebra for the r6 displacement tail budget

STATUS: uncompiled candidate. No local Lean or Comparator build was run.
This file is not a formalisation of countable gluing, the infinite weighted
hosts, the logarithmic erasure argument, or the Baire-category result.
Those ordinary proofs are in CountableGluingAndActualBarriers.tex/PDF.
The namespace is separate from registered claims. No sorry or new axiom is used.
-/

namespace ErdosProblems.Erdos257.R6TailBudgetDraft

/-- The exact rational displacement of one positive exponent. -/
def atom (b a N : ℕ) : ℚ :=
  ((b : ℚ) ^ (N % a) - 1) / ((b : ℚ) ^ a - 1)

/-- A future exponent has not wrapped at the chosen shift. -/
theorem atom_of_lt (b a N : ℕ) (h : N < a) :
    atom b a N = ((b : ℚ) ^ N - 1) / ((b : ℚ) ^ a - 1) := by
  simp [atom, Nat.mod_eq_of_lt h]

/-- A selected finite prefix can be annihilated exactly. -/
theorem atom_of_dvd (b a N : ℕ) (h : a ∣ N) : atom b a N = 0 := by
  simp [atom, Nat.mod_eq_zero_of_dvd h]

def finiteDisplacement (F : Finset ℕ) (b N : ℕ) : ℚ :=
  ∑ a ∈ F, atom b a N

theorem finiteDisplacement_eq_zero (F : Finset ℕ) (b N : ℕ)
    (h : ∀ a ∈ F, a ∣ N) : finiteDisplacement F b N = 0 := by
  unfold finiteDisplacement
  apply Finset.sum_eq_zero
  intro a ha
  exact atom_of_dvd b a N (h a ha)

/-- The finite version of the future-mass amplification identity. -/
theorem finite_tail_identity (F : Finset ℕ) (b N : ℕ)
    (h : ∀ a ∈ F, N < a) :
    finiteDisplacement F b N =
      ((b : ℚ) ^ N - 1) * (∑ a ∈ F, 1 / ((b : ℚ) ^ a - 1)) := by
  unfold finiteDisplacement
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [atom_of_lt b a N (h a ha)]
  ring

/-- The explicit gap N+j+3 leaves at most 2^(-j-2) of the universal budget. -/
theorem dyadic_tail_budget (N j R : ℕ) (h : N + j + 3 ≤ R) :
    (2 : ℚ) ^ (N + 1) / (2 : ℚ) ^ R ≤
      1 / (2 : ℚ) ^ (j + 2) := by
  have hp : (2 : ℚ) ^ (N + j + 3) ≤ (2 : ℚ) ^ R :=
    pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) h
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa only [one_mul, ← pow_add, show N + 1 + (j + 2) = N + j + 3 by omega]
    using hp

/-- A literal first stage in the prime-colouring construction. -/
example : finiteDisplacement {2, 3, 5} 2 30 = 0 := by
  norm_num [finiteDisplacement, atom]

example : (2 : ℚ) ^ (30 + 1) / (2 : ℚ) ^ 34 = 1 / 8 := by
  norm_num

end ErdosProblems.Erdos257.R6TailBudgetDraft
