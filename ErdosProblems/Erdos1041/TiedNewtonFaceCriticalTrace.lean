import Mathlib.Tactic

/-!
# Erdős #1041: the critical-value trace of a low tied Newton face

For a sparse model `Q(z) = sum_m A_m z^m - z^n`, evaluating the critical
equation rewrites `Q(c)` as a weighted sum of the active powers `c^m`.
Consequently, if the corresponding critical-point power sums vanish, then the
sum of all critical values vanishes.  A nonempty zero-sum family of complex
numbers has a member with nonpositive real part.

The companion note supplies the Newton-identity argument showing that the
power-sum hypothesis is automatic when every active degree is strictly below
`n/2`, and the harmonic-topological consequence for the model sublevel set.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceCriticalTrace

/-- The sparse holomorphic Newton-face model. -/
noncomputable def modelValue (n : ℕ) (M : Finset ℕ) (A : ℕ → ℂ) (z : ℂ) : ℂ :=
  (∑ m ∈ M, A m * z ^ m) - z ^ n

/-- The critical-point value after using the derivative equation. -/
noncomputable def weightedCriticalValue
    (n : ℕ) (M : Finset ℕ) (A : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ m ∈ M, (1 - (m : ℂ) / (n : ℂ)) * A m * z ^ m

/-- Dividing the sparse derivative equation by the nonzero degree. -/
theorem criticalEquation_div {n : ℕ} (hn : n ≠ 0) {M : Finset ℕ}
    {A : ℕ → ℂ} {z : ℂ}
    (hcrit : (n : ℂ) * z ^ n = ∑ m ∈ M, (m : ℂ) * A m * z ^ m) :
    z ^ n = ∑ m ∈ M, ((m : ℂ) / (n : ℂ)) * A m * z ^ m := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  calc
    z ^ n = ((n : ℂ) * z ^ n) / (n : ℂ) := by field_simp
    _ = (∑ m ∈ M, (m : ℂ) * A m * z ^ m) / (n : ℂ) := by rw [hcrit]
    _ = ∑ m ∈ M, ((m : ℂ) / (n : ℂ)) * A m * z ^ m := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      field_simp

/-- At a critical point, the model value is the weighted active-mode sum.
This is the exact algebraic identity used by the trace argument. -/
theorem modelValue_eq_weightedCriticalValue {n : ℕ} (hn : n ≠ 0)
    {M : Finset ℕ} {A : ℕ → ℂ} {z : ℂ}
    (hcrit : (n : ℂ) * z ^ n = ∑ m ∈ M, (m : ℂ) * A m * z ^ m) :
    modelValue n M A z = weightedCriticalValue n M A z := by
  have hz := criticalEquation_div hn hcrit
  rw [modelValue, weightedCriticalValue, hz]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- Vanishing active power sums force the complete weighted critical-value
trace to vanish.  In the polynomial application `s` is the critical multiset. -/
theorem weightedCriticalValue_sum_eq_zero
    {ι : Type*} (s : Finset ι) (n : ℕ) (M : Finset ℕ)
    (A : ℕ → ℂ) (c : ι → ℂ)
    (hpower : ∀ m ∈ M, ∑ i ∈ s, c i ^ m = 0) :
    ∑ i ∈ s, weightedCriticalValue n M A (c i) = 0 := by
  simp only [weightedCriticalValue]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  rw [← Finset.mul_sum]
  simp [hpower m hm]

/-- A nonempty complex zero-sum family contains a value in the closed left
half-plane. -/
theorem exists_re_nonpos_of_sum_eq_zero
    {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℂ)
    (htrace : ∑ i, v i = 0) :
    ∃ i, (v i).re ≤ 0 := by
  by_contra h
  push Not at h
  have hpos : 0 < ∑ i, (v i).re :=
    Finset.sum_pos (fun i _ => h i) Finset.univ_nonempty
  have hzero : ∑ i, (v i).re = 0 := by
    rw [← Complex.re_sum, htrace]
    norm_num
  linarith

/-- The load-bearing finite trace principle: automatic power-sum cancellation
produces a critical value whose real part is nonpositive. -/
theorem exists_nonpositive_critical_value
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℕ) (M : Finset ℕ) (A : ℕ → ℂ) (c : ι → ℂ)
    (hpower : ∀ m ∈ M, ∑ i, c i ^ m = 0) :
    ∃ i, (weightedCriticalValue n M A (c i)).re ≤ 0 := by
  apply exists_re_nonpos_of_sum_eq_zero
  exact weightedCriticalValue_sum_eq_zero Finset.univ n M A c
    (by simpa using hpower)

end ErdosProblems.Erdos1041.TiedNewtonFaceCriticalTrace
