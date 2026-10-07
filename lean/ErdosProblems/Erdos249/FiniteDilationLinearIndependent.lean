import ErdosProblems.Erdos249.FiniteDilationLeastResidueRational

/-!
# Countable rational independence of dilated least-residue values

The finite affine obstruction is the source theorem.  This companion records
its countable family form using Mathlib's `LinearIndependent` predicate.
-/

namespace ErdosProblems.Erdos249.FiniteDilationLinearIndependent

open scoped BigOperators
open ErdosProblems.Erdos249.FiniteDilationLeastResidueRational
open ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables

/-- A rational coefficient may be moved from the residue observable to the
outside of its absolutely convergent radix series. -/
theorem positiveRadixValue_mul_residue
    (B d m : ℕ) (c : ℚ) :
    positiveRadixValue (B ^ d) (fun r : ℕ => c * (r : ℚ)) m =
      (c : ℝ) * positiveRadixValue (B ^ d)
        (fun r : ℕ => (r : ℚ)) m := by
  unfold positiveRadixValue
  calc
    (∑' n : ℕ,
      ((c * ((Nat.totient (n + 1) % m : ℕ) : ℚ) : ℚ) : ℝ) /
        ((B ^ d : ℕ) : ℝ) ^ (n + 1)) =
      ∑' n : ℕ, (c : ℝ) *
        (((Nat.totient (n + 1) % m : ℕ) : ℝ) /
          ((B ^ d : ℕ) : ℝ) ^ (n + 1)) := by
        apply tsum_congr
        intro n
        simp only [Rat.cast_mul, Rat.cast_natCast]
        ring
    _ = (c : ℝ) * (∑' n : ℕ,
        (((Nat.totient (n + 1) % m : ℕ) : ℝ) /
          ((B ^ d : ℕ) : ℝ) ^ (n + 1))) := tsum_mul_left

/-- The exact countable formulation of the finite affine obstruction:
index zero is the constant 1, and positive index d is the least-residue
totient series in base B^d. -/
theorem linearIndependent_one_and_least_residue_values
    (m B : ℕ) (hm : 3 ≤ m) (hB : 2 ≤ B) :
    LinearIndependent ℚ (fun d : ℕ =>
      if d = 0 then (1 : ℝ) else
        positiveRadixValue (B ^ d) (fun r : ℕ => (r : ℚ)) m) := by
  classical
  let v : ℕ → ℝ := fun d =>
    if d = 0 then 1 else
      positiveRadixValue (B ^ d) (fun r : ℕ => (r : ℚ)) m
  change LinearIndependent ℚ v
  rw [linearIndependent_iff']
  intro s g hsum d hd
  let D := s.filter (fun e => e ≠ 0)
  let F := s.filter (fun e => e = 0)
  let q : ℚ := if 0 ∈ s then g 0 else 0
  have hFset : F = if 0 ∈ s then {0} else ∅ := by
    by_cases h0 : 0 ∈ s
    · rw [if_pos h0]
      ext e
      constructor
      · intro he
        exact Finset.mem_singleton.mpr (Finset.mem_filter.mp he).2
      · intro he
        have he0 : e = 0 := Finset.mem_singleton.mp he
        subst e
        exact Finset.mem_filter.mpr ⟨h0, rfl⟩
    · rw [if_neg h0]
      ext e
      constructor
      · intro he
        obtain ⟨hes, he0⟩ := Finset.mem_filter.mp he
        subst e
        exact False.elim (h0 hes)
      · intro he
        simp at he
  have hFsum : (∑ e ∈ F, g e • v e) = (q : ℝ) := by
    by_cases h0 : 0 ∈ s
    · rw [hFset, if_pos h0]
      simp [q, h0, v, Rat.smul_def]
    · rw [hFset, if_neg h0]
      simp [q, h0]
  have hDsum : (∑ e ∈ D, g e • v e) =
      ∑ e ∈ D, positiveRadixValue (B ^ e)
        (fun r : ℕ => g e * (r : ℚ)) m := by
    apply Finset.sum_congr rfl
    intro e he
    have hene : e ≠ 0 := (Finset.mem_filter.mp he).2
    simp only [v, if_neg hene, Rat.smul_def]
    exact (positiveRadixValue_mul_residue B e m (g e)).symm
  have hsplit : (∑ e ∈ D, g e • v e) + (∑ e ∈ F, g e • v e) =
      ∑ e ∈ s, g e • v e := by
    simpa only [D, F, not_ne_iff] using
      Finset.sum_filter_add_sum_filter_not s (fun e : ℕ => e ≠ 0)
        (fun e => g e • v e)
  have hrelation : (q : ℝ) + (∑ e ∈ D,
      positiveRadixValue (B ^ e)
        (fun r : ℕ => g e * (r : ℚ)) m) = 0 := by
    rw [← hsplit, hDsum, hFsum] at hsum
    simpa only [add_comm] using hsum
  have hposD : ∀ e ∈ D, 0 < e := by
    intro e he
    have hene : e ≠ 0 := (Finset.mem_filter.mp he).2
    omega
  have hzeroD : ∀ e ∈ D, g e = 0 := by
    intro e he
    by_contra hne
    exact (no_rational_affine_least_residue_relation
      D g q m B hm hB hposD ⟨e, he, hne⟩) hrelation
  have hDval : (∑ e ∈ D,
      positiveRadixValue (B ^ e)
        (fun r : ℕ => g e * (r : ℚ)) m) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp [hzeroD e he, positiveRadixValue]
  have hqzero : q = 0 := by
    rw [hDval, add_zero] at hrelation
    exact Rat.cast_injective (by simpa using hrelation)
  by_cases hd0 : d = 0
  · subst d
    have h0 : 0 ∈ s := hd
    simpa only [q, if_pos h0] using hqzero
  · exact hzeroD d (Finset.mem_filter.mpr ⟨hd, hd0⟩)

#print axioms positiveRadixValue_mul_residue
#print axioms linearIndependent_one_and_least_residue_values

end ErdosProblems.Erdos249.FiniteDilationLinearIndependent
