import Erdos249257.CarrySurvivorExtinction

/-! The manuscript's absolute-value finite carry test, with the actual
integer candidate set and the open invariant strip retained. -/
namespace ErdosProblems.Erdos249.PaperCompleteR20
open Erdos249257.TotientTailPeriodKiller

theorem finite_carry_test_sound (h N K : ℕ)
    (htest : ∀ z : ℤ, |z| ≤ (N + h + 1 : ℤ) →
      ∃ i : ℕ, i ≤ K ∧ (N + i + h + 2 : ℤ) ≤ |carryOrbit h N z i|) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  apply tail_diff_notMem_int_of_survivorKill (h := h) (N := N) (K := K)
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hjZ : (j : ℤ) < 2 * ((N : ℤ) + h + 1) + 1 := by exact_mod_cast hj'
  obtain ⟨i, hi, hesc⟩ := htest ((j : ℤ) - (N + h + 1)) (abs_le.mpr ⟨by omega, by omega⟩)
  refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
  rcases le_abs.mp hesc with hpos | hneg
  · exact Or.inr hpos
  · exact Or.inl (by omega)

theorem finite_carry_candidate_count (h N : ℕ) :
    (Finset.Icc (-(N + h + 1 : ℤ)) (N + h + 1)).card = 2 * (N + h + 1) + 1 := by
  simp only [Int.card_Icc]
  omega

theorem finite_carry_true_orbit (h N : ℕ) (z : ℤ)
    (hz : (z : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N z i : ℝ) = totientTail (N + i + h) - totientTail (N + i) ∧
    |carryOrbit h N z i| < (N + i + h + 2 : ℤ) := by
  have ht := carryOrbit_eq_tail_diff hz i
  refine ⟨ht, ?_⟩
  have hb := abs_tail_diff_lt h (N + i)
  rw [← ht] at hb
  exact_mod_cast hb

end ErdosProblems.Erdos249.PaperCompleteR20
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_test_sound
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_candidate_count
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_true_orbit
