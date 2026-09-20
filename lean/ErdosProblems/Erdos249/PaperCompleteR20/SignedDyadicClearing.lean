import Erdos249257.SignedQMomentObstruction

/-! Exact denominator clearing for the manuscript's signed dyadic sum.
The parity theorem is recovered from SignedQMomentObstruction. -/
namespace ErdosProblems.Erdos249.PaperCompleteR20
open scoped BigOperators

theorem signed_dyadic_clearing {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α)
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (2 : ℚ) ^ e m * (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) =
      ((∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i) : ℤ) : ℚ) := by
  classical
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : e i ≤ e m := by
    by_cases h : i = m
    · subst i; exact le_rfl
    · exact (hmax i hi h).le
  have hp : (2 : ℚ) ^ e m = 2 ^ (e m - e i) * 2 ^ e i := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hp]
  field_simp
  <;> ring

theorem signed_dyadic_sum_ne_zero {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) ≠ 0 := by
  intro hz
  have h := signed_dyadic_clearing s u e m hmax
  rw [hz, mul_zero] at h
  have hn := Erdos249257.SignedQMomentObstruction.scaled_dyadic_sum_ne_zero
    s u e m hm hu hmax
  apply hn
  exact_mod_cast h.symm

end ErdosProblems.Erdos249.PaperCompleteR20
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_clearing
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_sum_ne_zero
#print axioms Erdos249257.SignedQMomentObstruction.scaled_dyadic_sum_odd
