import Mathlib

/-! The scalar real statement of the paper's signed two-window criterion.
The even mismatch is an integer; neither state is assumed rational. -/
namespace ErdosProblems.Erdos251.PaperCompleteR20

theorem signed_two_window_iff (D D' : ℝ) (δ : ℤ)
    (heven : Even δ) (hstep : D' = 2 * D - (δ : ℝ)) :
    (|D| < 1 ∧ |D'| < 1 ∧ δ ≠ 0) ↔
      ∃ s : ℤ, (s = -1 ∨ s = 1) ∧ δ = 2 * s ∧
        (1 / 2 : ℝ) < (s : ℝ) * D ∧ (s : ℝ) * D < 1 := by
  constructor
  · rintro ⟨hD, hD', hδ⟩
    obtain ⟨k, hk⟩ := heven
    have hkR : (δ : ℝ) = 2 * (k : ℝ) := by
      rw [hk]
      push_cast
      ring
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hD
    obtain ⟨hlo', hhi'⟩ := abs_lt.mp hD'
    have hklo : (-2 : ℤ) < k := by
      have : (-2 : ℝ) < (k : ℝ) := by linarith
      exact_mod_cast this
    have hkhi : k < (2 : ℤ) := by
      have : (k : ℝ) < 2 := by linarith
      exact_mod_cast this
    have hkne : k ≠ 0 := by intro h; apply hδ; omega
    have hc : k = -1 ∨ k = 1 := by omega
    refine ⟨k, hc, by omega, ?_⟩
    rcases hc with rfl | rfl <;> norm_num at hkR ⊢ <;> constructor <;> linarith
  · rintro ⟨s, hs, hδ, hlo, hhi⟩
    rcases hs with rfl | rfl <;> subst δ <;> norm_num at hstep hlo hhi ⊢
    · exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩,
        abs_lt.mpr ⟨by linarith, by linarith⟩⟩
    · exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩,
        abs_lt.mpr ⟨by linarith, by linarith⟩⟩

private theorem nonintegral_of_small_nonzero {x : ℝ} (hx : |x| < 1) (hne : x ≠ 0) :
    x ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨k, rfl⟩
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hx
  have hklo : (-1 : ℤ) < k := by exact_mod_cast hlo
  have hkhi : k < (1 : ℤ) := by exact_mod_cast hhi
  have hk : k = 0 := by omega
  exact hne (by simp [hk])

theorem signed_two_window_consequences (D D' : ℝ) (δ s : ℤ)
    (hstep : D' = 2 * D - (δ : ℝ)) (hs : s = -1 ∨ s = 1)
    (hδ : δ = 2 * s) (hlo : (1 / 2 : ℝ) < (s : ℝ) * D)
    (hhi : (s : ℝ) * D < 1) :
    (-1 < (s : ℝ) * D' ∧ (s : ℝ) * D' < 0) ∧
      D ∉ Set.range ((↑) : ℤ → ℝ) ∧ D' ∉ Set.range ((↑) : ℤ → ℝ) := by
  have hsmall : |D| < 1 ∧ |D'| < 1 ∧ δ ≠ 0 :=
    (signed_two_window_iff D D' δ (by rw [hδ]; exact even_two_mul s) hstep).mpr
      ⟨s, hs, hδ, hlo, hhi⟩
  have hbounds : (-1 < (s : ℝ) * D' ∧ (s : ℝ) * D' < 0) := by
    rcases hs with rfl | rfl <;> subst δ <;> norm_num at hstep hlo hhi ⊢ <;>
      constructor <;> linarith
  refine ⟨hbounds, nonintegral_of_small_nonzero hsmall.1 ?_,
    nonintegral_of_small_nonzero hsmall.2.1 ?_⟩
  · intro h; rw [h, mul_zero] at hlo; norm_num at hlo
  · intro h; rw [h, mul_zero] at hbounds; linarith [hbounds.2]

#print axioms signed_two_window_iff
#print axioms signed_two_window_consequences
end ErdosProblems.Erdos251.PaperCompleteR20
