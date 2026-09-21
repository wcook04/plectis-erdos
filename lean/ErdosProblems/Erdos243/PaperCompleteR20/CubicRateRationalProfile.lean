import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateResidualConstant

/-!
# Erdős 243: rational coefficients of the eventual cubic
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

/-- An integer sequence which agrees eventually with a real rising cubic has
rational leading and constant coefficients. -/
theorem rational_coefficients_of_eventual_cubic
    (C : ℕ → ℤ) (K B : ℝ) (N : ℕ)
    (hprofile : ∀ n, N ≤ n → (C n : ℝ) = K * risingCubic n + B) :
    ∃ A D : ℚ, ∀ n, N ≤ n →
      (C n : ℝ) = (A : ℝ) * risingCubic n + (D : ℝ) := by
  have h0 := hprofile N (le_rfl)
  have h1 := hprofile (N + 1) (by omega)
  have h2 := hprofile (N + 2) (by omega)
  have h3 := hprofile (N + 3) (by omega)
  let m : ℤ := iterIntForwardDiff 3 C N
  have hm : (m : ℝ) = 6 * K := by
    dsimp [m]
    simp only [iterIntForwardDiff, intForwardDiff, Int.cast_sub]
    simp [risingCubic] at h0 h1 h2 h3
    push_cast
    linear_combination h3 - 3 * h2 + 3 * h1 - h0
  let A : ℚ := (m : ℚ) / 6
  have hA : (A : ℝ) = K := by
    dsimp [A]
    push_cast
    linarith
  let D : ℚ := (C N : ℚ) - A *
    (N : ℚ) * ((N : ℚ) + 1) * ((N : ℚ) + 2)
  have hD : (D : ℝ) = B := by
    dsimp [D]
    push_cast
    rw [hA]
    simp [risingCubic] at h0 ⊢
    linarith
  exact ⟨A, D, fun n hn => by rw [hprofile n hn, hA, hD]⟩

theorem literal_ratio_error_gives_rational_eventual_cubic
    (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ A D : ℚ, ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = (A : ℝ) * risingCubic n + (D : ℝ) := by
  obtain ⟨K, B, N, hprofile⟩ :=
    literal_ratio_error_gives_exact_eventual_cubic C hpos hratio
  obtain ⟨A, D, hAD⟩ := rational_coefficients_of_eventual_cubic
    C K B N hprofile
  exact ⟨A, D, N, hAD⟩

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.rational_coefficients_of_eventual_cubic
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_rational_eventual_cubic

end ErdosProblems.Erdos243.PaperCompleteR20
