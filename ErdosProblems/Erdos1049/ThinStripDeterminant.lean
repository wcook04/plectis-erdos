import ErdosProblems.Erdos1049.TwoSelectorRemainderEscape

/-!
R6 candidate. NOT compiled in the review environment.

The finite divisibility-versus-area step behind affine collapse in a narrow
real bin. Applied to differences from an anchor, it forces every affine
three-point determinant to vanish. Source lattice indices and source real
bin estimates remain separate hypotheses.
-/
namespace ErdosProblems.Erdos1049

/-- A determinant divisible by a positive integer cannot be strictly smaller
than that integer. Real errors supply its upper bound. -/
theorem det_eq_zero_of_local_divisor_and_real_strip
    (A₁ B₁ A₂ B₂ D : ℤ) (ξ H ε : ℝ)
    (hD : 0 < D) (hH : 0 ≤ H) (hε : 0 ≤ ε)
    (hA₁ : |(A₁ : ℝ)| ≤ H) (hA₂ : |(A₂ : ℝ)| ≤ H)
    (he₁ : |(A₁ : ℝ) * ξ - B₁| ≤ ε)
    (he₂ : |(A₂ : ℝ) * ξ - B₂| ≤ ε)
    (hdiv : D ∣ A₁ * B₂ - A₂ * B₁)
    (hsmall : 2 * H * ε < (D : ℝ)) :
    A₁ * B₂ - A₂ * B₁ = 0 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hbound : |((A₁ * B₂ - A₂ * B₁ : ℤ) : ℝ)| ≤ 2 * H * ε := by
    calc
      |((A₁ * B₂ - A₂ * B₁ : ℤ) : ℝ)| =
          |(A₂ : ℝ) * ((A₁ : ℝ) * ξ - B₁) -
            (A₁ : ℝ) * ((A₂ : ℝ) * ξ - B₂)| := by
              congr 1
              push_cast
              ring
      _ ≤ |(A₂ : ℝ) * ((A₁ : ℝ) * ξ - B₁)| +
            |(A₁ : ℝ) * ((A₂ : ℝ) * ξ - B₂)| := abs_sub _ _
      _ = |(A₂ : ℝ)| * |(A₁ : ℝ) * ξ - B₁| +
            |(A₁ : ℝ)| * |(A₂ : ℝ) * ξ - B₂| := by rw [abs_mul, abs_mul]
      _ ≤ H * ε + H * ε :=
        add_le_add
          (mul_le_mul hA₂ he₁ (abs_nonneg _) hH)
          (mul_le_mul hA₁ he₂ (abs_nonneg _) hH)
      _ = 2 * H * ε := by ring
  by_contra hne
  obtain ⟨k, hk⟩ := hdiv
  have hk0 : k ≠ 0 := by
    intro hz
    apply hne
    rw [hk, hz, mul_zero]
  have hkZ : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
  have hkR : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hkZ
  have hlarge : (D : ℝ) ≤ |((A₁ * B₂ - A₂ * B₁ : ℤ) : ℝ)| := by
    calc
      (D : ℝ) ≤ (D : ℝ) * |(k : ℝ)| := by nlinarith
      _ = |((D * k : ℤ) : ℝ)| := by
        push_cast
        rw [abs_mul, abs_of_pos hDR]
      _ = |((A₁ * B₂ - A₂ * B₁ : ℤ) : ℝ)| := by rw [hk]
  linarith

end ErdosProblems.Erdos1049
