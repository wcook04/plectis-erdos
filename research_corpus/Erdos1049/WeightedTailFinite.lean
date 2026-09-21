-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Mathlib

/-!
# Finite supporting lemmas for the weighted-tail review

**UNRUN.** This file is not imported by any registered module and is not part
of any checked build. It has never been compiled in this checkout. The absence
of `sorry` and of new `axiom` declarations below is a lexical observation about
the source, not a kernel-acceptance claim.

These lemmas formalise only elementary finite consumers of
`WeightedTailRoutes.md` and `SunCatalanAudit.md`. They do not claim
formalisation of the geometric-moment limit, the cyclotomic pole theorem, the
complete tail-denominator argument, or an irrationality theorem. The only
nontrivial hypotheses are the finite divisibility assumptions, `q ≠ 0` for the
field identity, and `2 ≤ n` for positivity.

Before composing any of these into a consumer: compile the file in isolation,
inspect `#print axioms` for each accepted declaration, and only then import it.
-/

namespace Erdos1049SunReview

/-- Exact integer span of the first two primitive tail rows. -/
theorem seed_span_iff (a b x y : ℤ) :
    (∃ s t : ℤ, x = s + t * (a - b) ∧ y = t * b) ↔ b ∣ y := by
  constructor
  · rintro ⟨s, t, hx, hy⟩
    exact ⟨t, by simpa only [mul_comm] using hy⟩
  · rintro ⟨t, ht⟩
    refine ⟨x - t * (a - b), t, ?_, ?_⟩
    · ring
    · simpa only [mul_comm] using ht

/-- The seed minor is b, with no coprimality hypothesis required. -/
theorem seed_minor (a b : ℤ) : 1 * b - 0 * (a - b) = b := by
  ring

/-- A finite integer combination preserves the divisibility of second coordinates. -/
theorem sum_second_divisible {ι : Type*} (s : Finset ι)
    (b : ℤ) (c v : ι → ℤ) (h : ∀ i ∈ s, b ∣ v i) :
    b ∣ ∑ i ∈ s, c i * v i := by
  classical
  apply Finset.dvd_sum
  intro i hi
  obtain ⟨t, ht⟩ := h i hi
  refine ⟨c i * t, ?_⟩
  rw [ht]
  ring

/-- Clearing an individual rationally weighted tail stays on the same rational line. -/
theorem weighted_tail_line (w f p q : ℚ) (hq : q ≠ 0) :
    w * (f - p / q) = (w / q) * (q * f - p) := by
  field_simp [hq]
  <;> ring

/-- The small-prime singular coefficient does not cancel the real coefficient. -/
theorem sun_leading_residual (ρ : ℚ) :
    2 * ρ - (2 * ρ - ρ ^ 2 / 2) = ρ ^ 2 / 2 := by
  ring

/-- The precise residual at Sun's parameter, not a floating-point comparison. -/
theorem sun_one_over_eight_hundred :
    2 * (1 / 20 : ℚ) -
      (2 * (1 / 20 : ℚ) - (1 / 20 : ℚ) ^ 2 / 2) = 1 / 800 := by
  norm_num

/-- Numerator at the claimed removable pole in the B=2, j=1 correction. -/
theorem sun_bad_correction_numerator :
    (2 * (-1 / 2 : ℚ) + 3) * (2 * (-1 / 2 : ℚ) + 5) ^ 2 = 32 := by
  norm_num

/-- The additional same-rank extraction still required by the packet's budget. -/
theorem residual_charge_identity (n : ℚ) :
    (39 / 41 : ℚ) * (4 * n ^ 3 - 3 * n ^ 2) - (2 * n ^ 3 - n) =
      n * (74 * n ^ 2 - 117 * n + 41) / 41 := by
  ring

/-- A useful positive expansion of the quadratic factor for n >= 2. -/
theorem residual_quadratic_expansion (n : ℚ) :
    74 * n ^ 2 - 117 * n + 41 =
      74 * (n - 2) ^ 2 + 179 * (n - 2) + 103 := by
  ring

theorem residual_quadratic_pos (n : ℚ) (hn : 2 ≤ n) :
    0 < 74 * n ^ 2 - 117 * n + 41 := by
  have hsq : 0 ≤ (n - 2) ^ 2 := sq_nonneg (n - 2)
  rw [residual_quadratic_expansion]
  nlinarith

/-- Finite strict deficit, conditional only on the stated numerical range. -/
theorem residual_charge_pos (n : ℚ) (hn : 2 ≤ n) :
    0 < (39 / 41 : ℚ) * (4 * n ^ 3 - 3 * n ^ 2) - (2 * n ^ 3 - n) := by
  rw [residual_charge_identity]
  have hn0 : 0 < n := by linarith
  have hquad := residual_quadratic_pos n hn
  exact div_pos (mul_pos hn0 hquad) (by norm_num)

end Erdos1049SunReview
