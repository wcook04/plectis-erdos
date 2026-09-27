-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.ArgumentGraph.Derived.Erdos1041

/-!
# Erdős #1041: what the inner-chord factoring adds, clause by clause

`binomial_inner_chord_maximal` assumes the switch condition `1 ≤ rⁿ (1 + cⁿ)`, with
`c = cos (π / n)`, and concludes a midpoint equality and a maximality clause
`∀ s, innerRadius n r < s → s ≤ r → 1 < ‖…‖`. Its proof passes the switch condition to
`inner_chord_maximal`, and `derive_factor` finds it unused once that lemma is factored:
`binomial_inner_chord_maximal.factored` states both clauses without it.

The theorems below say what that adds. Off the switch condition the inner radius exceeds
`r`, so no `s` meets the maximality clause's hypotheses there and that clause gains
nothing. The midpoint equality is asserted at every added point, and the added region is
not empty: the switch condition fails at `n = 3`, `r = 1/2`, where the factored theorem
gives the equality and the Lean theorem as written does not apply.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open BinomialChord

/-- Off the switch condition the inner radius exceeds `r`. -/
theorem lt_innerRadius_of_not_switch {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ^ n < 1) (hsw : ¬ 1 ≤ r ^ n * (1 + chordCos n ^ n)) : r < innerRadius n r := by
  have hc := chordCos_pos hn
  have ht0 := (innerRadius_pos hn hr1).le
  have hn0 : n ≠ 0 := by omega
  have hlt : r ^ n * (1 + chordCos n ^ n) < 1 := not_le.mp hsw
  have hpow : (r * chordCos n) ^ n < (innerRadius n r * chordCos n) ^ n := by
    rw [innerRadius_mul_cos_pow hn hr1.le, mul_pow]
    have e : r ^ n * (1 + chordCos n ^ n) = r ^ n + r ^ n * chordCos n ^ n := by ring
    linarith
  have hbase : r * chordCos n < innerRadius n r * chordCos n := by
    by_contra hcon
    push_neg at hcon
    rcases hcon.lt_or_eq with h | h
    · have := pow_lt_pow_left₀ h (by positivity) hn0
      linarith
    · rw [h] at hpow
      exact lt_irrefl _ hpow
  exact lt_of_mul_lt_mul_right hbase hc.le

/-- Off the switch condition the maximality clause of `binomial_inner_chord_maximal` has
no instance. -/
theorem inner_chord_maximality_vacuous_off_switch {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ^ n < 1) (hsw : ¬ 1 ≤ r ^ n * (1 + chordCos n ^ n)) (s : ℝ) :
    ¬ (innerRadius n r < s ∧ s ≤ r) := by
  rintro ⟨h1, h2⟩
  have := lt_innerRadius_of_not_switch hn hr0 hr1 hsw
  linarith

/-- The switch condition fails at `n = 3`, `r = 1/2`. -/
theorem switch_fails_at_three_half : ¬ 1 ≤ ((1 : ℝ) / 2) ^ 3 * (1 + chordCos 3 ^ 3) := by
  have h0 := chordCos_nonneg (n := 3) (by norm_num)
  have h1 := chordCos_le_one 3
  have hc3 : chordCos 3 ^ 3 ≤ 1 := by
    calc chordCos 3 ^ 3 ≤ 1 ^ 3 := by gcongr
      _ = 1 := one_pow 3
  intro h
  rw [show ((1 : ℝ) / 2) ^ 3 = 1 / 8 by norm_num] at h
  linarith

/-- At `n = 3`, `r = 1/2`, outside the switch condition, the factored theorem gives the
midpoint equality. -/
theorem inner_chord_midpoint_at_three_half :
    ‖(chordPoint 3 (innerRadius 3 (1 / 2)) (1 / 2)) ^ 3 - (((1 / 2 : ℝ) : ℝ) : ℂ) ^ 3‖ = 1 :=
  (binomial_inner_chord_maximal.factored (n := 3) le_rfl (r := 1 / 2) (by norm_num)
    (by norm_num)).1

end ErdosProblems.Erdos1041.PaperCompleteR21

#print axioms ErdosProblems.Erdos1041.PaperCompleteR21.lt_innerRadius_of_not_switch
#print axioms ErdosProblems.Erdos1041.PaperCompleteR21.inner_chord_maximality_vacuous_off_switch
#print axioms ErdosProblems.Erdos1041.PaperCompleteR21.switch_fails_at_three_half
#print axioms ErdosProblems.Erdos1041.PaperCompleteR21.inner_chord_midpoint_at_three_half
