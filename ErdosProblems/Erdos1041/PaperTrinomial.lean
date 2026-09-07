import ErdosProblems.Erdos1041.PaperCurveAssembly
import ErdosProblems.Erdos1041.AbelControlPolygon

/-!
# The complete displayed trinomial statement

Paper labels: short_note/res:trinomial-all-degree and
long_record/res:trinomial-all-degree.

The imported kernel supplies Vieta, spoke containment, and the norm-sum
budget. This file supplies the continuous, rectifiable broken line and its
actual variation. The source is uncompiled in this return.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperTrinomial

open Set PaperCurve AbelControlPolygon

/-- A public function spelling exactly the trinomial in both papers. -/
def polynomialValue (n m : ℕ) (a b z : ℂ) : ℂ := z ^ n + a * z ^ m + b

/-- Every root spoke is contained, with the constant-term bound derived from
all the roots, not assumed as an additional paper hypothesis. -/
theorem all_spokes {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z : ℂ} (hz : polynomialValue n m a b z = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1 := by
  exact trinomial_radial_norm_lt_one hm hmn
    (norm_const_lt_one_of_roots_lt_one hm hmn hroots) (hroots z hz) hz ht0 ht1

/-- The complete broken-line statement, including its endpoints, continuous
parametrisation, containment, rectifiability, and exact (not surrogate) length.
It also holds when the two chosen roots coincide; distinctness can be imposed
by a caller without any change to the construction. -/
theorem complete_trinomial {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z₁ z₂ : ℂ} (h₁ : polynomialValue n m a b z₁ = 0)
    (h₂ : polynomialValue n m a b z₂ = 0) :
    Continuous (hub z₁ 0 z₂) ∧
    hub z₁ 0 z₂ 0 = z₁ ∧ hub z₁ 0 z₂ 2 = z₂ ∧
    (∀ t ∈ Icc (0 : ℝ) 2,
      ‖polynomialValue n m a b (hub z₁ 0 z₂ t)‖ < 1) ∧
    BoundedVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2) ∧
    (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal = ‖z₁‖ + ‖z₂‖ ∧
    (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal < 2 := by
  refine ⟨hub_continuous _ _ _, hub_zero _ _ _, hub_two _ _ _, ?_,
    hub_rectifiable _ _ _, ?_, ?_⟩
  · intro t ht
    apply hub_mem (S := {z | ‖polynomialValue n m a b z‖ < 1}) ?_ ?_ ht
    · intro u hu0 hu1
      simpa using all_spokes hm hmn hroots h₁ hu0 hu1
    · intro u hu0 hu1
      simpa using all_spokes hm hmn hroots h₂ hu0 hu1
  · simpa using hub_length z₁ 0 z₂
  · rw [hub_length]
    simpa only [zero_sub, norm_neg, sub_zero] using
      (show ‖z₁‖ + ‖z₂‖ < 2 by linarith [hroots z₁ h₁, hroots z₂ h₂])

theorem trinomial_connectedBelow {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    {a b z₁ z₂ : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    (h₁ : polynomialValue n m a b z₁ = 0)
    (h₂ : polynomialValue n m a b z₂ = 0) :
    ConnectedBelow (polynomialValue n m a b) 1 2 z₁ z₂ := by
  apply connectedBelow_of_spokes (h := 0)
  · intro u hu0 hu1
    simpa using all_spokes hm hmn hroots h₁ hu0 hu1
  · intro u hu0 hu1
    simpa using all_spokes hm hmn hroots h₂ hu0 hu1
  · simp only [zero_sub, norm_neg, sub_zero]
    linarith [hroots z₁ h₁, hroots z₂ h₂]

/-- The existential quantifier in the displayed sextic obstruction is closed
by the exact rational radius `999/1000`; the ambient root assertion is universal.
This is a spoke counterexample, not a no-go for arbitrary connections. -/
theorem complete_sextic_guardrail :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ w : ℂ, sextic (r : ℂ) w = 0 → ‖w‖ < 1) ∧
      sextic (r : ℂ) (r : ℂ) = 0 ∧
      (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧
      1 < ‖sextic (r : ℂ) (((1 / 2 : ℝ) : ℂ) * (r : ℂ))‖ := by
  let r : ℝ := 999 / 1000
  have hr : 0 < r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  have hbig : (320 : ℝ) / 327 < r ^ 6 := by norm_num [r]
  obtain ⟨hroots, hescape⟩ := sextic_guardrail hr hr1 hbig
  refine ⟨r, hr, hr1, hroots, ?_, by norm_num, by norm_num, ?_⟩
  · rw [sextic_factor]
    simp
  · convert hescape using 1 <;> push_cast <;> ring

#print axioms complete_trinomial
#print axioms complete_sextic_guardrail

end ErdosProblems.Erdos1041.PaperTrinomial
