import ErdosProblems.Erdos1041.QuinticCanonicalMixedSlice
import Mathlib.Tactic

/-!
# Erdős #1041: the four-contact equality tetrahedron

At the sharp canonical quintic chart, four certified connectors have contact
points proportional to

`sqrt(5)+i`, `i(sqrt(3)-1)`, `-sqrt(5)+i`, `-i(sqrt(3)+1)`.

Their first variations in the three normalized coefficient directions form a
tetrahedron centred at zero.  This module kernel-checks the exact barycentric
identity, the strict first-order selector in every nonzero direction, and the
elementary quadratic-remainder absorption used in the local stability proof.
-/

namespace ErdosProblems.Erdos1041.QuinticEqualityTetrahedron

/-- First variation at the contact proportional to `sqrt(5)+i`. -/
def leftVariation (s₅ y a b c : ℝ) : ℝ :=
  y * (s₅ * a - b) - 4 * y ^ 2 * c

/-- First variation at the contact `i(sqrt(3)-1)`. -/
def upperAxisVariation (s₃ y b c : ℝ) : ℝ :=
  -y * (s₃ - 1) * b + y ^ 2 * (s₃ - 1) ^ 2 * c

/-- First variation at the contact proportional to `-sqrt(5)+i`. -/
def rightVariation (s₅ y a b c : ℝ) : ℝ :=
  y * (-s₅ * a - b) - 4 * y ^ 2 * c

/-- First variation at the contact `-i(sqrt(3)+1)`. -/
def lowerAxisVariation (s₃ y b c : ℝ) : ℝ :=
  y * (s₃ + 1) * b + y ^ 2 * (s₃ + 1) ^ 2 * c

/-- The four contact gradients have barycentre zero. -/
theorem variation_sum_zero {s₃ s₅ y a b c : ℝ} (hs₃ : s₃ ^ 2 = 3) :
    leftVariation s₅ y a b c + upperAxisVariation s₃ y b c +
      rightVariation s₅ y a b c + lowerAxisVariation s₃ y b c = 0 := by
  unfold leftVariation upperAxisVariation rightVariation lowerAxisVariation
  ring_nf at hs₃ ⊢
  linear_combination 2 * y ^ 2 * c * hs₃

/-- Coordinate form of affine independence: if every contact variation
vanishes, then the parameter perturbation itself vanishes. -/
theorem contactVariations_jointKernel {s₃ s₅ y a b c : ℝ}
    (hs₃ : 1 < s₃) (hs₅ : 0 < s₅) (hy : 0 < y)
    (hL : leftVariation s₅ y a b c = 0)
    (hU : upperAxisVariation s₃ y b c = 0)
    (hR : rightVariation s₅ y a b c = 0)
    (hD : lowerAxisVariation s₃ y b c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hp : 0 < s₃ - 1 := sub_pos.mpr hs₃
  have hq : 0 < s₃ + 1 := by linarith
  have hp0 : s₃ - 1 ≠ 0 := ne_of_gt hp
  have hq0 : s₃ + 1 ≠ 0 := ne_of_gt hq
  have haProd : 2 * y * s₅ * a = 0 := by
    simp only [leftVariation] at hL
    simp only [rightVariation] at hR
    linarith
  have ha : a = 0 := by
    exact (mul_eq_zero.mp haProd).resolve_left (by positivity)
  have hUfact : y * (s₃ - 1) * (-b + y * (s₃ - 1) * c) = 0 := by
    rw [show y * (s₃ - 1) * (-b + y * (s₃ - 1) * c) =
      upperAxisVariation s₃ y b c by
        unfold upperAxisVariation
        ring]
    exact hU
  have hDfact : y * (s₃ + 1) * (b + y * (s₃ + 1) * c) = 0 := by
    rw [show y * (s₃ + 1) * (b + y * (s₃ + 1) * c) =
      lowerAxisVariation s₃ y b c by
        unfold lowerAxisVariation
        ring]
    exact hD
  have hUb : -b + y * (s₃ - 1) * c = 0 := by
    exact (mul_eq_zero.mp hUfact).resolve_left (mul_ne_zero hy0 hp0)
  have hDb : b + y * (s₃ + 1) * c = 0 := by
    exact (mul_eq_zero.mp hDfact).resolve_left (mul_ne_zero hy0 hq0)
  have hcProd : 2 * y * s₃ * c = 0 := by nlinarith
  have hc : c = 0 := by
    exact (mul_eq_zero.mp hcProd).resolve_left (by positivity)
  have hb : b = 0 := by nlinarith
  exact ⟨ha, hb, hc⟩

/-- Every nonzero normalized coefficient perturbation makes at least one of
the four contact values strictly smaller to first order. -/
theorem tetrahedral_strict_selector {s₃ s₅ y a b c : ℝ}
    (hs₃sq : s₃ ^ 2 = 3) (hs₃ : 1 < s₃)
    (hs₅ : 0 < s₅) (hy : 0 < y)
    (hnonzero : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    leftVariation s₅ y a b c < 0 ∨
      upperAxisVariation s₃ y b c < 0 ∨
      rightVariation s₅ y a b c < 0 ∨
      lowerAxisVariation s₃ y b c < 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨hL, hU, hR, hD⟩
  have hsum : leftVariation s₅ y a b c + upperAxisVariation s₃ y b c +
      rightVariation s₅ y a b c + lowerAxisVariation s₃ y b c = 0 := by
    unfold leftVariation upperAxisVariation rightVariation lowerAxisVariation
    ring_nf at hs₃sq ⊢
    linear_combination 2 * y ^ 2 * c * hs₃sq
  have hL0 : leftVariation s₅ y a b c = 0 := by nlinarith
  have hU0 : upperAxisVariation s₃ y b c = 0 := by nlinarith
  have hR0 : rightVariation s₅ y a b c = 0 := by nlinarith
  have hD0 : lowerAxisVariation s₃ y b c = 0 := by nlinarith
  rcases contactVariations_jointKernel hs₃ hs₅ hy hL0 hU0 hR0 hD0 with
    ⟨ha, hb, hc⟩
  rcases hnonzero with ha' | hb' | hc'
  · exact ha' ha
  · exact hb' hb
  · exact hc' hc

/-- A uniform negative linear margin absorbs a quadratic Taylor remainder at
sufficiently small scale. -/
theorem linearMargin_absorbs_quadratic {margin C δ linear remainder : ℝ}
    (hδ : 0 < δ) (hsmall : C * δ < margin)
    (hlinear : linear ≤ -margin * δ)
    (hremainder : remainder ≤ C * δ ^ 2) :
    linear + remainder < 0 := by
  have hquad : C * δ ^ 2 < margin * δ := by
    nlinarith
  nlinarith

end ErdosProblems.Erdos1041.QuinticEqualityTetrahedron
