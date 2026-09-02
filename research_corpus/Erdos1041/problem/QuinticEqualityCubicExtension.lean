import ErdosProblems.Erdos1041.QuinticEqualityTetrahedron
import Mathlib.Tactic

/-!
# Erdős #1041: extending the equality tetrahedron by the paired cubic mode

At the four active quintic equality contacts, the paired cubic corrections
sum to `-48 * y³`.  Since the coefficient-gradient variations sum to zero,
the extended variations have strictly negative average whenever the cubic
scale is positive.  At scale zero the existing tetrahedral selector applies.
-/

namespace ErdosProblems.Erdos1041.QuinticEqualityCubicExtension

open ErdosProblems.Erdos1041.QuinticEqualityTetrahedron

def leftCubic (y : ℝ) : ℝ := -14 * y ^ 3
def upperCubic (s₃ y : ℝ) : ℝ := (s₃ - 1) ^ 3 * y ^ 3
def rightCubic (y : ℝ) : ℝ := -14 * y ^ 3
def lowerCubic (s₃ y : ℝ) : ℝ := -(s₃ + 1) ^ 3 * y ^ 3

/-- The four paired-cubic contact values have sum `-48 y³`. -/
theorem cubicCorrection_sum {s₃ y : ℝ} (hs₃ : s₃ ^ 2 = 3) :
    leftCubic y + upperCubic s₃ y + rightCubic y + lowerCubic s₃ y =
      -48 * y ^ 3 := by
  unfold leftCubic upperCubic rightCubic lowerCubic
  ring_nf at hs₃ ⊢
  linear_combination -6 * y ^ 3 * hs₃

def leftExtended (s₅ y a b c rho : ℝ) : ℝ :=
  leftVariation s₅ y a b c + rho * leftCubic y

def upperExtended (s₃ y b c rho : ℝ) : ℝ :=
  upperAxisVariation s₃ y b c + rho * upperCubic s₃ y

def rightExtended (s₅ y a b c rho : ℝ) : ℝ :=
  rightVariation s₅ y a b c + rho * rightCubic y

def lowerExtended (s₃ y b c rho : ℝ) : ℝ :=
  lowerAxisVariation s₃ y b c + rho * lowerCubic s₃ y

/-- The coefficient variations cancel and leave the strictly negative cubic
barycentre. -/
theorem extendedVariation_sum {s₃ s₅ y a b c rho : ℝ} (hs₃ : s₃ ^ 2 = 3) :
    leftExtended s₅ y a b c rho + upperExtended s₃ y b c rho +
      rightExtended s₅ y a b c rho + lowerExtended s₃ y b c rho =
        -48 * rho * y ^ 3 := by
  have hv := variation_sum_zero (s₅ := s₅) (y := y) (a := a) (b := b) (c := c) hs₃
  have hq := cubicCorrection_sum (y := y) hs₃
  calc
    leftExtended s₅ y a b c rho + upperExtended s₃ y b c rho +
          rightExtended s₅ y a b c rho + lowerExtended s₃ y b c rho =
        (leftVariation s₅ y a b c + upperAxisVariation s₃ y b c +
          rightVariation s₅ y a b c + lowerAxisVariation s₃ y b c) +
        rho * (leftCubic y + upperCubic s₃ y + rightCubic y + lowerCubic s₃ y) := by
          unfold leftExtended upperExtended rightExtended lowerExtended
          ring
    _ = 0 + rho * (-48 * y ^ 3) := by rw [hv, hq]
    _ = -48 * rho * y ^ 3 := by ring

/-- At least one extended contact is no larger than the four-contact average
`-12 rho y³`. -/
theorem oneExtended_le_average {s₃ s₅ y a b c rho : ℝ} (hs₃ : s₃ ^ 2 = 3) :
    leftExtended s₅ y a b c rho ≤ -12 * rho * y ^ 3 ∨
      upperExtended s₃ y b c rho ≤ -12 * rho * y ^ 3 ∨
      rightExtended s₅ y a b c rho ≤ -12 * rho * y ^ 3 ∨
      lowerExtended s₃ y b c rho ≤ -12 * rho * y ^ 3 := by
  have hsum := extendedVariation_sum (s₅ := s₅) (y := y)
    (a := a) (b := b) (c := c) (rho := rho) hs₃
  by_contra h
  push Not at h
  rcases h with ⟨hL, hU, hR, hD⟩
  nlinarith

/-- A common upper remainder smaller than the cubic average margin leaves one
strictly negative contact. -/
theorem extendedContact_absorbs_remainder
    {s₃ s₅ y a b c rho epsilon rL rU rR rD : ℝ}
    (hs₃ : s₃ ^ 2 = 3) (hmargin : epsilon < 12 * rho * y ^ 3)
    (hrL : rL ≤ epsilon) (hrU : rU ≤ epsilon)
    (hrR : rR ≤ epsilon) (hrD : rD ≤ epsilon) :
    leftExtended s₅ y a b c rho + rL < 0 ∨
      upperExtended s₃ y b c rho + rU < 0 ∨
      rightExtended s₅ y a b c rho + rR < 0 ∨
      lowerExtended s₃ y b c rho + rD < 0 := by
  rcases oneExtended_le_average (s₅ := s₅) (y := y)
      (a := a) (b := b) (c := c) (rho := rho) hs₃ with h | h | h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

/-- Every nonzero admissible extended direction has a strictly negative
contact: positive cubic scale uses the average, while scale zero reuses the
coefficient tetrahedron. -/
theorem extended_strict_selector {s₃ s₅ y a b c rho : ℝ}
    (hs₃sq : s₃ ^ 2 = 3) (hs₃ : 1 < s₃)
    (hs₅ : 0 < s₅) (hy : 0 < y) (hrho : 0 ≤ rho)
    (hnonzero : rho ≠ 0 ∨ a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    leftExtended s₅ y a b c rho < 0 ∨
      upperExtended s₃ y b c rho < 0 ∨
      rightExtended s₅ y a b c rho < 0 ∨
      lowerExtended s₃ y b c rho < 0 := by
  by_cases hzero : rho = 0
  · subst rho
    simp only [leftExtended, upperExtended, rightExtended, lowerExtended, zero_mul, add_zero]
    rcases hnonzero with hbad | hnonzero
    · exact (hbad rfl).elim
    · exact tetrahedral_strict_selector hs₃sq hs₃ hs₅ hy hnonzero
  · have hrho' : 0 < rho := lt_of_le_of_ne hrho (Ne.symm hzero)
    have hmargin : -12 * rho * y ^ 3 < 0 := by
      have hy3 : 0 < y ^ 3 := pow_pos hy 3
      nlinarith [mul_pos hrho' hy3]
    rcases oneExtended_le_average (s₅ := s₅) (y := y)
        (a := a) (b := b) (c := c) (rho := rho) hs₃sq with h | h | h | h
    · exact Or.inl (lt_of_le_of_lt h hmargin)
    · exact Or.inr (Or.inl (lt_of_le_of_lt h hmargin))
    · exact Or.inr (Or.inr (Or.inl (lt_of_le_of_lt h hmargin)))
    · exact Or.inr (Or.inr (Or.inr (lt_of_le_of_lt h hmargin)))

end ErdosProblems.Erdos1041.QuinticEqualityCubicExtension
