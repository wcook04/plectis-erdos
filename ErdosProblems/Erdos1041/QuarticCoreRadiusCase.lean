import ErdosProblems.Erdos1041.QuarticQuotientFiberCase

/-!
# Erdős #1041: quartic-core factor and radius budgets

Pendyala's degree-four theorem supplies a polygonal path inside a disk of
radius `R` on which the product of four selected root factors is strictly
below `R^4`.  Every remaining root factor can then be paid for
multiplicatively.  This module checks that fan-in, the uniform all-roots
radius identity, and an exact separated quintic witness beyond the existing
`5/9` close-pair certificate.

The attributed degree-four path construction remains an analytic input in the
companion note.  No version of it is postulated as an axiom here.
-/

namespace ErdosProblems.Erdos1041

/-- Multiplying a strict quartic-core estimate by a nonnegative remainder
estimate preserves strictness when the comparison remainder is positive. -/
theorem quarticCore_factor_budget
    {R B coreNorm remainderNorm : ℝ}
    (hB : 0 < B)
    (hcore0 : 0 ≤ coreNorm)
    (hcore : coreNorm < R ^ 4)
    (hremainder : remainderNorm ≤ B)
    (hbudget : R ^ 4 * B ≤ 1) :
    coreNorm * remainderNorm < 1 := by
  have hfirst : coreNorm * remainderNorm ≤ coreNorm * B :=
    mul_le_mul_of_nonneg_left hremainder hcore0
  have hstrict : coreNorm * B < R ^ 4 * B :=
    mul_lt_mul_of_pos_right hcore hB
  exact lt_of_lt_of_le (lt_of_le_of_lt hfirst hstrict) hbudget

/-- Complex-valued consumer used pointwise along the quartic-core path. -/
theorem quarticCore_complex_factor_budget
    {R B : ℝ} {core remainder : ℂ}
    (hB : 0 < B)
    (hcore : ‖core‖ < R ^ 4)
    (hremainder : ‖remainder‖ ≤ B)
    (hbudget : R ^ 4 * B ≤ 1) :
    ‖core * remainder‖ < 1 := by
  rw [norm_mul]
  exact quarticCore_factor_budget hB (norm_nonneg _)
    hcore hremainder hbudget

/-- If `m` unselected roots are in the same radius-`R` disk as the quartic
core, their `2R` factor bounds give exactly `2^m R^(m+4)`. -/
theorem quarticCore_uniform_budget_identity (m : ℕ) (R : ℝ) :
    R ^ 4 * (2 * R) ^ m = (2 : ℝ) ^ m * R ^ (m + 4) := by
  rw [mul_pow, pow_add]
  ring

/-- Uniform-radius scalar fan-in for a quartic core and `m` remaining root
factors. -/
theorem quarticCore_uniform_factor_budget
    {m : ℕ} {R coreNorm remainderNorm : ℝ}
    (hR : 0 < R)
    (hcore0 : 0 ≤ coreNorm)
    (hcore : coreNorm < R ^ 4)
    (hremainder : remainderNorm ≤ (2 * R) ^ m)
    (hbudget : (2 : ℝ) ^ m * R ^ (m + 4) ≤ 1) :
    coreNorm * remainderNorm < 1 := by
  have htwoR : 0 < 2 * R := by positivity
  apply quarticCore_factor_budget (pow_pos htwoR m)
    hcore0 hcore hremainder
  simpa [quarticCore_uniform_budget_identity]

/-- Gaussian-rational arithmetic for the exact quintic strict-extension
certificate. -/
abbrev QuarticCoreRat := ℚ × ℚ

def qcSub (a b : QuarticCoreRat) : QuarticCoreRat :=
  (a.1 - b.1, a.2 - b.2)

def qcNormSq (a : QuarticCoreRat) : ℚ :=
  a.1 ^ 2 + a.2 ^ 2

def quarticCoreWitnessCenter : QuarticCoreRat := (-(3 / 10), 0)

def quarticCoreWitnessCore : Fin 4 → QuarticCoreRat :=
  ![(3 / 50, 12 / 25),
    (-(39 / 50), 9 / 25),
    (-(33 / 50), -(12 / 25)),
    (9 / 50, -(9 / 25))]

def quarticCoreWitnessFifth : QuarticCoreRat := (9 / 10, 0)

/-- The four selected roots lie on the radius-`3/5` circle about `-3/10`. -/
theorem quarticCoreWitness_core_radius :
    ∀ i, qcNormSq
      (qcSub (quarticCoreWitnessCore i) quarticCoreWitnessCenter) = (3 / 5) ^ 2 := by
  decide +kernel

/-- The unselected fifth root is at distance `6/5` from the core centre. -/
theorem quarticCoreWitness_fifth_distance :
    qcNormSq
      (qcSub quarticCoreWitnessFifth quarticCoreWitnessCenter) = (6 / 5) ^ 2 := by
  decide +kernel

/-- Every root of the exact witness lies strictly inside the unit disk. -/
theorem quarticCoreWitness_roots_inside :
    (∀ i, qcNormSq (quarticCoreWitnessCore i) < 1) ∧
      qcNormSq quarticCoreWitnessFifth < 1 := by
  decide +kernel

/-- No pair of witness roots satisfies the existing squared-distance
`5/9` quintic close-pair certificate. -/
theorem quarticCoreWitness_pairwiseSeparated :
    (∀ i j, i ≠ j →
      (5 : ℚ) / 9 < qcNormSq
        (qcSub (quarticCoreWitnessCore i) (quarticCoreWitnessCore j))) ∧
    (∀ i,
      (5 : ℚ) / 9 < qcNormSq
        (qcSub (quarticCoreWitnessCore i) quarticCoreWitnessFifth)) := by
  decide +kernel

/-- The full quintic factor budget of the exact witness is only
`(3/5)^4 (9/5) = 729/3125`. -/
theorem quarticCoreWitness_factor_budget :
    (3 / 5 : ℚ) ^ 4 * (9 / 5) = 729 / 3125 ∧
      (729 / 3125 : ℚ) < 1 := by
  decide +kernel

end ErdosProblems.Erdos1041
