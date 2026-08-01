import ErdosProblems.Erdos68.CanonicalFactorialDigits
import Mathlib.Data.Rat.Floor

/-!
# Erdős #68: finite residual-centre defect automaton

The returned packet introduces a finite rational centre `F_m`, its ceiling
`Z_m`, gap `delta_m = Z_m - F_m`, and an integer code

`q_m = m Z_(m-1) + 1 - C_m - Z_m`.

This module isolates and kernel-checks the complete algebraic transport from
the centre recurrence

`F_m = m F_(m-1) + 1 + epsilon_m - C_m`

to the floor code and gap recurrence.  The theorem is stated for arbitrary
exact rational centre and coefficient sequences, so the later series-specific
finite-sum identity can plug into it without repeating any rounding argument.
-/

namespace ErdosProblems.Erdos68

/-- Integer ceiling of a finite rational centre. -/
def centreCeil (F : ℕ → ℚ) (m : ℕ) : ℤ :=
  ⌈F m⌉

/-- Distance from a finite rational centre to its ceiling. -/
def centreGap (F : ℕ → ℚ) (m : ℕ) : ℚ :=
  (centreCeil F m : ℚ) - F m

/-- Integer defect code associated with a centre sequence and integer
coefficient sequence. -/
def centreDefectCode (F : ℕ → ℚ) (C : ℕ → ℤ) (m : ℕ) : ℤ :=
  (m : ℤ) * centreCeil F (m - 1) + 1 - C m - centreCeil F m

/-- The packet's explicit factorial error term. -/
def factorialEpsilon (m : ℕ) : ℚ :=
  1 / ((m.factorial : ℚ) - 1)

/-- A centre gap is always nonnegative. -/
theorem centreGap_nonneg (F : ℕ → ℚ) (m : ℕ) :
    0 ≤ centreGap F m := by
  unfold centreGap centreCeil
  exact sub_nonneg.mpr (Int.le_ceil _)

/-- A centre gap is always strictly below one. -/
theorem centreGap_lt_one (F : ℕ → ℚ) (m : ℕ) :
    centreGap F m < 1 := by
  unfold centreGap centreCeil
  linarith [Int.ceil_lt_add_one (F m)]

/-- The exact centre recurrence turns the integer code into the floor of the
previous rescaled gap. -/
theorem centreDefectCode_eq_floor
    (F : ℕ → ℚ) (C : ℕ → ℤ) (epsilon : ℕ → ℚ) (m : ℕ)
    (hrec :
      F m =
        (m : ℚ) * F (m - 1) + 1 + epsilon m - (C m : ℚ)) :
    centreDefectCode F C m =
      ⌊(m : ℚ) * centreGap F (m - 1) - epsilon m⌋ := by
  have hid :
      (m : ℚ) * centreGap F (m - 1) - epsilon m =
        (centreDefectCode F C m : ℚ) + centreGap F m := by
    unfold centreGap centreDefectCode centreCeil
    push_cast
    linarith
  rw [hid, add_comm, Int.floor_add_intCast]
  have hfloor : ⌊centreGap F m⌋ = 0 := by
    rw [Int.floor_eq_iff]
    exact ⟨centreGap_nonneg F m, by simpa using centreGap_lt_one F m⟩
  rw [hfloor]
  simp

/-- Exact fractional recurrence for the centre gap and defect code. -/
theorem centreGap_recurrence
    (F : ℕ → ℚ) (C : ℕ → ℤ) (epsilon : ℕ → ℚ) (m : ℕ)
    (hrec :
      F m =
        (m : ℚ) * F (m - 1) + 1 + epsilon m - (C m : ℚ)) :
    centreGap F m =
      (m : ℚ) * centreGap F (m - 1) - epsilon m -
        (centreDefectCode F C m : ℚ) := by
  unfold centreGap centreDefectCode centreCeil
  push_cast
  linarith

/-- Specialization to the factorial error `1 / (m! - 1)` appearing in the
Erdős #68 finite centre. -/
theorem centreDefectCode_eq_factorial_floor
    (F : ℕ → ℚ) (C : ℕ → ℤ) (m : ℕ)
    (hrec :
      F m =
        (m : ℚ) * F (m - 1) + 1 + factorialEpsilon m -
          (C m : ℚ)) :
    centreDefectCode F C m =
      ⌊(m : ℚ) * centreGap F (m - 1) -
        1 / ((m.factorial : ℚ) - 1)⌋ := by
  simpa [factorialEpsilon] using
    centreDefectCode_eq_floor F C factorialEpsilon m hrec

/-- The corresponding factorial-error gap recurrence. -/
theorem centreGap_factorial_recurrence
    (F : ℕ → ℚ) (C : ℕ → ℤ) (m : ℕ)
    (hrec :
      F m =
        (m : ℚ) * F (m - 1) + 1 + factorialEpsilon m -
          (C m : ℚ)) :
    centreGap F m =
      (m : ℚ) * centreGap F (m - 1) -
        1 / ((m.factorial : ℚ) - 1) -
        (centreDefectCode F C m : ℚ) := by
  simpa [factorialEpsilon] using
    centreGap_recurrence F C factorialEpsilon m hrec

end ErdosProblems.Erdos68
