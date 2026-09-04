/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #251 LCM-diagonal criterion

The package gives the exact order lattice of integral rational shifts, the
generic one-schedule irrationality criterion, and its canonical small LCM
diagonal specialization.
-/

namespace Erdos249257.ExternalVerification251LcmDiagonalCriterion

def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N

def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z

def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬ RealIntegral (realTailShift T h N)

def lcmDiagonalSchedule : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1)

/-- An integer-digit real dyadic orbit starts rationally exactly when one
positive tail difference is integral. -/
theorem notIrrationalInitial_iff_exists_integral_positive_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    ¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N) := by
  sorry

/-- The equivalent irrational form requires a nonintegral difference
cofinally for every fixed positive shift length. -/
theorem irrationalInitial_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalNonintegralTailShifts T := by
  sorry

/-- At a rational basepoint, the integral shift lengths are exactly the
multiples of the multiplicative order of two modulo the reduced denominator. -/
theorem tailShiftIntegral_iff_orderOf_dvd
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔
      orderOf (2 : ZMod (T N).den) ∣ h := by
  sorry

/-- Any positive schedule that eventually dominates every basepoint and is
eventually divisible by every positive shift length decides irrationality on
its own diagonal. -/
theorem irrationalInitial_iff_nonintegral_on_schedule
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (s : ℕ → ℕ)
    (hpos : ∀ j, 0 < s j)
    (hdvd : ∀ h : ℕ, 0 < h → ∃ J : ℕ, ∀ j : ℕ, J ≤ j → h ∣ s j)
    (hgrow : ∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → N ≤ s j) :
    Irrational (T 0) ↔
      ∀ j : ℕ, ¬ RealIntegral (realTailShift T (s j) (s j)) := by
  sorry

/-- A real dyadic integer-digit orbit has irrational initial value exactly
when every shift on the single LCM diagonal is nonintegral. -/
theorem irrationalInitial_iff_allLcmDiagonal_nonintegral
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ,
        ¬ RealIntegral
          (realTailShift T (lcmDiagonalSchedule j) (lcmDiagonalSchedule j)) := by
  sorry

end Erdos249257.ExternalVerification251LcmDiagonalCriterion
