/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #251 signed-window and circularity family

These exact recurrence-level theorems classify the adjacent unit-window event
and show that two proposed cofinal escape tests are equivalent to the
non-eventual-integrality conclusion they were intended to establish.
-/

namespace Erdos249257.ExternalVerification251AffineCircularity

def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ := T (N + h) - T N

def RatIntegral (x : ℚ) : Prop := ∃ z : ℤ, x = z

def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | r + 1 => 2 * dyadicTailBlock g N r + g (N + r + 1)

def RatAffinePowTwo (x : ℚ) (c : ℤ) (r : ℕ) : Prop :=
  ∃ z : ℤ, x = ((((2 : ℤ) ^ (r + 1)) * z - c : ℤ) : ℚ)

def shiftDigit (g : ℕ → ℤ) (h n : ℕ) : ℤ := g (n + h) - g n

def DyadicScaleDominates (bound : ℕ → ℚ) : Prop :=
  ∀ N q : ℕ, 0 < q → ∃ r : ℕ, 2 * bound (N + r) * q < 2 ^ r

/-- The two adjacent unit windows and an even nonzero difference digit are
exactly one of the two signed `±2` half-window configurations. -/
theorem adjacent_small_mismatch_iff_signed_two_window
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (-1 < tailShift T h N ∧ tailShift T h N < 1 ∧
        -1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1 ∧
        g (N + h + 1) ≠ g (N + 1)) ↔
      ((g (N + h + 1) - g (N + 1) = 2 ∧
          1 / 2 < tailShift T h N ∧ tailShift T h N < 1) ∨
        (g (N + h + 1) - g (N + 1) = -2 ∧
          -1 < tailShift T h N ∧ tailShift T h N < -(1 / 2))) := by
  sorry

/-- Under even difference digits, the cofinal data-dependent affine-cylinder
escape is equivalent to non-eventual integrality of the fixed shift. -/
theorem cofinal_affinePowTwo_escape_iff_not_eventuallyIntegral
    {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (hdiffEven : ∀ N, ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
        ¬ RatAffinePowTwo (tailShift T h (N + r))
          (dyadicTailBlock (shiftDigit g h) N r) r) ↔
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  sorry

/-- Under an exact terminal bound and dyadic domination, cofinal escape from
the fixed lattice `2^r * ℤ` is likewise equivalent to non-eventual
integrality. -/
theorem cofinal_blockResidue_escape_iff_not_eventuallyIntegral
    {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (bound : ℕ → ℚ)
    (hbound : ∀ N, |tailShift T h N| ≤ bound N)
    (hscale : DyadicScaleDominates bound) :
    (∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
      ∀ z : ℤ, bound (N + r) <
        |((dyadicTailBlock (shiftDigit g h) N r : ℤ) : ℚ) -
          2 ^ r * (z : ℚ)|) ↔
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  sorry

end Erdos249257.ExternalVerification251AffineCircularity
