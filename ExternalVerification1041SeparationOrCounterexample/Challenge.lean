/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 separation-or counterexample

The Challenge states the displayed proposition of the short note over Mathlib
alone. It does not import the project-local module and does not use its
namespace vocabulary: the positive-ray relation and the least critical modulus
are written out.

The statement exhibits a monic cubic whose critical values sit on distinct
positive rays while their normalised separation is far below two. It refutes a
covering reading of a separation criterion. It says nothing about Erdős
Problem #1041 itself, which is open.
-/

namespace Erdos249257.ExternalVerification1041SeparationOrCounterexample

open Polynomial

/- A monic cubic with all zeros in the open unit disc, two simple critical
points, least critical modulus above `13/25`, critical values on distinct
positive rays, and normalised critical-value separation below `2/375`. -/
theorem separation_or_counterexample :
    ∃ f : ℂ[X], f.Monic ∧ f.natDegree = 3 ∧
      (∀ z : ℂ, f.eval z = 0 → ‖z‖ < 1) ∧
      ∃ cp cm : ℂ, cp ≠ cm ∧
        (∀ z : ℂ, f.derivative.eval z = 0 ↔ z = cp ∨ z = cm) ∧
        (∀ z : ℂ, f.derivative.eval z = 0 →
          f.derivative.derivative.eval z ≠ 0) ∧
        IsLeast {x : ℝ | ∃ c : ℂ, f.derivative.eval c = 0 ∧ x = ‖f.eval c‖}
          ‖f.eval cp‖ ∧
        (13 / 25 : ℝ) < ‖f.eval cp‖ ∧
        (¬ ∃ r : ℝ, 0 < r ∧ f.eval cm = (r : ℂ) * f.eval cp) ∧
        ‖1 - f.eval cm / f.eval cp‖ < 2 / 375 ∧
        (2 / 375 : ℝ) < 2 := by
  sorry

end Erdos249257.ExternalVerification1041SeparationOrCounterexample
