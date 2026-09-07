/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041SeparationOrCounterexample.Statements
import ErdosProblems.Erdos1041.PaperSeparationCounterexample

/-!
# Source transport for the #1041 separation-or counterexample

The witness is the project-local cubic `z ^ 3 + (3/100) z - 3/4`. Its critical
points, critical values, least critical modulus, ray separation and normalised
separation bound are the local theorems; this file only supplies the witness
and rewrites the local `SamePositiveRay` predicate into its definition.
-/

namespace Erdos249257.ExternalVerification1041SeparationOrCounterexample

open Polynomial

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
  obtain ⟨hmonic, hdeg, hroots, hcrit, hne, hsimple, hleast, hmu, hrays,
    hsep, htwo⟩ :=
    ErdosProblems.Erdos1041.PaperSeparationCounterexample.complete_sep_or_counterexample
  refine ⟨ErdosProblems.Erdos1041.PaperSeparationCounterexample.P, hmonic, hdeg,
    hroots, ErdosProblems.Erdos1041.PaperSeparationCounterexample.plus,
    ErdosProblems.Erdos1041.PaperSeparationCounterexample.minus, hne, hcrit,
    hsimple, ?_, ?_, ?_, hsep, htwo⟩
  · exact hleast
  · exact hmu
  · exact hrays

end Erdos249257.ExternalVerification1041SeparationOrCounterexample
