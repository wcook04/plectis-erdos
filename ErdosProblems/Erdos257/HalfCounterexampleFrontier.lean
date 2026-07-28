import Erdos249257.TerminalOnlyScaledVanishing
import Mathlib.NumberTheory.Real.Irrational

/-!
# Erdős #257: the rational-half counterexample frontier

The legacy half-carry development contains a much stronger endpoint than the
problem-centric packet previously exposed.  A cofinal family of finite words
with terminal carry negligible on the binary scale produces an infinite
support whose reciprocal-Mersenne subseries is exactly `1/2`.  Hence that
producer would *disprove*, rather than prove, the universal irrationality
assertion.

This module gives that endpoint a short problem-centric interface.  It does
not assert the remaining producer: the deterministic suffix-cylinder orbit
has only been checked to a large finite cutoff.
-/

namespace ErdosProblems.Erdos257

open Erdos249257
open Erdos249257.HalfCarryReachability

/-- The universal irrationality assertion in Erdős #257. -/
def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

/-- Any terminal scaled-vanishing sequence supplies an infinite rational
counterexample of exact value `1/2`. -/
theorem exists_rational_half_counterexample_of_terminalScaledVanishing
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 :=
  exists_infinite_support_half_of_terminalScaledVanishing S

/-- The same producer negates the original universal irrationality claim. -/
theorem not_universal_of_terminalScaledVanishing
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  obtain ⟨A, hA, hhalf⟩ :=
    exists_rational_half_counterexample_of_terminalScaledVanishing S
  intro huniversal
  have hirr := huniversal A hA
  rw [hhalf] at hirr
  have hcast : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by norm_num
  rw [hcast] at hirr
  exact (Rat.not_irrational (1 / 2 : ℚ)) hirr

end ErdosProblems.Erdos257
