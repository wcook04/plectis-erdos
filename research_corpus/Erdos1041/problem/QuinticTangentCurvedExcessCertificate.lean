import ErdosProblems.Erdos1041.QuinticTraceMaxUniversalChamber

/-!
# Erdős 1041: algebra for the tangent curved-excess certificate

The analytic input is the support--oscillation lemma and the exact
Sturm/interval certificate replayed by the companion Python checker.  This
module checks the new critical-gap collapse, tangent level-set factorization,
and final rational fan-in.
-/

namespace ErdosProblems.Erdos1041

/-- On the other-critical cubic, the fixed quintic critical gap collapses
further to a quadratic expression involving the chamber parameter. -/
theorem quintic_universal_critical_gap_quadratic
    (μ x : ℂ)
    (hx : 5 * x ^ 3 + 20 * x ^ 2 + 30 * x + 20 + 2 * μ = 0) :
    (1 / 2 : ℂ) * x ^ 3 * (3 * x ^ 2 + 10 * x + 10) =
      x * (2 * μ + 20 - 3 * μ * x) / 5 := by
  linear_combination (3 * x ^ 2 / 10 - x / 5) * hx

/-- The real part of the tangent normal-form level equation factors through
the square of the displacement from the critical hub. -/
theorem quintic_tangent_level_factor
    (A t h : ℝ)
    (hh : h ^ 2 + 2 * h - 2 = 0) :
    let a := h + A
    let b := A * t
    let P :=
      A ^ 3 * (5 * (t ^ 2) ^ 2 - 10 * t ^ 2 + 1)
        + 5 * h * A ^ 2 * ((t ^ 2) ^ 2 - 6 * t ^ 2 + 1)
        + 20 * (1 - h) * A * (1 - 3 * t ^ 2)
        + 60 * h * (1 - t ^ 2)
    (a ^ 5 - 10 * a ^ 3 * b ^ 2 + 5 * a * b ^ 4
          + 40 * (a ^ 2 - b ^ 2) - 60 * a)
        - (h ^ 5 + 40 * h ^ 2 - 60 * h) = A ^ 2 * P := by
  dsimp
  linear_combination
    -5 * A *
      (6 * A ^ 2 * t ^ 2 - 2 * A ^ 2 + 2 * A * h * t ^ 2
        - 2 * A * h - 4 * A * t ^ 2 + 4 * A - h ^ 2 + 2 * h - 6) * hh

/-- Exact arithmetic at the fan-in of the two support--oscillation bounds. -/
theorem quintic_tangent_curved_excess_rational_fanin :
    (2401 : ℚ) / 10000 *
          ((732051 / 1000000) * (309018 / 1000000) + 2 * (277 / 1000))
        - (73205 / 100000) * (951056 / 1000000)
        + (57 / 500) *
          ((732051 / 1000000) * (809018 / 1000000) + 2 * (63 / 2000))
        + (732051 / 1000000) * (587786 / 1000000) =
      -19517458527181 / 5000000000000000 ∧
    (-19517458527181 : ℚ) / 5000000000000000 < 0 := by
  norm_num

end ErdosProblems.Erdos1041
