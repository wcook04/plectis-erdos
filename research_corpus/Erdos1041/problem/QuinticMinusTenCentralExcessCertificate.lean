import ErdosProblems.Erdos1041.QuinticTraceMaxUniversalChamber

/-!
# Erdős 1041: algebra for the central `μ = -10` curved-excess certificate

The analytic input is the support--oscillation lemma and the exact rational
interval certificate replayed by the companion Python checker.  This module
checks the singular cubic normal form, its quadratic level-curve equation,
the terminal-factor identity, and the final rational fan-in.
-/

namespace ErdosProblems.Erdos1041

/-- At `μ=-10`, the universal quintic has a triple zero and its derivative
has the corresponding double critical point. -/
theorem quintic_minusTen_cubic_degeneracy (x : ℂ) :
    x ^ 2 * (x ^ 3 + 5 * x ^ 2 + 10 * x) =
      x ^ 3 * (x ^ 2 + 5 * x + 10) ∧
    x * (5 * x ^ 3 + 20 * x ^ 2 + 30 * x) =
      5 * x ^ 2 * (x ^ 2 + 4 * x + 6) := by
  constructor <;> ring

/-- After writing `x=a+ib`, the non-real component of `F_{-10}(x)=0 mod ℝ`
is `b` times this quartic. -/
theorem quintic_minusTen_level_curve_factor (a b : ℝ) :
    5 * a ^ 4 * b + 20 * a ^ 3 * b - 10 * a ^ 2 * b ^ 3
        + 30 * a ^ 2 * b - 20 * a * b ^ 3 + b ^ 5 - 10 * b ^ 3 =
      b *
        (5 * a ^ 4 + 20 * a ^ 3 - 10 * a ^ 2 * b ^ 2
          + 30 * a ^ 2 - 20 * a * b ^ 2 + b ^ 4 - 10 * b ^ 2) := by
  ring

/-- With `a=bt`, the selected conjugate level curve is quadratic in `b`. -/
theorem quintic_minusTen_level_curve_radial (t b : ℝ) :
    5 * (b * t) ^ 4 + 20 * (b * t) ^ 3
        - 10 * (b * t) ^ 2 * b ^ 2 + 30 * (b * t) ^ 2
        - 20 * (b * t) * b ^ 2 + b ^ 4 - 10 * b ^ 2 =
      b ^ 2 *
        ((5 * t ^ 4 - 10 * t ^ 2 + 1) * b ^ 2
          + 20 * t * (t ^ 2 - 1) * b + 10 * (3 * t ^ 2 - 1)) := by
  ring

/-- The `w=1` terminal comparison factors after `t=ku`, modulo the exact
terminal-direction equation `5k⁴-10k²+1=0`. -/
theorem quintic_minusTen_terminal_one_factor
    (k u : ℝ) (hk : 5 * k ^ 4 - 10 * k ^ 2 + 1 = 0) :
    30 * k ^ 2 * (k * u) ^ 2 - 10 * k ^ 2
        - 40 * k * (k * u) ^ 3 + 15 * (k * u) ^ 4 + 1 =
      (10 * k ^ 2 - 1) * (u - 1) ^ 3 * (3 * u + 1) := by
  linear_combination u ^ 2 * (3 * u ^ 2 - 8 * u + 6) * hk

/-- Exact arithmetic at the support--oscillation fan-in.  The analytic
certificate supplies weighted transverse budget `<309/1000`, terminal slope
`>324919696232906/10^15`, and terminal direction cosine `>951/1000`. -/
theorem quintic_minusTen_central_excess_rational_fanin :
    2 * (951 : ℚ) / 1000 *
          (309 / 1000 - 324919696232906 / 1000000000000000) <
        -2853 / 100000 ∧
      (-2853 : ℚ) / 100000 < 0 := by
  norm_num

end ErdosProblems.Erdos1041
