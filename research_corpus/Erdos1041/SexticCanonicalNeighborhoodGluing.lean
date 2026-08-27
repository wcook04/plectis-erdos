import ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector
import ErdosProblems.Erdos1041.SexticNullBranchGlobalBoxAtlas
import Mathlib.Tactic

/-!
# Erdős #1041: exact gluing of the canonical transverse and null-box charts

The transverse selector closes energy at least `6075 β^4`.  Below that
threshold, every normalized coordinate is strictly smaller than `78 β^2`,
because `78^2 = 6084 > 6075`.  Thus the existing outer selector and complete
`[-78,78]^3` null-box atlas overlap without a parameter gap.
-/

namespace ErdosProblems.Erdos1041.SexticCanonicalNeighborhoodGluing

open ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector

/-- The scalar inequality behind the exact `6075`/`78` overlap. -/
theorem abs_lt_seventyEight_sq_of_sq_lt
    {x β : ℝ} (h : x ^ 2 < 6075 * β ^ 4) :
    |x| < 78 * β ^ 2 := by
  by_contra hnot
  have hbound : 78 * β ^ 2 ≤ |x| := le_of_not_gt hnot
  have hright : 0 ≤ |x| + 78 * β ^ 2 := by positivity
  have hprod : 0 ≤ (|x| - 78 * β ^ 2) * (|x| + 78 * β ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hbound) hright
  have habs : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith

/-- Every transverse point is either in the proved outer selector or in the
strict interior of the complete normalized null box. -/
theorem outer_or_nullBox
    (p q r β : ℝ) :
    6075 * β ^ 4 ≤ transverseEnergy p q r ∨
      (|p| < 78 * β ^ 2 ∧
       |q| < 78 * β ^ 2 ∧
       |r| < 78 * β ^ 2) := by
  by_cases houter : 6075 * β ^ 4 ≤ transverseEnergy p q r
  · exact Or.inl houter
  · right
    have henergy : transverseEnergy p q r < 6075 * β ^ 4 :=
      lt_of_not_ge houter
    have hp : p ^ 2 < 6075 * β ^ 4 := by
      unfold transverseEnergy at henergy
      nlinarith [sq_nonneg q, sq_nonneg r]
    have hq : q ^ 2 < 6075 * β ^ 4 := by
      unfold transverseEnergy at henergy
      nlinarith [sq_nonneg p, sq_nonneg r]
    have hr : r ^ 2 < 6075 * β ^ 4 := by
      unfold transverseEnergy at henergy
      nlinarith [sq_nonneg p, sq_nonneg q]
    exact ⟨abs_lt_seventyEight_sq_of_sq_lt hp,
      abs_lt_seventyEight_sq_of_sq_lt hq,
      abs_lt_seventyEight_sq_of_sq_lt hr⟩

/-- Abstract fan-in: any conclusion proved on the outer selector and on the
normalized null box holds throughout the canonical transverse chart. -/
theorem canonicalChart_fanIn
    {P : Prop} {p q r β : ℝ}
    (houter : 6075 * β ^ 4 ≤ transverseEnergy p q r → P)
    (hbox : |p| < 78 * β ^ 2 →
      |q| < 78 * β ^ 2 → |r| < 78 * β ^ 2 → P) :
    P := by
  rcases outer_or_nullBox p q r β with hout | ⟨hp, hq, hr⟩
  · exact houter hout
  · exact hbox hp hq hr

end ErdosProblems.Erdos1041.SexticCanonicalNeighborhoodGluing
