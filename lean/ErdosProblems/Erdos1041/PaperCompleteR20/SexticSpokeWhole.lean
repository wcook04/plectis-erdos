import ErdosProblems.Erdos1041.AbelControlPolygon

/-! The full existential sextic example: roots in the open unit disc and
an actual interior point of the radial segment to a root outside the sublevel. -/

namespace ErdosProblems.Erdos1041.PaperCompleteR20
open AbelControlPolygon

theorem sextic_spoke_counterexample_whole :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ w : ℂ, sextic (r : ℂ) w = 0 → ‖w‖ < 1) ∧
      sextic (r : ℂ) (r : ℂ) = 0 ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        1 < ‖sextic (r : ℂ) ((t : ℂ) * (r : ℂ))‖ := by
  let r : ℝ := 999 / 1000
  have hr : 0 < r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  have hbig : 320 / 327 < r ^ 6 := by norm_num [r]
  have H := sextic_guardrail hr hr1 hbig
  refine ⟨r, hr, hr1, H.1, ?_, 1 / 2, by norm_num, by norm_num, ?_⟩
  · rw [sextic_factor]
    simp
  · have hp : (((1 / 2 : ℝ) : ℂ) * (r : ℂ)) = (r : ℂ) / 2 := by
      push_cast
      ring
    rw [hp]
    exact H.2

#print axioms sextic_spoke_counterexample_whole

end ErdosProblems.Erdos1041.PaperCompleteR20
