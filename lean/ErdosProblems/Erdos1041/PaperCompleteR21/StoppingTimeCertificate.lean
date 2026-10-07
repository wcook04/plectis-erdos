import Mathlib

/-!
# Erdős 1041: the closing inequalities at the recorded stopping time

The long paper's low-critical section (`paper/reasoning-parts/erdos1041/core.tex`,
lines 679–685) records a terminal time `X = 635762889599/10^12` for the
area-growth certificate and asserts, as the arithmetic that turns that
stopping time into the two stated cutoffs,

    (13/25) e^X < 0.982000386 < 1    and    (529/1000) e^X < 0.998996547 < 1.

Both are proved here, with no `native_decide` and no appeal to the external
exact-arithmetic program.  The paper reaches them through the majorant
`e^X ≤ ∑_{j≤14} X^j/j! + (X^15/15!)/(1 - X/16)`; the proof below instead uses
Mathlib's `Real.exp_bound'`, whose tail `X^15·16/(15!·15)` is the larger of the
two for `0 < X < 1`, so the same two conclusions follow from a weaker
majorant.  The margins are thin: `0.982000386 - (13/25)e^X ≈ 2.5·10^{-10}`.

This is one named ingredient of Theorem `res:low-critical-thirteen-twentyfifths`
(the "rational certificate" step); it is not that theorem, whose analytic chain
still needs the Riemann mapping theorem, the component-wise Blaschke identity,
the hyperbolic packing bound, the coarea formula and Pólya's area inequality.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

/-- The terminal time recorded by the area-growth certificate. -/
def stoppingTime : ℝ := 635762889599 / 10 ^ 12

theorem stoppingTime_nonneg : 0 ≤ stoppingTime := by
  unfold stoppingTime
  norm_num

theorem stoppingTime_le_one : stoppingTime ≤ 1 := by
  unfold stoppingTime
  norm_num

/-- Fifteen-term Taylor majorant, evaluated in exact rational arithmetic. -/
theorem exp_stoppingTime_lt :
    Real.exp stoppingTime < 1888462280288 / 10 ^ 12 := by
  refine lt_of_le_of_lt
    (Real.exp_bound' stoppingTime_nonneg stoppingTime_le_one (n := 15) (by norm_num)) ?_
  simp only [stoppingTime, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]

/-- The cutoff the theorem states. -/
theorem thirteen_twentyfifths_exp_stoppingTime_lt :
    (13 / 25 : ℝ) * Real.exp stoppingTime < 0.982000386 := by
  have h := exp_stoppingTime_lt
  nlinarith [h]

theorem thirteen_twentyfifths_exp_stoppingTime_lt_one :
    (13 / 25 : ℝ) * Real.exp stoppingTime < 1 :=
  lt_trans thirteen_twentyfifths_exp_stoppingTime_lt (by norm_num)

/-- The wider cutoff the same recorded output also covers. -/
theorem five_hundred_twentynine_thousandths_exp_stoppingTime_lt :
    (529 / 1000 : ℝ) * Real.exp stoppingTime < 0.998996547 := by
  have h := exp_stoppingTime_lt
  nlinarith [h]

theorem five_hundred_twentynine_thousandths_exp_stoppingTime_lt_one :
    (529 / 1000 : ℝ) * Real.exp stoppingTime < 1 :=
  lt_trans five_hundred_twentynine_thousandths_exp_stoppingTime_lt (by norm_num)

#print axioms exp_stoppingTime_lt
#print axioms thirteen_twentyfifths_exp_stoppingTime_lt
#print axioms thirteen_twentyfifths_exp_stoppingTime_lt_one
#print axioms five_hundred_twentynine_thousandths_exp_stoppingTime_lt
#print axioms five_hundred_twentynine_thousandths_exp_stoppingTime_lt_one

end ErdosProblems.Erdos1041.PaperCompleteR21
