import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCarryReachability

/-!
Paper-form restatements of two asserted environments from the long
Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`.

* `prop:achievement-set-topology` (`a257_front.tex:3763`), "Achievement-set
  topology: compact, closed, perfect, measure exactly one":
  `paper_achievement_set_topology`.
* `record:257bm-i10` (`a257_front.tex:4611`), "No finite support has value one
  half": `paper_no_finite_support_has_value_half`,
  `paper_half_representing_support_infinite`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.HalfCarryReachability Set MeasureTheory

/-! ## `prop:achievement-set-topology` -/

/-- Paper display of `prop:achievement-set-topology`: `𝒜` is compact --
explicitly as the continuous image of the binary-sequence Cantor space
`ℕ → Fin 2` under `positiveMersenneDigitValue` -- hence closed; it is also
perfect, totally disconnected and nowhere dense, with Lebesgue measure
exactly `1`. -/
theorem paper_achievement_set_topology :
    Continuous positiveMersenneDigitValue ∧
      Set.range positiveMersenneDigitValue = mersenneAchievementSet ∧
      IsCompact mersenneAchievementSet ∧
      IsClosed mersenneAchievementSet ∧
      Perfect mersenneAchievementSet ∧
      IsTotallyDisconnected mersenneAchievementSet ∧
      IsNowhereDense mersenneAchievementSet ∧
      volume mersenneAchievementSet = 1 :=
  ⟨continuous_positiveMersenneDigitValue,
    range_positiveMersenneDigitValue_eq,
    isCompact_mersenneAchievementSet,
    isClosed_mersenneAchievementSet,
    perfect_mersenneAchievementSet,
    isTotallyDisconnected_mersenneAchievementSet,
    isNowhereDense_mersenneAchievementSet,
    volume_mersenneAchievementSet⟩

/-! ## `record:257bm-i10` -/

/-- Paper display of `record:257bm-i10`: a finite sum of reciprocals of the
odd integers `2^a - 1` has odd denominator in lowest terms, so it cannot equal
`1/2`. -/
theorem paper_no_finite_support_has_value_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2 :=
  finite_boolSupport_ne_half A hfinite hzero

/-- The consequence the paper draws in the same environment: a support
representing `1/2` must be infinite. -/
theorem paper_half_representing_support_infinite
    (A : Set ℕ) (hzero : 0 ∉ A)
    (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2) :
    A.Infinite :=
  fun hfinite ↦ finite_boolSupport_ne_half A hfinite hzero hvalue

#print axioms paper_achievement_set_topology
#print axioms paper_no_finite_support_has_value_half
#print axioms paper_half_representing_support_infinite

end ErdosProblems.Erdos257.PaperCompleteR21
