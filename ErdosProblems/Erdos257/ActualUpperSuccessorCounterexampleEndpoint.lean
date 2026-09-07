import ErdosProblems.Erdos257.FatalCriticalDangerEndpointReduction
import ErdosProblems.Erdos257.HalfCounterexampleFrontier

/-!
# Erdős #257: actual upper-successor counterexample endpoint

The realized upper/right-run analysis reaches half-membership from the exact
`SeamActualUpperSuccessorLinearEscape` hypothesis.  This module propagates
that result to the problem-level endpoint: an infinite reciprocal-Mersenne
support of exact value `1/2`, and hence failure of the universal irrationality
assertion.

No successor-linear escape certificate is constructed here.  The theorems
are conditional consequences of that open producer and do not solve Erdős
Problem 257.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse

/-- The realized-run successor lower bound produces an infinite rational
counterexample of exact value `1/2`. -/
theorem exists_rational_half_counterexample_of_actualUpperSuccessorLinearEscape
    (hescape : SeamActualUpperSuccessorLinearEscape) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  obtain ⟨A, hA0, hhalf⟩ :=
    half_mem_mersenneAchievementSet_of_actualUpperSuccessorLinearEscape
      hescape
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hhalf.symm
  refine ⟨A, ?_, hseries⟩
  intro hfinite
  exact
    Erdos257PeriodNoncollapse.HalfCarryReachability.finite_boolSupport_ne_half
      A hfinite hA0 hseries

/-- Consequently the realized-run successor lower bound negates the universal
irrationality assertion in Erdős Problem 257. -/
theorem not_universal_of_actualUpperSuccessorLinearEscape
    (hescape : SeamActualUpperSuccessorLinearEscape) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  obtain ⟨A, hA, hhalf⟩ :=
    exists_rational_half_counterexample_of_actualUpperSuccessorLinearEscape
      hescape
  intro huniversal
  have hirr := huniversal A hA
  rw [hhalf] at hirr
  have hcast : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by norm_num
  rw [hcast] at hirr
  exact (Rat.not_irrational (1 / 2 : ℚ)) hirr

/-- Composite problem-level endpoint intended for exact external comparison.
It conjoins the infinite-support half-value witness with the resulting
refutation of universal irrationality, without weakening the realized-run
successor hypothesis. -/
theorem actualUpperSuccessorLinearEscape_completeCounterexample
    (hescape : SeamActualUpperSuccessorLinearEscape) :
    (∃ A : Set ℕ, A.Infinite ∧
        erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
      ¬ UniversalMersenneSubseriesIrrationality :=
  ⟨exists_rational_half_counterexample_of_actualUpperSuccessorLinearEscape
      hescape,
    not_universal_of_actualUpperSuccessorLinearEscape hescape⟩

#print axioms exists_rational_half_counterexample_of_actualUpperSuccessorLinearEscape
#print axioms not_universal_of_actualUpperSuccessorLinearEscape
#print axioms actualUpperSuccessorLinearEscape_completeCounterexample

end ErdosProblems.Erdos257
