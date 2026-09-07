import Erdos257PeriodNoncollapse.HalfUpperResetCriticalBand

/-!
# Missing charge-range hypothesis in the abstract critical-band iff

Uncompiled literal no-go for long `prop:critical-band-index`. Uses the actual
library predicates: at d=0,E=3 all bands are already below E, while no critical
index exists. It does not refute the correctly guarded library theorem or its
concrete seam specialisation.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR7
open Erdos257PeriodNoncollapse.HalfUpperResetCriticalBand

/-- A finite counterexample to dropping E ≤ 2^(d+1). -/
theorem critical_band_range_counterexample :
    DyadicBandEscape 0 3 ∧
      ¬ ∃ j : ℕ, CriticalDyadicBandIndex 0 3 j ∧
        3 + 2 * (0 + j) ≤ 2 ^ (0 - j + 1) := by
  constructor
  · intro j hj
    left
    norm_num
  · rintro ⟨j, hindex, _⟩
    have hbound := hindex.2.1
    norm_num at hbound

/-- The globally quantified, unguarded iff is false. -/
theorem critical_band_equivalence_requires_range :
    ¬ (∀ d E : ℕ, DyadicBandEscape d E ↔
      ∃ j : ℕ, CriticalDyadicBandIndex d E j ∧
        E + 2 * (d + j) ≤ 2 ^ (d - j + 1)) := by
  intro h
  exact critical_band_range_counterexample.2
    ((h 0 3).mp critical_band_range_counterexample.1)

end ErdosProblems.Erdos257.PaperCompleteR7
