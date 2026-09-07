import Erdos257PeriodNoncollapse.TotientActualLcmOrbitSeparation

/-!
# Exact actual-LCM orbit frontier for Erdős #249

The quantitative separation predicate in
`TotientActualLcmOrbitSeparation` is sufficient for the existing signed-margin
endpoint, but the exact arithmetic frontier is simply cofinal
non-integrality of the actual LCM-diagonal tail orbit.  This file records that
the latter condition is equivalent to irrationality of the totient series.
-/

namespace Erdos257PeriodNoncollapse
namespace DiagonalFreshLossBridge
namespace PowerTwoOddWindowAffine

open TotientTailPeriodKiller

/-- Cofinal non-integrality of the actual power-two LCM-diagonal tail orbit. -/
def PowerTwoActualLcmOrbitNonintegralitySupply : Prop :=
  ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ)

/-- Irrationality makes every actual power-two LCM-diagonal tail orbit a
non-integer. -/
theorem actualLcmTailOrbit_notMem_int_of_irrational
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
    (a : ℕ) :
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ) := by
  have hheight : 0 < actualLcmHeight a := periodLcm_pos _
  simpa only [actualLcmTailOrbit, two_mul] using
    (irrational_totient_series_iff_all_tail_diffs_nonintegral.mp hirr
      (actualLcmHeight a) hheight (actualLcmHeight a))

/-- The exact power-two actual-LCM orbit frontier is equivalent to Erdős
#249. -/
theorem irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      PowerTwoActualLcmOrbitNonintegralitySupply := by
  constructor
  · intro hirr a₀
    exact ⟨a₀, le_rfl, actualLcmTailOrbit_notMem_int_of_irrational hirr a₀⟩
  · intro hsupply
    refine irrational_totient_series_of_lcm_diagonal_nonintegrality_supply fun t₀ => ?_
    obtain ⟨a, ha, hnon⟩ := hsupply t₀
    have hat : a < 2 ^ a := Nat.lt_two_pow_self
    refine ⟨2 ^ a, ha.trans hat.le, ?_⟩
    simpa only [actualLcmTailOrbit, actualLcmHeight, two_mul] using hnon

/-- Cofinal actual-LCM orbit non-integrality closes the irrationality
endpoint directly, without a quantitative separation hypothesis. -/
theorem irrational_totientSeries_of_actualLcmOrbitNonintegralitySupply
    (hsupply : PowerTwoActualLcmOrbitNonintegralitySupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply.mpr hsupply

#print axioms actualLcmTailOrbit_notMem_int_of_irrational
#print axioms irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply
#print axioms irrational_totientSeries_of_actualLcmOrbitNonintegralitySupply

end PowerTwoOddWindowAffine
end DiagonalFreshLossBridge
end Erdos257PeriodNoncollapse
