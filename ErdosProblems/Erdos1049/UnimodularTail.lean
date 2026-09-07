import ErdosProblems.Erdos1049.BezoutPluckerJets

/-!
# Adjacent minors with unimodular rows

The coordinate that is invertible need not be the same along a tail. In fact,
neither coordinate need be invertible: a Bézout identity for each row suffices.
For example, `(2,3)` is unimodular modulo six, although neither entry is a unit.
The middle row's Bézout identity is precisely what lets two adjacent vanishing
minors imply the outer minor vanishes, even over rings with zero divisors.

This strengthens the algebraic input to the endpoint selector collision.
It supplies no analytic remainder or nonvanishing assertion for Erdős #1049.
-/

namespace ErdosProblems.Erdos1049.BezoutPluckerJets

variable {R : Type*} [CommRing R]

/-- Only the middle row needs to be unimodular to propagate across two edges. -/
theorem det_zero_trans_of_middle_isCoprime (u v w : R × R)
    (hv : IsCoprime v.1 v.2)
    (huv : u.1 * v.2 - u.2 * v.1 = 0)
    (hvw : v.1 * w.2 - v.2 * w.1 = 0) :
    u.1 * w.2 - u.2 * w.1 = 0 := by
  have hvu : v.1 * u.2 - v.2 * u.1 = 0 := by
    calc
      v.1 * u.2 - v.2 * u.1 = -(u.1 * v.2 - u.2 * v.1) := by ring
      _ = 0 := by rw [huv]; ring
  obtain ⟨a, ha₁, ha₂⟩ := exists_scalar_eq_of_det_eq_zero hv hvu
  obtain ⟨b, hb₁, hb₂⟩ := exists_scalar_eq_of_det_eq_zero hv hvw
  rw [ha₁, ha₂, hb₁, hb₂]
  ring

/- The all-tail propagation and selector-collision theorems are supplied by
`BezoutPluckerJets`; this module adds the local middle-row argument and the
nonunit-coordinate example. -/

/-- Unimodularity can hold even when both coordinates are nonunits. -/
theorem two_three_isCoprime_zmod_six : IsCoprime (2 : ZMod 6) 3 := by
  exact ⟨-1, 1, by decide⟩

end ErdosProblems.Erdos1049.BezoutPluckerJets
