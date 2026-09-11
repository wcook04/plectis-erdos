import Erdos249257.HalfCarrySelectedWindow
import Erdos249257.HalfCarryProtectedSeamConsumer

/-!
# Cofinal selected-window-or-localized-seam consumer

The compactness endpoint does not require every large depth to carry a full
selected window, nor does it require a global canonical-seam equivalence. At
each requested scale it is enough to produce either:

* one selected protected window with a positive carry range; or
* one localized realized one-hole seam on the protected carries `3, ..., 27`.

Both branches contain an admissible finite word. This mixed cofinal interface
is the operational fan-in for a producer that may alternate between
rewind-singleton and rewind-seam outcomes.
-/

namespace Erdos249257.HalfCarryReachability

open Erdos249257.HalfCarrySelectedWindow

/-- Cofinal mixed producer: a full selected window or a localized realized
seam may witness each requested scale. -/
def HalfCarryCofinalSelectedWindowOrProtectedSeam : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
    ((∃ R : ℕ, 1 ≤ R ∧ Nonempty (SelectedHalfWindow M R)) ∨
      ∃ δ c : ℤ, ProtectedEvenSeamRealizedAt M δ c)

/-- Every mixed cofinal receipt contains the one admissible word required by
the landed inverse-system compactness theorem. -/
theorem cofinalAdmissibility_of_cofinalSelectedWindowOrProtectedSeam
    (hsupply : HalfCarryCofinalSelectedWindowOrProtectedSeam) :
    HalfCarryCofinalAdmissibility := by
  intro N
  obtain ⟨M, hNM, hwindow | hseam⟩ := hsupply N
  · obtain ⟨R, hR, ⟨W⟩⟩ := hwindow
    let a := W.word 1 (by omega) hR
    exact ⟨M, hNM, a, W.admissible 1 (by omega) hR⟩
  · obtain ⟨δ, c, hrealize⟩ := hseam
    let k : ℕ := if 2 * δ - c = 3 then 4 else 3
    have hk3 : 3 ≤ k := by
      simp only [k]
      split_ifs <;> omega
    have hk27 : k ≤ 27 := by
      simp only [k]
      split_ifs <;> omega
    have hnotHole : (k : ℤ) ≠ 2 * δ - c := by
      simp only [k]
      split_ifs <;> omega
    have hreachable : EvenSeamReachable δ c k :=
      (evenSeamReachable_iff δ c k).2 hnotHole
    obtain ⟨a, ha, _hcarry⟩ := hrealize k hk3 hk27 hreachable
    exact ⟨M, hNM, a, ha⟩

/-- The mixed cofinal producer is already sufficient for an infinite support
whose Mersenne achievement sum is exactly `1 / 2`. -/
theorem exists_infinite_support_half_of_cofinalSelectedWindowOrProtectedSeam
    (hsupply : HalfCarryCofinalSelectedWindowOrProtectedSeam) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 :=
  exists_infinite_support_half_of_cofinalAdmissibility
    (cofinalAdmissibility_of_cofinalSelectedWindowOrProtectedSeam hsupply)

#print axioms HalfCarryCofinalSelectedWindowOrProtectedSeam
#print axioms cofinalAdmissibility_of_cofinalSelectedWindowOrProtectedSeam
#print axioms exists_infinite_support_half_of_cofinalSelectedWindowOrProtectedSeam

end Erdos249257.HalfCarryReachability
