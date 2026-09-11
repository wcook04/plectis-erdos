import Erdos249257.HalfCarryReachability

/-!
# Localized one-hole consumer

The full low-carry window does not have to survive a feedback seam.  A unit
coefficient drop removes exactly one scalar child carry, while the compactness
endpoint needs only one admissible word at cofinally many depths.  This module
isolates the minimal remaining forward-realization interface.
-/

namespace Erdos249257.HalfCarryReachability

/-- At one depth, every scalar carry in the protected window that survives
the exact seam is realized by an admissible finite word.  Only the forward
realization direction is needed; neither full-strip equivalence nor seam
escape is assumed. -/
def ProtectedEvenSeamRealizedAt
    (N : ℕ) (δ c : ℤ) : Prop :=
  ∀ k : ℕ, 3 ≤ k → k ≤ 27 →
    EvenSeamReachable δ c k → HalfTerminalReachable N k

/-- Cofinal supply of localized, realized one-hole seams. -/
def HalfCarryCofinalProtectedEvenSeamRealization : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
    ∃ δ c : ℤ, ProtectedEvenSeamRealizedAt M δ c

/-- A one-hole seam cannot delete both protected carries `3` and `4`.
Choosing the other one yields the sole finite word required by cofinal
admissibility. -/
theorem cofinalAdmissibility_of_cofinalProtectedEvenSeamRealization
    (hsupply : HalfCarryCofinalProtectedEvenSeamRealization) :
    HalfCarryCofinalAdmissibility := by
  intro N
  obtain ⟨M, hNM, δ, c, hrealize⟩ := hsupply N
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
  have hseam : EvenSeamReachable δ c k :=
    (evenSeamReachable_iff δ c k).2 hnotHole
  obtain ⟨a, ha, _hcarry⟩ := hrealize k hk3 hk27 hseam
  exact ⟨M, hNM, a, ha⟩

/-- Localized seam realization is already a complete arithmetic producer
for an infinite Mersenne support summing to `1/2`. -/
theorem exists_infinite_support_half_of_cofinalProtectedEvenSeamRealization
    (hsupply : HalfCarryCofinalProtectedEvenSeamRealization) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 :=
  exists_infinite_support_half_of_cofinalAdmissibility
    (cofinalAdmissibility_of_cofinalProtectedEvenSeamRealization hsupply)

#print axioms cofinalAdmissibility_of_cofinalProtectedEvenSeamRealization
#print axioms exists_infinite_support_half_of_cofinalProtectedEvenSeamRealization

end Erdos249257.HalfCarryReachability
