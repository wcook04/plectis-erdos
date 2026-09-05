import Mathlib

namespace Erdos249257.ExternalVerification243RepairEntropy

open scoped BigOperators

def deletionProduct (c : ℕ → ℕ) (s t : ℕ) : ℕ :=
  ∏ n ∈ Finset.Ico s t, c n

def repairedAt (c : ℕ → ℕ) (s t m : ℕ) : Prop :=
  m ∣ deletionProduct c s t

/- Deliberately drops the square on the repaired-family LCM. -/
theorem repairedFamily_recovery_energy_divisionFree
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (m : ι → ℕ)
    (u h c : ℕ → ℕ) (e : ℕ → ℤ) (K r L : ℕ)
    (hK : 0 < K) (hupos : ∀ n, 0 < u n) (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (herr : ∀ i, i < L → K * Int.natAbs (e (r + i)) < u (r + i))
    (hL : 0 < L) (hrecover : u r ≤ u (r + L))
    (hrepair : ∀ q ∈ R, repairedAt c r (r + L) (m q))
    (hsq : ∀ n ∈ Finset.Ico r (r + L), c n ^ 2 ∣ h n) :
    K ^ L * R.lcm m < (K + 1) ^ L := by
  sorry

end Erdos249257.ExternalVerification243RepairEntropy
