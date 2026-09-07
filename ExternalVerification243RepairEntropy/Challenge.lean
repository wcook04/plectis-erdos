/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for repair entropy in Erdős #243

The three declarations expose the exact square-LCM recovery inequality, its
independent-family consequence, and the disappearance of every fixed-length
reset under normalized vanishing. They do not exclude recoveries whose lengths
tend to infinity, and Erdős #243 remains open.
-/

namespace Erdos249257.ExternalVerification243RepairEntropy

open scoped BigOperators

def deletionProduct (c : ℕ → ℕ) (s t : ℕ) : ℕ :=
  ∏ n ∈ Finset.Ico s t, c n

def repairedAt (c : ℕ → ℕ) (s t m : ℕ) : Prop :=
  m ∣ deletionProduct c s t

theorem repairedFamily_recovery_energy_divisionFree
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (m : ι → ℕ)
    (u h c : ℕ → ℕ) (e : ℕ → ℤ) (K r L : ℕ)
    (hK : 0 < K)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (herr : ∀ i, i < L → K * Int.natAbs (e (r + i)) < u (r + i))
    (hL : 0 < L)
    (hrecover : u r ≤ u (r + L))
    (hrepair : ∀ q ∈ R, repairedAt c r (r + L) (m q))
    (hsq : ∀ n ∈ Finset.Ico r (r + L), c n ^ 2 ∣ h n) :
    K ^ L * (R.lcm m) ^ 2 < (K + 1) ^ L := by
  sorry

theorem repaired_card_bound_of_independent
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (m : ι → ℕ)
    (u h c : ℕ → ℕ) (e : ℕ → ℤ) (K r L : ℕ)
    (hK : 0 < K)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (herr : ∀ i, i < L → K * Int.natAbs (e (r + i)) < u (r + i))
    (hL : 0 < L)
    (hrecover : u r ≤ u (r + L))
    (hrepair : ∀ q ∈ R, repairedAt c r (r + L) (m q))
    (hsq : ∀ n ∈ Finset.Ico r (r + L), c n ^ 2 ∣ h n)
    (hindep : 2 ^ R.card ≤ R.lcm m) :
    K ^ L * 4 ^ R.card < (K + 1) ^ L := by
  sorry

theorem eventually_recoveryPayment_eq_one_of_fixedLength
    (u h : ℕ → ℕ) (e : ℕ → ℤ)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (hvanish : ∀ K : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K * Int.natAbs (e n) < u n)
    (L : ℕ) (hL : 0 < L) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → u r ≤ u (r + L) →
      (∏ i ∈ Finset.range L, h (r + i)) = 1 := by
  sorry

end Erdos249257.ExternalVerification243RepairEntropy
