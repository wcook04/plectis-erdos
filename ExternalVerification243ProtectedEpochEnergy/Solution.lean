/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.ProtectedEpochEnergy

/-!
# Source transport for protected-epoch record energy in Erdős #243

The only work is showing that the locally defined `runningMax` agrees with the
corpus `runningMax` (same primitive recursion), so the record-window and
record-step conditions transport across the two definitions.
-/

namespace Erdos249257.ExternalVerification243ProtectedEpochEnergy

def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

/-- The local `runningMax` is the corpus `runningMax`: both are the primitive
recursion `| 0 => u 0 | n+1 => max (running u n) (u (n+1))`. -/
theorem runningMax_eq (u : ℕ → ℕ) (n : ℕ) :
    runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
  induction n with
  | zero => simp [runningMax, ErdosProblems.Erdos243.runningMax]
  | succ k ih => simp [runningMax, ErdosProblems.Erdos243.runningMax, ih]

theorem protected_epoch_energy_integer
    (a u v w hc : ℕ → ℕ) (p l s τ : ℕ)
    (hp : p.Prime)
    (hpodd : Odd p)
    (hl : 1 ≤ l)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hprot : p ^ l ∣ v s)
    (hQ : 16 ≤ p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hsτ : s < τ)
    (hτ : p * p ^ l ≤ 2 * u τ) :
    ∃ J : Finset ℕ,
      (∀ n ∈ J, s ≤ n ∧ n < τ ∧ runningMax u n < u (n + 1) ∧
          u n + 3 ≤ u (n + 1) ∧ hc n = 1) ∧
      p * p ^ l ≤ (8 * p + 8) * J.card
        + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by
  have hRs' : 4 * ErdosProblems.Erdos243.runningMax u s < p * p ^ l := by
    simpa [runningMax_eq] using hRs
  obtain ⟨J, hJ, hbound⟩ :=
    ErdosProblems.Erdos243.protected_epoch_energy_integer a u v w hc p l s τ hp
      hpodd hl hred hvpos hw hwpos hnum hden hslow hprot hQ hRs' hsτ hτ
  exact ⟨J, fun n hn => by simpa [runningMax_eq] using hJ n hn, hbound⟩

end Erdos249257.ExternalVerification243ProtectedEpochEnergy
