import Mathlib

namespace Erdos249257.ExternalVerification249FullDepthRayAmplifier

open scoped BigOperators

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) -
      (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

def PeriodMultipleKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : ℕ,
    ∃ t N L : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N L

def ApFullDepthEscape : Prop :=
  ∀ d : ℕ, 0 < d → ∀ N : ℕ,
    ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)

def fullDepthKillMultipliers (d N : ℕ) : Set ℕ :=
  {t | certifiedKill (t * d) N (t * d)}

def CofinalFullDepthKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : ℕ,
    ∃ t N : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N (t * d)

theorem eventually_twoSyndetic_fullDepthKillMultipliers_of_seed
    {d N L : ℕ} (hd : 0 < d) (hseed : certifiedKill d N L) :
    ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t →
      ∃ m : ℕ, m ∈ fullDepthKillMultipliers d N ∧ t ≤ m ∧ m ≤ t + 1 := by
  sorry

theorem exists_fullDepthKill_on_ray_iff_shift_notMem_int
    {d N : ℕ} (hd : 0 < d) :
    (∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
      totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

theorem apFullDepthEscape_iff_irrational :
    ApFullDepthEscape ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

theorem cofinalFullDepthKillSupply_iff_periodMultipleKillSupply :
    CofinalFullDepthKillSupply ↔ PeriodMultipleKillSupply := by
  sorry

theorem cofinalFullDepthKillSupply_iff_irrational :
    CofinalFullDepthKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

end Erdos249257.ExternalVerification249FullDepthRayAmplifier
